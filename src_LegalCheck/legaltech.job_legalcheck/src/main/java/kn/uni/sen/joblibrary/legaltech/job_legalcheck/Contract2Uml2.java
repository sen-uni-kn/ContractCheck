package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractCard;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUmlGerman;
import kn.uni.sen.jobscheduler.common.helper.Helper;
import kn.uni.sen.jobscheduler.common.helper.Helper.Pair;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

/**
 * Converts a @see Contract in a UML class diagram
 * 
 * @author Martin Koelbl
 */
public class Contract2Uml2
{
	Job job;
	Map<String, Element> nodeMap = new HashMap<>();
	Stack<Element> clauseStack = null;
	List<Helper.Pair<String, ContractCard>> assList = null;
	UmlModel2 model = null;
	ResourceFile xmlFile;
	ResourceFile xsdFile;

	public Contract2Uml2(Job j, ResourceFile xmlFile, ResourceFile xsd)
	{
		job = j;
		this.xmlFile = xmlFile;
		xsdFile = new ResourceFile();
		String val = Helper.loadFilePath("legal.xsd");
		xsdFile.setData(val);
	}

	Element createNode(UmlModel2 model, Element parent, String type, String id)
	{
		// get node class
		Element cn = model.getClassElement(type);
		if (cn == null)
		{
			job.logEventStatus(JobEvent.WARNING, "Unkown Type " + type);
		}

		// reuse old id when attribute already existed
		Element ele = model.createElement(parent, type, id);
		nodeMap.put(id, ele);
		if (model.inheritatesFrom(type, LegalUml.Claim))
		{
			// every claims needs a date by default
			model.addAttribute(ele, LegalUml.EventDate, null);
		}
		return ele;
	}

	public void convertVariableCard(UmlModel2 model, ContractCard c)
	{
		String idCard = c.getID();
		for (String v : c.getVariableList())
		{
			// get essential data about the node
			String name = c.getVariableName(v);
			String id = idCard + "_" + name;
			String type = c.getVariableType(v);
			type = parseLanguage(type);
			if ((id == null) || (type == null))
			{
				job.logEventStatus(JobEvent.WARNING, "" + v + " could not be parsed!");
				continue;
			}

			// is node a reference?
			if (type.startsWith("$"))
			{
				nodeMap.put(id, null);
				continue;
			}

			// create node
			if (model.inheritatesFrom(type, LegalUml.Clause))
			{
				add2ClauseStack(model, type, id);
			} else
			{
				Element n = createNode(model, null, type, id);
				addNode2Stack(model, n);
			}
		}
	}

	private String parseLanguage(String type)
	{
		return LegalUmlGerman.convertEnglish(type);
	}

	int getClauseLevel(String type)
	{
		// String type = item.getNodeName();
		if (LegalUml.Clause1.equals(type))
			return 1;
		if (LegalUml.Clause2.equals(type))
			return 2;
		if (LegalUml.Clause3.equals(type))
			return 3;
		return -1;
	}

	private void removeLevels(int level)
	{
		while (!!!clauseStack.empty())
		{
			Element parent = clauseStack.peek();
			int cur = getClauseLevel(parent.getNodeName());
			if (cur < level)
				return;
			clauseStack.pop();
		}
	}

	private void add2ClauseStack(UmlModel2 model, String type, String id)
	{
		int level = getClauseLevel(type);
		if (level < 0)
			return;
		removeLevels(level);

		Element node = null;
		if (!!!clauseStack.empty())
		{
			Element par = clauseStack.peek();
			node = createNode(model, par, type, id);
			// model.addAssociation2Node(par, LegalUml.Clause, node);
		} else
			node = createNode(model, null, type, id);
		clauseStack.push(node);
	}

	private void addNode2Stack(UmlModel2 model, Element node)
	{
		if (!!!clauseStack.empty())
		{
			Element par = clauseStack.peek();
			model.addAssociation2Node(par, LegalUml.Reference, node);
		}
	}

	Element getNodeByID(UmlModel2 model, String url)
	{
		if (url == null)
			return null;
		// String last = url;
		String rest = url;
		Element node = null;
		while (!!!rest.isEmpty())
		{
			int idx = rest.indexOf(".");
			String id = rest;
			if (idx >= 0)
			{
				id = rest.substring(0, idx);
				rest = rest.substring(idx + 1);
			} else
				rest = "";
			if (node == null)
			{
				node = nodeMap.get(id);
			} else
			{
				UmlNode2 n = model.getAssoziationByName(node, id);
				if (n != null)
					node = n.getElement();
			}
			if (node == null)
				// an id of the url was not found
				return null;
		}
		return node;
		// if (node != null)
		// return nodeMap.get(last);
	}

	String getIDAttr(String url)
	{
		int index = url.lastIndexOf(".");
		if (index == -1)
			return null;
		return url.substring(index + 1);
	}

	String getIDValue(String val)
	{
		if (val.startsWith("'"))
		{
			val = val.substring(1);
			if (val.endsWith("'"))
				val = val.substring(0, val.length() - 1);
		}
		return val;
	}

	// returns a variable referenced by a name
	Element getReference(UmlModel2 model, String name, String idCard)
	{
		Element n = getNodeByID(model, name);
		String ids = idCard + "_" + name;
		if (n == null)
			n = getNodeByID(model, ids);
		return n;
	}

	public void setAssignmentValue(String id, String val, ContractCard c)
	{
		String idCard = c.getID();
		String nodeID = c.getNodeFirstID(id);
		Element node = getReference(model, nodeID, idCard);

		String idAttr = getIDAttr(id);
		idAttr = parseLanguage(idAttr);
		if (val.startsWith("$"))
		{ // is reference to another variable
			String name2 = val.substring(1);
			Element n = getReference(model, name2, idCard);
			if (n == null)
			{
				System.out.println("Card: " + idCard + " " + name2 + " not found!");
				return;
			}
			if ((node != null))
			{
				if (idAttr == null)
					return;
				model.addAssociation2Node(node, idAttr, n);
			} else
			{
				// create reference entry
				if (idAttr == null)
					nodeMap.put(idCard + "_" + id, n);
				else
				{
					System.out.println("" + id + " not found!");
				}
			}
			return;
		}

		if (node == null)
		{
			System.out.println("Warning " + val + " ignored in Card " + c.getID());
			return;
		}

		if (isFormula(val) && (idAttr != null))
		{
			// parse formula and assign to attribute
			Element ele = createFormula(model, null, c, val, false);
			model.addAssociation2Node(node, idAttr, ele);
			return;
		} else
		{
			String v = getIDValue(val);
			if (idAttr != null)
				model.addAttribute(node, idAttr, v);
			else
				model.setNodeAttribute(node, v);
		}
	}

	// searches for an operator in assign
	// find == true -> ignores "="
	int findOperator(String formula, boolean find)
	{
		// sequence of operators defines binding
		Map<String, Integer> map = new HashMap<>();
		String[] ops = { "<", ">", "=", "+", "-", "*", "/" };
		for (String op : ops)
			map.put(op, -1);
		int brackets = 0;
		// last sign cannot be an operator
		for (int i = 0; i < formula.length() - 1; i++)
		{
			char c = formula.charAt(i);
			if (c == '(')
				brackets++;
			if (c == ')')
				brackets--;

			// only if no bracket is open
			if (brackets == 0)
			{
				// search for the first occurrence of every sign
				Integer val = map.get("" + c);
				if ((val != null) && (val == -1))
				{
					if (find && (c == '=') && (formula.charAt(i + 1) != '='))
						// single equivalence could be an assignment
						continue;
					// remove "=" operator
					map.put("" + c, i);
				}
			}
		}
		// return the most binding operator
		for (String op : ops)
		{
			int idx = map.get(op);
			if (idx != -1)
				return idx;
		}
		return -1;
	}

	// remove brackets when
	String checkBrackets(String form)
	{
		if (form.isEmpty() || form.charAt(0) != '(' || form.charAt(form.length() - 1) != ')')
			return form;
		int brackets = 1;
		for (int i = 1; i < form.length() - 1; i++)
		{
			if (form.charAt(i) == '(')
				brackets++;
			else if (form.charAt(i) == ')')
				brackets--;
			if (brackets == 0)
				// braket is closed in formula
				return form;
		}
		// first character opens and last character closes same bracket pair
		return form.substring(1, form.length() - 1);
	}

	public static boolean isValue(String val)
	{
		String rex = "^([+-]?\\d*\\.?\\d*)$";
		Pattern pattern = Pattern.compile(rex);
		Matcher matcher = pattern.matcher(val);
		return matcher.matches();
	}

	int formulaCounter = 1;
	int variableCounter = 1;

	// (a + (b * 4)) < 4
	private Element createFormula(UmlModel2 model, Element func, ContractCard c, String assign, boolean isCon)
	{
		assign = checkBrackets(assign);
		assign = assign.replace(" ", "");
		int idx = findOperator(assign, false);
		if (idx < 0)
		{
			Element var = getReference(model, assign, c.getID());
			if (var != null)
			{ // is reference to another variable
				if (isCon && func != null)
				{
					// is constraint, thus, add to variable
					model.addAssociation2Node(var, LegalUml.Constraint, func);
				}
				return var;
			} else if (isValue(assign))
			{ // is value
				String name = "" + c.getID() + "_" + (variableCounter++);
				Element n = createNode(model, null, LegalUml.IntegerS, name);
				n.setTextContent(assign);
				return n;
			} else
				System.out.println("Card: " + c.getID() + " " + assign + " not found!");
		}
		String id = c.getID() + "_formula" + (formulaCounter++);
		Element n = createNode(model, null, "Formula", id);
		if (func == null)
			func = n;
		String left = assign.substring(0, idx);
		String op = "" + assign.charAt(idx);
		if (assign.charAt(idx + 1) == '=')
		{
			op += "=";
			idx += 1;
		}
		String right = assign.substring(idx + 1);
		Element op1 = createFormula(model, func, c, left, isCon);
		Element op2 = createFormula(model, func, c, right, isCon);
		if ((op1 == null) || (op2 == null))
			// an operand is missing
			return null;
		model.addAssociation2Node(n, "Op1", op1);
		model.addAttribute(n, "Operator", op);
		model.addAssociation2Node(n, "Op2", op2);
		return n;
	}

	public void convertAssignmentCard(UmlModel2 model, ContractCard c)
	{
		for (String assign : c.getAssignmentList())
		{
			if (assign.startsWith("%"))
				continue;

			if (isFormula(assign) && !isAssignment(assign))
			{ // assignment is an additional constraint for a variable
				assign = assign.replace("'", "");
				createFormula(model, null, c, assign, true);
				continue;
			}

			// System.out.println(v);
			String id = c.getAssignmentName(assign);
			String val = c.getAssignmentValue(assign);
			if ((id == null) || (val == null))
			{
				System.out.println("" + assign + " could not be parsed!");
				job.logEventStatus(JobEvent.ERROR, "" + assign + " could not be parsed!");
				continue;
			}

			if (id.startsWith("$"))
			{
				Helper.Pair<String, ContractCard> pair = new Helper.Pair<String, ContractCard>(assign, c);
				assList.add(pair);
			}
			setAssignmentValue(id, val, c);
		}
	}

	private boolean isAssignment(String assign)
	{
		// search for "=" and not "=="
		// would be nicer with a regex
		assign = assign.replace("<=", "").replace(">=", "").replace("==", "");
		if (assign.contains("="))
			return true;
		return false;
	}

	private boolean isFormula(String assign)
	{
		if (assign.startsWith("${"))
			// '${' is start for search query
			return false;
		if (assign.contains("=+"))
			// special assignment, no formula
			return false;

		int idx = findOperator(assign, true);
		if (idx < 0)
			// no operator found -> no formula
			return false;
		return true;
	}

	private void convertAssignmentCard2(UmlModel2 model, String assign, ContractCard card)
	{
		// XMI 2.1 for UML 2.0
		// todo: execute xPath parser
		if ((assign == null) || !!!assign.startsWith("$"))
			return;
		assign = assign.substring(1);

		int idx1 = assign.lastIndexOf("{");
		int idx2 = assign.lastIndexOf("}");
		int idx3 = assign.lastIndexOf("=");
		if ((idx1 < 0) || (idx2 < idx1) || (idx3 < idx2))
			return;

		String expr = assign.substring(idx1 + 1, idx2);
		String idRest = assign.substring(idx2 + 1, idx3);
		String val = assign.substring(idx3 + 1);

		if ((expr != null) && (expr.contains("$")))
			System.out.println("Implement search query with variables");

		List<UmlNode2> list = model.findNodesByExpression(expr);
		for (UmlNode2 n : list)
		{
			String name = n.getName();
			if (name.isEmpty())
				continue;
			String id = name + idRest;
			setAssignmentValue(id, val, card);
		}
	}

	public UmlModel2 convert(Contract contract)
	{
		if (contract == null)
			return null;
		clauseStack = new Stack<>();
		assList = new ArrayList<>();

		model = new UmlModel2(job, xsdFile.getData());

		for (ContractCard c : contract.getCardList())
		{
			if (c.isHidden())
				continue;
			convertVariableCard(model, c);
		}
		for (ContractCard c : contract.getCardList())
		{
			if (c.isHidden())
				continue;
			convertAssignmentCard(model, c);
		}
		for (Pair<String, ContractCard> p : assList)
			convertAssignmentCard2(model, p.name, p.value);

		String xml = null;
		if (xmlFile != null)
		{
			xml = xmlFile.getData();
		}
		if ((xml != null) && !!!xml.isBlank())
		{
			model.writeFile(xml);
			model.validateFile(xml, null);
		}

		// String filePath2 = ResourceFolder.appendFolder(job.getFolderText(),
		// "test2.xml");
		// UmlCopy cop = new UmlCopy(job);
		// UmlModel2 model2 = cop.copyModel(model);
		// model2.writeFile(filePath2);
		return model;
	}
}
