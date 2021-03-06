package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

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

public class Contract2Uml2
{
	Job job;
	Map<String, Element> nodeMap = new HashMap<>();
	Stack<Element> clauseStack = null;
	List<Helper.Pair<String, ContractCard>> assList = null;
	UmlModel2 model = null;
	ResourceFile xsdFile = null;

	public Contract2Uml2(Job j, ResourceFile xsd)
	{
		job = j;
	}

	Element createNode(UmlModel2 model, Element parent, String type, String id)
	{
		// get node class
		Element cn = model.getClassElement(type);
		if (cn == null)
		{
			job.logEventStatus(JobEvent.WARNING, "Unkown Type " + type);
		}

		Element ele;
		ele = model.createElement(parent, type, id);
		nodeMap.put(id, ele);
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
			model.addAssociation2Node(par, LegalUml.Legal, node);
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

	public void setAssingmentValue(String id, String val, ContractCard c)
	{
		String idCard = c.getID();
		// if (id.equals("rueckK.Schuldner"))
		// System.out.println("");

		// if ("Ruecktritt2_pflicht".startsWith(idCard + "_" + id))
		// System.out.println("id");

		String nodeID = c.getNodeFirstID(id);
		Element node = getNodeByID(model, nodeID);
		if (node == null)
			node = getNodeByID(model, idCard + "_" + nodeID);

		String idAttr = getIDAttr(id);
		idAttr = parseLanguage(idAttr);
		if (val.startsWith("$"))
		{
			String name2 = val.substring(1);
			Element n = getNodeByID(model, name2);
			String ids = idCard + "_" + name2;
			if (n == null)
				n = getNodeByID(model, ids);
			if (n == null)
			{
				System.out.println("" + val.substring(1) + " not found!");
				return;
			}

			if ((node != null))
			{
				if (idAttr == null)
					return;
				model.addAssociation2Node(node, idAttr, n);
			} else
			{
				if (idAttr == null)
					nodeMap.put(idCard + "_" + id, n);
				else
				{
					System.out.println("" + id + " not found!");
					return;
				}
			}
		} else if (node != null)
		{
			String v = getIDValue(val);
			if (idAttr != null)
				model.addAttribute(node, idAttr, v);
			else
				model.setNodeAttribute(node, v);
		}
	}

	public void convertAssignmentCard(UmlModel2 model, ContractCard c)
	{
		for (String assign : c.getAssignmentList())
		{
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
			setAssingmentValue(id, val, c);
		}
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

		List<UmlNode2> list = model.findNodesByExpression(expr);
		for (UmlNode2 n : list)
		{
			String name = n.getName();
			if (name.isEmpty())
				continue;
			String id = name + idRest;
			setAssingmentValue(id, val, card);
		}

	}

	public UmlModel2 convert(Contract contract)
	{
		if (contract == null)
			return null;
		clauseStack = new Stack<>();
		assList = new ArrayList<>();

		model = new UmlModel2(job, xsdFile);

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

		String filePath = ResourceFolder.appendFolder(job.getFolderText(), "test.xml");
		model.writeFile(filePath);
		model.validateFile(filePath, null);

		return model;
	}
}
