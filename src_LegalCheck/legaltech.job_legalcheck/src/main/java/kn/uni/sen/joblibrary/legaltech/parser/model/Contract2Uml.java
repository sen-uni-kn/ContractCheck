package kn.uni.sen.joblibrary.legaltech.parser.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractCard;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.ComputeClause;
import kn.uni.sen.jobscheduler.common.helper.Helper;
import kn.uni.sen.jobscheduler.common.helper.Helper.Pair;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

/** First implementation of an conversion from contract cards to UML
 * 
 * @author Martin Koelbl
 */
@Deprecated
public class Contract2Uml
{
	Job job;
	Map<String, UmlNode> nodeMap = new HashMap<>();
	Stack<UmlNode> clauseStack = null;
	List<Helper.Pair<String, ContractCard>> assList = null;
	
	public Contract2Uml(Job j, ResourceFile xsd)
	{
		job = j;
	}

	UmlNode createNode(UmlModel model, String type, String id)
	{
		// get node class
		UmlNode cn = model.getClass(type);
		if (cn == null)
		{
			job.logEventStatus("Warning", "Unkown Type " + type);
			cn = new UmlNode(type, type);
			// System.out.println(t);
			model.addNode(cn);
		}

		UmlNode n = new UmlNode(id, id);
		nodeMap.put(id, n);
		n.setInstanceOf(cn);
		model.addNode(n);
		return n;
	}

	public void convertVariableCard(UmlModel model, ContractCard c)
	{
		String idCard = c.getID();
		for (String v : c.getVariableList())
		{
			// get essential data about the node
			String name = c.getVariableName(v);
			String id = idCard + "_" + name;
			String type = c.getVariableType(v);
			if ((id == null) || (type == null))
			{
				job.logEventStatus("Warning", "" + v + " could not be parsed!");
				continue;
			}

			// is node a reference?
			if (type.startsWith("$"))
			{
				nodeMap.put(id, null);
				continue;
			}

			// create node
			UmlNode n = createNode(model, type, id);
			addNode2Stack(n);
		}
	}

	private void removeLevels(int level)
	{
		while (!!!clauseStack.empty())
		{
			UmlNode parent = clauseStack.peek();
			int cur = ComputeClause.getClauseLevel(parent);
			if (cur < level)
				return;
			clauseStack.pop();
		}
	}

	private void add2ClauseStack(UmlNode node)
	{
		int level = ComputeClause.getClauseLevel(node);
		if (level < 0)
			return;
		removeLevels(level);

		if (!!!clauseStack.empty())
		{
			UmlNode par = clauseStack.peek();
			par.addAss(LegalUml.Clause, node);
		}
		clauseStack.push(node);
	}

	private void addNode2Stack(UmlNode node)
	{
		if (node.inheritatesFrom(LegalUml.Clause))
		{
			add2ClauseStack(node);
			return;
		}

		if (!!!clauseStack.empty())
		{
			UmlNode par = clauseStack.peek();
			par.addAss(LegalUml.Legal, node);
		}
	}

	UmlNode getNodeByID(UmlModel model, String url)
	{
		String last = url;
		String rest = url;
		int index = url.indexOf(".");
		UmlNode node = null;
		while (index != -1)
		{
			last = rest.substring(0, index);
			if (node == null)
			{
				node = nodeMap.get(last);
			} else
			{
				List<UmlNode> list = node.getAssociatedNodeByKey(last);
				if (!!!list.isEmpty())
					node = list.get(0);
			}
			rest = rest.substring(index + 1);
			index = rest.indexOf(".");
		}
		;
		if (node != null)
			return node;
		return nodeMap.get(last);
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

	public void convertAssignmentCard(UmlModel model, ContractCard c)
	{
		String idCard = c.getID();
		for (String assign : c.getAssignmentList())
		{
			// System.out.println(v);
			String id = c.getAssignmentName(assign);
			String val = c.getAssignmentValue(assign);
			if ((id == null) || (val == null))
			{
				System.out.println("" + assign + " could not be parsed!");
				job.logEventStatus("Error", "" + assign + " could not be parsed!");
				continue;
			}

			if (id.startsWith("$"))
			{
				Pair<String, ContractCard> pair = new Pair<>(assign, c);
				assList.add(pair);
			}

			// if (id.equals("ersatz.Preis"))
			// System.out.println("");

			// if ("Ruecktritt2_pflicht".startsWith(idCard + "_" + id))
			// System.out.println("id");

			String nodeID = c.getNodeFirstID(id);
			UmlNode node = getNodeByID(model, nodeID);
			if (node == null)
				node = getNodeByID(model, idCard + "_" + nodeID);

			String idAttr = getIDAttr(id);
			if (val.startsWith("$"))
			{
				String name2 = val.substring(1);
				UmlNode n = getNodeByID(model, name2);
				if (n == null)
					n = getNodeByID(model, idCard + "_" + name2);
				if (n == null)
				{
					System.out.println("" + val.substring(1) + " not found!");
					continue;
				}

				if ((node != null))
				{
					if (idAttr == null)
						continue;
					node.addAss(idAttr, n);
				} else
				{
					if (idAttr == null)
						nodeMap.put(idCard + "_" + id, n);
					else
					{
						System.out.println("" + id + " not found!");
						continue;
					}
				}
			} else if (node != null)
			{
				String v = getIDValue(val);
				node.addAtt(idAttr, v);
			}
		}
	}

	private void parseAssignments(UmlModel model, String name, ContractCard card)
	{
		// todo: execute xPath parser
	}

	public UmlModel convert(Contract contract)
	{
		if (contract == null)
			return null;
		clauseStack = new Stack<>();
		assList = new ArrayList<>();

		UmlModel model = new UmlModel();
		LegalUml.addClasses(model);

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
			parseAssignments(model, p.name, p.value);

		return model;
	}
}
