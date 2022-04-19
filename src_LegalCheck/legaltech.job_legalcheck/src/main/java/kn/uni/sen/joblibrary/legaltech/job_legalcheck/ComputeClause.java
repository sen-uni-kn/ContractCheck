package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.Stack;

import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlAssociation;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlAttribute;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlModel;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlNode;

public class ComputeClause
{
	class ClauseData
	{
		ClauseData(String t, UmlNode n)
		{
			text = t;
			node = n;
		}

		String text;
		UmlNode node;
	}

	Stack<ClauseData> clauseStack = new Stack<>();

	public static int getClauseLevel(String type)
	{
		if (LegalUml.Clause1.equals(type))
			return 1;
		if (LegalUml.Clause2.equals(type))
			return 2;
		if (LegalUml.Clause3.equals(type))
			return 3;
		return -1;
	}

	public static int getClauseLevel(UmlNode node)
	{
		// check whether node is class
		String type = node.getName();
		int level = getClauseLevel(type);
		if (level >= 0)
			return level;
		// get class type of current node
		UmlNode cl = node.getClass2();
		if (cl == null)
			return -1;
		type = cl.getName();
		return getClauseLevel(type);
	}

	public int getTextLevel(String text)
	{
		if (text == null)
			return 0;

		int counter = 1;
		int idx = text.indexOf(".");
		while (idx >= 0)
		{
			counter++;
			idx = text.indexOf(".", idx + 1);
		}
		return counter;
	}

	private String incLevelValue(String last, int level)
	{
		if ((last == null) && (level == 1))
			return "1";
		if (getTextLevel(last) < level)
		{
			String t = last;
			if (t == null)
				t = "1";
			while (getTextLevel(t) < level)
			{
				t += ".1";
			}
			return t;
		}
		if (last == null)
			return "1";

		int idx = last.lastIndexOf(".");
		String val = last;
		String rest = "";
		if (idx > 0)
		{
			val = last.substring(idx + 1);
			rest = last.substring(0, idx);
		}
		try
		{
			int val2 = Integer.parseInt(val);
			if (rest.isBlank())
				return "" + (val2 + 1);
			return rest += "." + (val2 + 1);
		} catch (Exception ex)
		{
			System.out.println("Warning: Error with computing clause numbers.");
		}
		return "";
	}

	public String getClause(String type, UmlNode node)
	{
		int level = getClauseLevel(type);
		;
		// remove elements with higher level
		ClauseData curData = null;
		if (!!!clauseStack.empty())
			curData = clauseStack.peek();
		while ((curData != null) && getTextLevel(curData.text) > level)
		{
			clauseStack.pop();
			if (clauseStack.empty())
			{
				curData = null;
				break;
			}
			curData = clauseStack.peek();
		}

		// compute new level
		String last = null;
		if (curData != null)
		{
			last = curData.text;
			if (curData.node != null)
			{
				// add child to parent
				UmlAssociation as = new UmlAssociation(LegalUml.Clause);
				as.addAssNode(LegalUml.Clause, node);
				curData.node.addAssoziation(as);
			}
		}

		// get next item entry
		String newText = incLevelValue(last, level);
		ClauseData clause = new ClauseData(newText, node);
		clauseStack.push(clause);
		return newText;
	}

	public void setClause(UmlModel model, String type, UmlNode node)
	{
		String valClause = getClause(type, node);
		if (node != null)
		{
			UmlNode cs = model.getClass(LegalUml.StringS);
			UmlAttribute att = new UmlAttribute(LegalUml.Item, LegalUml.Item, cs);
			att.setValue(valClause);
			node.addAttribute(att);
		}
	}

	public UmlNode getCurrentNode()
	{
		if (!!!clauseStack.isEmpty())
			return null;
		ClauseData data = clauseStack.peek();
		return data.node;
	}
}
