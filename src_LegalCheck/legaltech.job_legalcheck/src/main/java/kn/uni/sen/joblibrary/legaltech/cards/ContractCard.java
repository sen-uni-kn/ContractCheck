package kn.uni.sen.joblibrary.legaltech.cards;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlAssociation;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlAttribute;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlNode;

/**
 * Contract card formalizes some part of a contract text by variables and their
 * assignment
 * 
 * @author Martin Koelbl
 */
public class ContractCard
{
	Contract contract = null;
	String id;
	String index;
	String text;
	String multi;
	List<String> variableList = new ArrayList<>();
	List<String> assignmentList = new ArrayList<>();
	// List<String> constraintList = new ArrayList<>();
	Map<String, String> resultMap = new HashMap<>();

	public static final String HideT = "Hide";

	public ContractCard()
	{
	}

	public ContractCard(ContractCard card)
	{
		this.contract = card.getContract();
		this.id = card.getID();
		this.text = card.getPlainText();
		this.multi = card.getMultiplicity();
		for (String var : card.getVariableList())
			variableList.add(var);
		for (String var : card.getAssignmentList())
			assignmentList.add(var);
		// for (String var : card.getConstraintList())
		// constraintList.add(var);
	}

	public void setID(String id)
	{
		this.id = id;
	}

	public String getID()
	{
		return id;
	}

	public void setPlainText(String text)
	{
		this.text = text;
	}

	public String getPlainText()
	{
		return text;
	}

	public void setPlainAssignment(String text)
	{
		if (text == null)
			return;
		assignmentList.add(text);
	}

	public String getPlainAssignment()
	{
		return createArray(assignmentList);
	}

	/*
	 * public void setPlainConstraint(String text) { if (text == null) return;
	 * constraintList.add(text); }
	 * 
	 * public String getPlainConstraint() { return createArray(constraintList);
	 * }
	 */

	public void setPlainVariable(String text)
	{
		if (text == null)
			return;
		variableList.add(text);
	}

	public String getPlainVariable()
	{
		return createArray(variableList);
	}

	String createArray(List<String> list)
	{
		String text = "";
		for (String s : list)
		{
			if (!!!text.isEmpty())
				text += ",";
			text += "\"" + s + "\"";
		}
		return "[" + text + "]";
	}

	public String getCardText()
	{
		String text = getPlainText();
		Pattern pattern = Pattern.compile("\\$([^\\s]+)");
		Matcher matcher = pattern.matcher(text);
		StringBuilder sb = new StringBuilder();
		while (matcher.find())
		{
			String pat = text.substring(matcher.start() + 1, matcher.end());
			String rep = getNodeValueNice(pat);
			if (rep == null)
				rep = getNodeValue(pat);
			if (rep == null)
				continue;
			if (rep.contains("$"))
			{
				System.out.println("Warning: Replace elements recursively " + rep);
				rep = rep.replace("$", "");
				// continue;
			}
			matcher.appendReplacement(sb, rep);
		}
		matcher.appendTail(sb);
		String val = sb.toString();
		return val;
	}

	// String val = c.getNodeValue(HtmlCreator_ContractInput.HideT);
	public void setHide(boolean b)
	{
		String v = getVariableDeclare(HideT);
		if (b)
		{
			if (v == null)
				setPlainVariable(HideT + ":" + LegalUml.BooleanS);
			setVariableAssignment(HideT, "true");
		} else
		{
			removeVariableDeclare(HideT + ":" + LegalUml.BooleanS);
			removeVariableAssignment(HideT);
		}
	}

	public boolean isHidden()
	{
		String val = getNodeValue(HideT);
		if ((val != null) && val.equals("true"))
			return true;
		return false;
	}

	public List<String> getVariableList()
	{
		return variableList;
	}

	public List<String> getAssignmentList()
	{
		return assignmentList;
	}

	private String getVariableAssignment(String name)
	{
		if (name == null)
			return null;
		for (String ass : assignmentList)
		{
			String n = getAssignmentName(ass);
			if (name.equals(n))
				return ass;
		}
		return null;
	}

	/*
	 * public List<String> getConstraintList() { return constraintList; }
	 */

	public String getVariableName(String v)
	{
		int index = v.lastIndexOf(":");
		if (index != -1)
			return v.substring(0, index);
		return null;
	}

	public String getVariableType(String v)
	{
		if (v == null)
			return null;
		int index = v.lastIndexOf(":");
		if (index != -1)
			return v.substring(index + 1);
		return null;
	}

	public String getAssignmentName(String v)
	{
		int index = v.indexOf("=");
		if (index != -1)
			return v.substring(0, index);
		return null;
	}

	public String getAssignmentValue(String v)
	{
		if (v == null)
			return null;
		int index = v.indexOf("=");
		if (index != -1)
			return v.substring(index + 1);
		return null;
	}

	public void setMultiplicity(String string)
	{
		multi = string;
	}

	public String getMultiplicity()
	{
		return multi;
	}

	public void setContract(Contract contract)
	{
		this.contract = contract;
	}

	public String getVariableDeclare(String name)
	{
		if (name == null)
			return null;
		for (String var : variableList)
		{
			String n = getVariableName(var);
			if (name.equals(n))
				return var;
		}
		return null;
	}

	public boolean removeVariableDeclare(String name)
	{
		if (name == null)
			return false;
		for (String var : variableList)
		{
			String n = getVariableName(var);
			if (name.equals(n))
			{
				variableList.remove(n);
				return true;
			}
		}
		return false;
	}

	public String getNodeType(String name)
	{
		int index = name.indexOf(".");
		String text = name;
		String rest = null;
		if (index != -1)
		{
			text = name.substring(0, index);
			rest = name.substring(index + 1);
		}

		String val = getVariableDeclare(text);
		String type = getVariableType(val);
		if ((type != null) && type.startsWith("$"))
			type = type.substring(1);

		if (rest == null)
			return type;
		// reference to attribute or association
		UmlNode node = LegalUml.getNodeByName(type);
		if (node == null)
			return null;
		UmlNode node2 = null;
		List<UmlAttribute> attrs = node.getAttributesByName(rest);
		for (UmlAttribute attr : attrs)
			node2 = attr.getClassType();
		if (node2 == null)
		{
			List<UmlAssociation> ass = node.getAssoziationsByName(rest);
			for (UmlAssociation as : ass)
				node2 = as.hasEndNodeKey(rest);
		}
		if (node2 == null)
			return null;
		return node2.getName();
	}

	public String getNodeFirstID(String name)
	{
		int index = name.indexOf(".");
		if (index == -1)
			return name;
		return name.substring(0, index);
	}

	public String getNodeValue(String name)
	{
		// String dec = getVariableDeclare(text);
		// String type = getVariableType(dec);
		String ass = getVariableAssignment(name);
		String val = getAssignmentValue(ass);
		if (val != null)
		{
			if (val.startsWith("$"))
				return val.substring(1);
			return val;
		}
		return "";
	}

	public String getNodeValueNice(String name)
	{
		String ass = getVariableAssignment(name);
		String val = getAssignmentValue(ass);
		if (val != null)
		{
			if (val.startsWith("$"))
			{
				String varName = val.substring(1) + ".Name";
				String val2 = null;
				if (contract != null)
					val2 = contract.getNodeValueNice(varName);
				if (val2 != null)
					val = val2;
			}
			return val;
		}
		return null;
	}

	public void getInstancesByClass(List<String> list, String cl)
	{
		UmlNode cln = LegalUml.getNodeByName(cl);
		for (String var : variableList)
		{
			String t = getVariableType(var);
			if (cl.equals(t))
			{
				String name = getVariableName(var);
				list.add(id + "_" + name);
				continue;
			}
			if (cln == null)
				continue;
			UmlNode n = LegalUml.getNodeByName(t);
			if ((n != null) && n.inheritatesFrom(cln))
			{
				String name = getVariableName(var);
				list.add(id + "_" + name);
			}
		}
	}

	public Contract getContract()
	{
		return contract;
	}

	public void setVariableAssignment(String name, String value)
	{
		if (name == null)
			return;
		String as = getVariableAssignment(name);
		if (as != null)
			assignmentList.remove(as);
		as = name + "=" + value;
		assignmentList.add(as);
	}

	public void removeVariableAssignment(String name)
	{
		if (name == null)
			return;
		String as = getVariableAssignment(name);
		if (as != null)
			assignmentList.remove(as);
	}

	public void setIndex(String idx)
	{
		index = idx;
	}

	public String getIndex()
	{
		return index;
	}

	public int getIndexValue()
	{
		if (index == null)
			return Integer.MAX_VALUE;
		return Integer.parseInt(index);
	}

	public void addResult(String eO, String tO)
	{
		resultMap.put(eO, tO);
	}

	public Map<String, String> getResultMap()
	{
		return resultMap;
	}
}
