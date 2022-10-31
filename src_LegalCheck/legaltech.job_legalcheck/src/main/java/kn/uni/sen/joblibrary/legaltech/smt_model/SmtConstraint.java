package kn.uni.sen.joblibrary.legaltech.smt_model;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * defines an SMT contraint
 * 
 * @author Martin Koelbl
 */
public class SmtConstraint implements SmtElement
{
	List<SmtElement> children = new ArrayList<>();
	String operator;
	String name;
	public static int Count = 0;
	// todo: ugly hack that have to be solved when it work out
	SmtModel model = null;

	public SmtConstraint(String op)
	{
		operator = op;
	}

	public SmtConstraint(String op, String name, SmtModel model)
	{
		operator = op;
		this.name = name;
		this.model = model;
	}

	public SmtConstraint addConstraint(SmtConstraint bedFunc)
	{
		if (bedFunc == null)
			return this;
		children.add(bedFunc);
		return this;
	}

	public SmtConstraint addConstraint(SmtElement bedFunc)
	{
		if (bedFunc == null)
		{
			System.out.println("Warning: Constraint==null");
			return this;
		}
		children.add(bedFunc);
		return this;
	}

	private String xorToText()
	{

		String text = "";
		String or = "";
		int count = 0;
		for (SmtElement c : children)
		{
			String t1 = c.toText();
			if (!!!text.isEmpty())
			{
				text += " ";
				or += " ";
			}
			or += t1;

			for (int i = 0; i < count; i++)
			{
				SmtElement c2 = children.get(i);
				text += "(not (and " + t1 + " " + c2.toText() + "))";
			}
			count++;
		}
		return "(and " + text + " (or " + or + "))";
	}

	@Override
	public String toText()
	{
		if (operator == null)
		{
			System.out.println("SMT Operator is missing.");
			return "";
		}
		if (children.size() == 0)
			return operator;

		String op = operator;
		String text = "";
		if (operator.equals("xor") && (children.size() > 2))
		{
			op = "and";
			text = xorToText();
		} else
		{
			for (SmtElement c : children)
			{
				if (!!!text.isEmpty())
					text += " ";
				text += c.toText();
			}
		}

		if ((name != null) && !!!name.isEmpty() && (model != null))
		{
			Map<String, String> codeMap = model.getCodeMap();
			if (codeMap != null)
				codeMap.put(text, name);
			return "(" + op + " (! " + text + " :named a" + (++Count) + "_" + name + ") )";
		}

		return "(" + op + " " + text + ")";
	}
}
