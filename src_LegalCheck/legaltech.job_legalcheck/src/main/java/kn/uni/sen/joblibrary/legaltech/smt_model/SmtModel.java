package kn.uni.sen.joblibrary.legaltech.smt_model;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import kn.uni.sen.joblibrary.legaltech.parser.model.Pair;

public class SmtModel implements SmtElement
{
	List<SmtDeclare> declList = new ArrayList<>();
	// Integer is used to sort output of constraints in z3 file
	List<Pair<Integer, SmtConstraint>> conList = new ArrayList<>();
	List<SmtCommand> cmdList = new ArrayList<>();
	Map<String, String> codeMap = null;

	public SmtModel()
	{
		codeMap = new HashMap<>();
	}

	public SmtDeclare addDeclaration(SmtDeclare dec)
	{
		if (dec == null)
			return null;
		if (declList.contains(dec))
			return dec;
		declList.add(dec);
		return dec;
	}

	public SmtConstraint addConstraint(SmtConstraint con, int i)
	{
		if (con == null)
			return null;
		Pair<Integer, SmtConstraint> pair = new Pair<>(i, con);
		conList.add(pair);
		return con;
	}

	public SmtCommand addCommand(SmtCommand cmd)
	{
		if (cmd == null)
			return null;
		cmdList.add(cmd);
		return cmd;
	}

	public SmtConstraint createAssert(String name, int i)
	{
		SmtConstraint as = new SmtConstraint("assert", name, this);
		return addConstraint(as, i);
	}
	
	public SmtConstraint createAssertSoft(String name, int i)
	{
		SmtConstraint as = new SmtConstraint("assert-soft", name, this);
		return addConstraint(as, i);
	}

	private void sortConstraints()
	{
		Collections.sort(conList, new Comparator<Pair<Integer, SmtConstraint>>()
		{
			@Override
			public int compare(Pair<Integer, SmtConstraint> lhs, Pair<Integer, SmtConstraint> rhs)
			{
				// -1 - less than, 1 - greater than, 0 - equal, all inversed for
				// descending
				return lhs.getKey() - rhs.getKey();
			}
		});
	}

	@Override
	public String toText()
	{
		return toText("");
	}

	public String toText(String extraCode)
	{
		StringBuilder text = new StringBuilder();
		for (SmtDeclare dec : declList)
			text.append(dec.declareText() + "\n");
		text.append("\n");

		sortConstraints();
		int last = 1;
		for (Pair<Integer, SmtConstraint> con : conList)
		{
			if (last != con.getKey())
			{
				last = con.getKey();
				text.append("\n");
			}
			text.append(con.getValue().toText() + "\n");
		}
		text.append("\n");
		text.append(extraCode);
		for (SmtCommand cmd : cmdList)
			text.append(cmd.toText() + "\n");
		return text.toString();
	}

	public SmtDeclare getVariable(String text)
	{
		for (SmtDeclare var : declList)
		{
			if (var.getName().compareTo(text) == 0)
				return var;
		}
		return null;
	}

	public Map<String, String> getCodeMap()
	{
		return codeMap;
	}
}
