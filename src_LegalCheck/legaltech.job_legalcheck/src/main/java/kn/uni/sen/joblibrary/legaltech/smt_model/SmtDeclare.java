package kn.uni.sen.joblibrary.legaltech.smt_model;

public class SmtDeclare implements SmtElement
{
	String name;
	String type;
	String body;

	public SmtDeclare(String type, String n, String body)
	{
		this.type = type;
		name = n;
		this.body = body;
	}

	public String declareText()
	{
		return "(declare-" + type + " " + name + " " + body + ")";
	}

	@Override
	public String toText()
	{
		return name;
	}

	public String getName()
	{
		return name;
	}
}
