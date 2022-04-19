package kn.uni.sen.joblibrary.legaltech.smt_model;

public class SmtCommand implements SmtElement
{
	String cmd;

	public SmtCommand(String cmd)
	{
		this.cmd = cmd;
	}

	@Override
	public String toText()
	{
		if (cmd == null)
			return "";
		return "(" + cmd + ")";
	}
}
