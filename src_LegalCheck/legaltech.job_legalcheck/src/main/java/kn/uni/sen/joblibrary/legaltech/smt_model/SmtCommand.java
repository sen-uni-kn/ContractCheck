package kn.uni.sen.joblibrary.legaltech.smt_model;

/**
 * smt command that is executed in an SMT solver
 * 
 * @author Martin Koelbl
 */
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
