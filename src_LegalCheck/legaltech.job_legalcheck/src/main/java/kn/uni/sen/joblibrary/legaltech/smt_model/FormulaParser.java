package kn.uni.sen.joblibrary.legaltech.smt_model;

public class FormulaParser
{
	private int findNextSign(String math, char[] pat, int start)
	{
		for (int j = start; j < math.length(); j++)
		{
			for (int i = 0; i < pat.length; i++)
				if (math.charAt(j) == pat[i])
					return j;
		}
		return -1;
	}

	int getCloseBraket(String math, int start)
	{
		int counter = 1;
		char[] pat = { '(', ')' };
		int idx = 1;
		int idx2 = findNextSign(math, pat, idx);
		while (idx2 > 0)
		{
			char val = math.charAt(idx2);
			if (val == ')')
				counter--;
			else if (val == '(')
				counter++;
			if (counter == 0)
				return idx2;
			idx = idx2 + 1;
			idx2 = findNextSign(math, pat, idx);
		}
		return -1;
	}

	SmtConstraint convertEle(SmtElement c)
	{
		if (c instanceof SmtConstraint)
			return (SmtConstraint) c;
		return null;
	}

	SmtElement addCurElement(SmtElement cur, SmtElement n)
	{
		if (cur == null)
			return n;
		if (cur instanceof SmtConstraint)
		{
			SmtConstraint c = (SmtConstraint) cur;

			if (n instanceof SmtConstraint)
				c.addConstraint((SmtConstraint) n);
			else if (n instanceof SmtDeclare)
				c.addConstraint((SmtDeclare) n);
		}
		return cur;
	}

	public SmtConstraint parseFormula(String math, SmtModel smtModel)
	{
		math.replace(" ", "");

		SmtElement cur = null;

		// todo: parse >=, <=
		char[] pat = { '+', '-', '/', '*', '=', '(', ')', '<', '>' };
		int idx = 0;
		int idx2 = findNextSign(math, pat, idx);
		while (idx >= 0)
		{
			String text = null;
			if (idx == idx2)
			{
				// parse special sign
				char val = math.charAt(idx2);
				if (val == '(')
				{
					int idxClose = getCloseBraket(math, idx);
					if (idxClose <= 0)
					{
						System.out.println("Error: formula misses braket");
						return null;
					}

					String math2 = math.substring(idx + 1, idxClose);
					idx2 = idxClose;
					SmtConstraint n = parseFormula(math2, smtModel);
					cur = addCurElement(cur, n);
				} else
				{
					SmtConstraint n = new SmtConstraint("" + val);
					cur = addCurElement(n, cur);
				}
				idx = idx2 + 1;
			} else
			{
				if (idx2 == -1)
					// end of string
					text = math.substring(idx);
				else
					// between text
					text = math.substring(idx, idx2);
				text = text.replace(" ", "");

				// parse text
				SmtElement ele = null;
				if (isNumber(text))
				{
					ele = new SmtConstraint(text);
				} else
					ele = getVariable(text, smtModel);

				cur = addCurElement(cur, ele);
				idx = idx2;
			}
			if (idx == -1)
				break;
			idx2 = findNextSign(math, pat, idx);
		}
		return convertEle(cur);
	}

	private SmtDeclare getVariable(String text, SmtModel smtModel)
	{
		SmtDeclare v = smtModel.getVariable(text);
		if (v == null)
			v = smtModel.addDeclaration(new SmtDeclare("const", text, "Real"));
		return v;
	}

	private boolean isNumber(String text)
	{
		try
		{
			Double.parseDouble(text);
		} catch (Exception ex)
		{
			return false;
		}
		return true;
	}

}
