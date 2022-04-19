package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Model;
import com.microsoft.z3.RatNum;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;

public class ParseSmtResult
{
	UmlModel2 umlModel;
	boolean sat = false;
	boolean unsat = false;
	String unsatCore = null;
	Map<String, Float> varValues = null;
	Set<Date> DateBounds = null;

	public ParseSmtResult(UmlModel2 model, Z3Call call, SmtModel smtModel)
	{
		this.umlModel = model;
		sat = call.isSat();
		unsat = !sat;
		parseModel(call.getModel());
		parseObjectives(call.getObjectives());
		Map<String, String> codeMap = null;
		if (smtModel != null)
			codeMap = smtModel.getCodeMap();
		parseUnsatCore(call.getUnsatCore(), codeMap);
		call.close();
	}

	private void parseUnsatCore(BoolExpr[] core)
	{
		if (core == null)
			return;
		unsatCore = "";
		for (BoolExpr e : core)
		{
			System.out.println("" + e);
			unsatCore += e + "\n";
		}
		// System.out.println("" + e.toString());
	}

	private void parseUnsatCore(BoolExpr[] core, Map<String, String> map)
	{
		if (map == null)
		{
			parseUnsatCore(core);
			return;
		}
		if (core == null)
			return;
		unsatCore = "";
		for (BoolExpr e : core)
		{
			String val = e.toString();
			String val2 = map.get(val);

			if ((val2 == null) || (val2.isEmpty()))
				continue;
			// System.out.println("" + val2);
			if (!!!unsatCore.isEmpty())
				unsatCore += ",";
			unsatCore += val2;
		}
		// unsatCore = "[" + unsatCore + "]";
		// System.out.println("" + e.toString());
	}

	private void parseModel(Model model)
	{
		if (model == null)
			return;
		varValues = new HashMap<>();
		// for (FuncDecl fun : model.getFuncDecls())
		// {
		// FuncInterp in = model.getFuncInterp(fun);
		// System.out.println("fun " + fun);
		// System.out.println("" + in.toString());
		// }

		// System.out.println("start");
		for (FuncDecl<?> con : model.getConstDecls())
		{
			String name = "" + con.getName();
			Expr<?> valE = model.getConstInterp(con);
			float val = 0;
			if (valE.isRatNum())
			{
				RatNum rational = (RatNum) valE;
				IntNum num = rational.getNumerator(), den = rational.getDenominator();
				val = ((float) num.getInt() / den.getInt());
			} else if (valE.isIntNum())
			{
				IntNum intV = (IntNum) valE;
				val = intV.getInt();
			} else if (valE.isBool())
			{
			} else
				System.out.println("Type of " + name + " unkown");

			varValues.put(name, val);
			// System.out.println(name + " Value = " + val);
		}
	}

	private void parseObjectives(Expr<?>[] objectives)
	{
		DateBounds = new HashSet<>();
		if (objectives == null)
			return;
		if (isUnsatisfiable())
			return;
		for (Expr<?> valE : objectives)
		{
			// System.out.print(valE.toString() + ":");
			float val = Float.NaN;
			if (valE.isRatNum())
			{
				RatNum rational = (RatNum) valE;
				IntNum num = rational.getNumerator(), den = rational.getDenominator();
				val = ((float) num.getInt() / den.getInt());
			} else if (valE.isIntNum())
			{
				IntNum intV = (IntNum) valE;
				val = intV.getInt();
			} else if (valE.isInt())
			{
				// IntExpr intE = (IntExpr) valE;
				// for (Expr e : intE.getArgs())
				// System.out.println("" + e);
			}
			System.out.println(val);
		}
	}

	protected static String[] getUnsatCore(String str)
	{
		int index = str.indexOf("model is not available");
		if (index < 0)
		{
			index = str.indexOf("unsat\n");
			if (index < 0)
				return null;
		}
		Matcher matcher = Pattern.compile("\\(([^)]+)\\)").matcher(str);
		if (!!!matcher.find(index))
			return null;
		String res = matcher.group(1);
		return res.split(" ");
	}

	protected String parseUnsatCore(String str)
	{
		String[] ress = getUnsatCore(str);
		if (ress == null)
			return null;
		String res = "";
		for (int i = 0; i < ress.length; i++)
		{
			Matcher matcher = Pattern.compile("_(.*)").matcher(ress[i]);
			if (!!!matcher.find())
				continue;
			ress[i] = matcher.group(1);
			res += ress[i] + " ";
		}
		return res;
	}

	public boolean hasUnsatCore()
	{
		return unsatCore != null;
	}

	public String getUnsatCore()
	{
		return unsatCore;
	}

	public void parseResults(String text)
	{
		if (text == null)
			return;
		if (text.contains("unsat\n"))
			unsat = true;
		if (text.contains("sat\n"))
			sat = true;
		unsatCore = parseUnsatCore(text);

		parseModel(text);
	}

	protected void parseModel(String text)
	{
		int index = text.indexOf("(model ");
		if (index == -1)
			return;

		varValues = new HashMap<>();

		// (define-fun Date_RuecktrittKaeufer_rueck () Int 28)

		Matcher matcher = Pattern.compile("\\(define-fun (.*) \\(\\) Int (.*)\\)").matcher(text);
		if (!!!matcher.find())
			return;
		int val = matcher.groupCount();
		for (int i = 1; i <= val; i++)
		{
			String val2 = matcher.group(i);
			System.out.println(val2);
		}
	}

	public String getDiagram()
	{
		if (varValues == null)
			return null;

		return createDiagram(null);
		// return "Anna->Max: Does something\\nNote over of B: Bob thinks";
	}

	public String getDiagram(Date dateExtra)
	{
		return createDiagram(dateExtra);
	}
	
	public String getMinMax()
	{
		String minMax = "";

		List<Date> list = getDateFromModel();
		for (Date d : list)
		{
			// UmlNode node = getUmlNode(d.Name);
			minMax += "" + d.Name + ",Min=" + d.getValueMin() + ",Max=" + d.getValue() + "</br>";
		}
		return minMax;
	}

	private String getName(String name)
	{
		int index = name.indexOf("_");
		if (index >= 0)
			return name.substring(index + 1);
		return name;
	}

	private UmlNode2 getUmlNode(String name)
	{
		String n = getName(name);

		UmlNode2 v = umlModel.getNodeByName(n);
		return v;
	}

	private List<Date> getDateFromModel()
	{
		List<Date> list = new ArrayList<>();
		if (varValues != null)
			for (String k : varValues.keySet())
			{
				if (!!!k.startsWith("Date"))
					continue;
				Date d = new Date();
				d.Name = k;
				d.Value = varValues.get(k);
				list.add(d);
			}
		return list;
	}

	private String createDiagram(Date dateExtra)
	{
		List<Date> list = getDateFromModel();
		if (dateExtra != null && list != null)
			list.add(dateExtra);
		Collections.sort(list);
		StringBuilder build = new StringBuilder();
		for (Date d : list)
		{
			if (build.length() > 0)
				build.append("\\n");

			String v = createUmlArrow(d);
			if (v == null)
				continue;
			build.append(v);
		}
		return build.toString();
	}

	private boolean isPflichtErfuellt(UmlNode2 node, float val)
	{
		if (node == null)
			return false;
		if (isWarranty(node))
		{
			if (val >= 0)
				return false;
		} else if (val < 0)
			return false;
		return true;
	}

	private String getArrowText(UmlNode2 node, float val)
	{
		if (node == null)
			return null;
		String text = "";

		String n = node.getAttributeValue(LegalUml.Name);
		if (n != null)
			text += n;

		if (!!!isPflichtErfuellt(node, val))
		{
			if (isWarranty(node))
				text += " asserted(" + val + ")";
			else
				text += " unperformed";
		} else
		{
			if (isWarranty(node))
				text += " performed";
			else if (node.inheritatesFrom(LegalUml.Withdrawal))
				text += " (" + val + ")";
			else
				text += " performed(" + val + ")";
		}
		return text;
	}

	private String createUmlArrow(Date d)
	{
		String from = "P1";
		String to = "P2";
		UmlNode2 node = getUmlNode(d.Name);

		if (node == null)
			return null;

		UmlNode2 claim = node;
		boolean bClaim = false;
		if (node.inheritatesFrom(LegalUml.SecondaryClaim))
		{
			bClaim = true;
			if (!!!isWarranty(node) && !!!isPflichtErfuellt(node, d.Value))
				return null;
			UmlNode2 node2 = getPflicht(node);
			if (node2 != null)
				node = node2;
		}
		boolean bGaran = node.inheritatesFrom(LegalUml.Warranty);

		List<UmlNode2> sL = node.getAssoziationsByName(LegalUml.Debtor);
		List<UmlNode2> gL = node.getAssoziationsByName(LegalUml.Creditor);

		for (UmlNode2 n : sL)
		{
			from = n.getAttributeValue(LegalUml.Name);
			break;
		}

		for (UmlNode2 n : gL)
		{
			to = n.getAttributeValue(LegalUml.Name);
			break;
		}

		String text = getArrowText(claim, d.Value);
		if (text == null)
			text = getName(getName(d.Name)) + "(" + d.getValue() + ")";
		if (d.Value == -1)
		{
			// if (node.inheritatesFrom(LegalUml.Garantie))
			// return "Note over " + to + ":" + text;
			// else
			return "Note over " + from + ":" + text;
		}

		if (bClaim ^ bGaran)
		{
			String f = from;
			from = to;
			to = f;
		}
		return "" + from + "->" + to + ":" + text;
	}

	private boolean isWarranty(UmlNode2 claim)
	{
		return claim.isOfClass(LegalUml.Warranty);
	}

	private UmlNode2 getPflicht(UmlNode2 node)
	{
		List<UmlNode2> list = node.getAssoziationsByName(LegalUml.Trigger);
		if (!!!list.isEmpty())
		{
			for (UmlNode2 n : list)
				return n;
		}
		return null;
	}

	public boolean isUnsatisfiable()
	{
		return unsat;
	}

	public boolean isSatisfiable()
	{
		return sat;
	}

	public Float getValue(String name)
	{
		if (name == null)
			return null;
		if (varValues == null)
			return null;
		return varValues.get(name);
	}
}
