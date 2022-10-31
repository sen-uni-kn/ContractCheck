package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.HashMap;
import java.util.Map;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceDouble;

/**
 * Compute the minimal and maximal possible value for every contract variable
 * while some contract variables are already assigned
 * 
 * @author Martin Koelbl
 */
public class UmlAnalysisContractMinMax extends UmlAnalysisContractAbstract
{
	public static final String Name = "MinMax";
	ResourceDouble varValues = null;

	public UmlAnalysisContractMinMax(Job j, String name, ResourceDouble resV)
	{
		super(j, name);
		varValues = resV;
	}

	public void checkContractMinMax(UmlModel2 model)
	{
		withSoft = false;
		SmtModel smtModel = createSMTCode(model);
		if (smtModel == null)
			return;

		String code = smtModel.toText();
		if (code == null)
			return;

		// several variables can be set to a constant
		String text_var = "";
		ResourceDouble vars = varValues;
		while (vars != null)
		{
			String n = vars.getName();
			String v = vars.getData();
			if ((n == null) || (v == null))
				continue;
			text_var += "(= " + n + " " + v + ")";
			vars = vars.getNextByType();
		}
		if (!!!text_var.isEmpty())
			code += "(assert (and " + text_var + "))\n";

		ParseSmtResult resVals = runSmtAnalysis(model, code, "_Vertrag", smtModel);
		if (varValues != null)
			reportRun("Contract", "Contract satisfiable", resVals.getDiagram(), UmlResultState.GOOD);

		Map<String, Float> mapVals = new HashMap<>();
		for (String para : intList.keySet())
		{
			Float val = resVals.getValue(para);
			if (val == null)
				continue;
			mapVals.put(para, val);
		}

		// compute the min/max values for every variable in intList
		String textMinMax = "";
		for (String para : intList.keySet())
		{
			SmtDeclare decl = intList.get(para);
			if (decl == null)
				continue;
			String name = decl.getName();
			if (name == null)
				continue;

			String text = name + ",";
			text += mapVals.get(para);
			text += ",";

			ParseSmtResult res = runSmtAnalysis(model, code + "(minimize " + decl.getName() + ")", "_Vertrag",
					smtModel);
			if (res == null)
				continue;
			else
				text += res.getValue(name);
			text += ",";

			res = runSmtAnalysis(model, code + "(maximize " + decl.getName() + ")", "_Vertrag", smtModel);
			log();
			if (res == null)
				continue;
			else
				text += res.getValue(name) + ",";

			String n2 = getNameGui(model, name);
			if (n2 != null)
				text += n2;

			textMinMax += text + "\n";
		}
		// code = "(set-option :produce-unsat-cores true)\n" + code;
		// code += "(get-unsat-core)";
		reportMinMax("Contract", "Contract satisfiable", textMinMax, UmlResultState.GOOD);
	}

	private String getNameGui(UmlModel2 model, String name)
	{

		int idx = name.indexOf("_");
		if (idx >= 0)
			name = name.substring(idx + 1);

		UmlNode2 node2 = model.getNodeByName(name);
		return node2.getAttributeValue("Name");
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
	{
		this.report = report;
		checkContractMinMax(model);
	}
}
