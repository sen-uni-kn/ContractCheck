package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze the contract is satisfiable for at least one contract execution.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class UmlAnalysisSPA extends UmlAnalysisSmtAbstract
{
	public static final String Name = "SPA";
	Element contract = null;

	public UmlAnalysisSPA(Job j, String anaName)
	{
		super(j, null, anaName, null);
	}

	public UmlAnalysisSPA(Job j, String name, String anaName, UmlModel2 model, Element ele)
	{
		super(j, name, anaName, model);
		contract = ele;
	}

	@Override
	public List<UmlAnalysis> createAnalyses(UmlModel2 model2)
	{
		List<UmlAnalysis> list = new ArrayList<>();
		List<Element> contracts = (new UmlSearchContracts(job)).searchContracts(model2);
		for (Element conEle : contracts)
		{
			String conName = (new UmlNode2(model2, conEle)).getName();
			list.add(new UmlAnalysisSPA(job, conName, anaName, model2, conEle));
		}
		return list;
	}

	@Override
	SmtModel createSMTCode(UmlModel2 model)
	{
		SmtModel smt = (new Legal2Constraints(this, job)).generate(model);
		return smt;
	}

	@Override
	public void runAnalysis(ReportResult report, String statisticsFile)
	{
		this.report = report;

		SmtModel smtModel = createSMTCode(model);
		if (smtModel == null)
			return;

		String code = smtModel.toText();
		if (code == null)
			return;
		// code = "(set-option :produce-unsat-cores true)\n" + code;
		// code += "(get-unsat-core)";

		ParseSmtResult res = runSmtAnalysis(model, code, null, smtModel);
		if (res != null)
		{
			if (res.isUnsatisfiable())
			{
				result = 0;
				reportUnsat(name, "Contract not satisfiable", res.getUnsatCore(), UmlResultState.ERROR);
			} else
			{
				result = 1;
				reportRun(name, "Contract satisfiable", res.getDiagram(), UmlResultState.GOOD);
			}
		}
		log(statisticsFile);
	}
}
