package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
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

	public UmlAnalysisSPA(Job j, String name)
	{
		super(j, name, null);
	}

	public UmlAnalysisSPA(Job j, String name, UmlModel2 model, Element ele)
	{
		super(j, name, model);
		contract = ele;
	}

	@Override
	public List<UmlAnalysis> createAnalyses(UmlModel2 model2)
	{
		List<UmlAnalysis> list = new ArrayList<>();
		List<Element> contracts = (new UmlAnalysisSearchContracts(job)).searchContracts(model2);
		for (Element ele : contracts)
		{
			list.add(new UmlAnalysisSPA(job, anaName, model2, ele));
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

		ParseSmtResult res = runSmtAnalysis(model, code, "_SPA", smtModel);
		if (res != null)
		{
			if (res.isUnsatisfiable())
			{
				reportUnsat("Contract", "Contract not satisfiable", res.getUnsatCore(), UmlResultState.ERROR);
			} else
				reportRun("Contract", "Contract satisfiable", res.getDiagram(), UmlResultState.GOOD);
		}
		log(statisticsFile);
	}
}
