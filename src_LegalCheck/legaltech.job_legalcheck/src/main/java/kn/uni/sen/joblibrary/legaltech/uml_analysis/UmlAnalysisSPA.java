package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
			list.add(new UmlAnalysisSPA(job, name, model2, ele));
		}
		return list;
	}

	@Override
	public void runAnalysis(ReportResult report)
	{
		Map<Element, UmlAnnotation> map = (new UmlAnnotateConstraints(job)).generate(model);
		SmtModel smt = (new UmlCombineConstraints(job)).combine(model, map);
		// todo: run smt analysis
	}
}
