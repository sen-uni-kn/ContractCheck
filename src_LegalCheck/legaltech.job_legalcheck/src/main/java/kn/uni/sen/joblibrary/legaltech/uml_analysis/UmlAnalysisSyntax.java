package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze the contract is satisfiable for at least one contract execution.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class UmlAnalysisSyntax implements UmlAnalysis, UmlAnalysisFactory
{
	public static final String Name = "Syntax";
	Job job;
	String name;
	UmlModel2 model;

	public UmlAnalysisSyntax(Job job, String name)
	{
		// factory
		this.job = job;
		this.name = name;
	}

	public UmlAnalysisSyntax(Job job, String name, UmlModel2 model)
	{
		// analysis
		this.job = job;
		this.name = name;
		this.model = model;
	}

	@Override
	public String getName()
	{
		return name;
	}

	@Override
	public List<UmlAnalysis> createAnalyses(UmlModel2 model2)
	{
		List<UmlAnalysis> list = new ArrayList<>();
		list.add(new UmlAnalysisSyntax(job, name, model2));
		return list;
	}

	@Override
	public void runAnalysis(ReportResult report)
	{
		// todo: run
	}
}
