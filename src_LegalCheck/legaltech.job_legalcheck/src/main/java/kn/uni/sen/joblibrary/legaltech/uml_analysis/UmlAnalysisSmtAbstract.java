package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

public abstract class UmlAnalysisSmtAbstract implements UmlAnalysis, UmlAnalysisFactory
{
	Job job;
	String name;
	UmlModel2 model;

	public UmlAnalysisSmtAbstract(Job job, String name, UmlModel2 model)
	{
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
	public void runAnalysis(ReportResult report)
	{
		// todo: run smt analysis
	}
}
