package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

public class UmlAnalysisSmt implements UmlAnalysis
{
	Job job;
	String name;
	SmtModel smt;

	public UmlAnalysisSmt(Job job, String name, SmtModel smt)
	{
		this.job = job;
		this.name = name;
		this.smt = smt;
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
