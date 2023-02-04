package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Generate analyses and execute them.
 * 
 * @author Martin Koelbl (C) 2023
 */
public class UmlAnalysisExecutor
{
	UmlAnalysisFactory ana;
	String statisticsFile = null;
	Job job;

	public UmlAnalysisExecutor(Job j)
	{
		job = j;
	}

	public String getStatisticFile()
	{
		return statisticsFile;
	}

	public void setStatisticFile(String file)
	{
		statisticsFile = file;
	}

	public void runAnalysis(UmlAnalysis ana, ReportResult report)
	{
		ana.runAnalysis(report);
	}
}
