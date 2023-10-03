package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

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
		if (statisticsFile == null)
		{
			// file not open create
			statisticsFile = ResourceFolder.appendFolder(job.getFolderText(), "statistics.txt");
			ResourceFile.removeFile(statisticsFile);
			String head = "name & analysis & good & time & mem & constraints & variables\\\\\n";
			ResourceFile.appendText2File(statisticsFile, head);
		}

		ana.runAnalysis(report, statisticsFile);
	}
}
