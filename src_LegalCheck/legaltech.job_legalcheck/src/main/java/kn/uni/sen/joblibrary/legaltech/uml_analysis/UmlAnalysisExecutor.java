package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
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

	public void runAnalysis(UmlAnalysisFactory fac, UmlModel2 model2, ReportResult rep)
	{
		if (fac == null)
		{
			// todo: write warning that factory is null
			return;
		}

		// search analysis elements
		List<Element> list = fac.searchAnalyzeElements(model2);
		for (Element ele : list)
		{
			// generate analysis
			UmlAnalysis ana = fac.generateAnalysis(model2, ele);
			
			if(ana==null)
			{
				// todo: write warning that no analysis was generated
				continue;				
			}

			// execute analysis
			ana.runAnalysis(rep);
		}
	}
}
