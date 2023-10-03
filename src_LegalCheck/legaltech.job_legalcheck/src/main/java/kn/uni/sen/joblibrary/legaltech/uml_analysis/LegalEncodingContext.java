package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.RunContext;

/**
 * Context of a legal encoding.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class LegalEncodingContext implements UmlAnalysisListener
{
	RunContext context;
	UmlAnalysisListener analysis;

	public LegalEncodingContext(UmlAnalysisListener ana, Job job)
	{
		context = job;
		analysis = ana;
	}

	public void reportError(String text)
	{
		analysis.reportError(text);
	}

	public void reportWarning(String text)
	{
		analysis.reportWarning(text);
	}

	public void reportGood(String text)
	{
		analysis.reportGood(text);
	}
}
