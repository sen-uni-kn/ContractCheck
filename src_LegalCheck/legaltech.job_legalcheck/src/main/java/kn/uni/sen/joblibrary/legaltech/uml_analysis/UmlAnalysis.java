package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;

public interface UmlAnalysis
{
	void runAnalysis(UmlModel2 model, ReportResult report);
	
	public String getStatisticFile();

	public void setStatisticFile(String file);
	
	String getName();
}
