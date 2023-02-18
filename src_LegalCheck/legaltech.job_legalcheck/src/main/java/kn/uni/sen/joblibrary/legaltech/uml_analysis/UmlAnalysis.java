package kn.uni.sen.joblibrary.legaltech.uml_analysis;

/**
 * General interface for a contract analysis.
 * 
 * @author Martin Koelbl (C) 2023
 */
public interface UmlAnalysis
{
	String getName();

	void runAnalysis(ReportResult report, String statisticsFile);
}
