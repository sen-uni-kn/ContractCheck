package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;

/**
 * 
 * @author Martin Koelbl (C) 2023
 */
public interface UmlAnalysisFactory
{
	String getName();

	List<UmlAnalysis> createAnalyses(UmlModel2 model2);
}
