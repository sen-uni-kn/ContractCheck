package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlElement;

/**
 * General interface for a contract analysis.
 *  
 * @author Martin Koelbl (C) 2023
 */
public interface UmlAnalysisFactory
{
	String getName();

	UmlAnalysis generateAnalysis(UmlModel2 model, UmlElement ele);	
}
