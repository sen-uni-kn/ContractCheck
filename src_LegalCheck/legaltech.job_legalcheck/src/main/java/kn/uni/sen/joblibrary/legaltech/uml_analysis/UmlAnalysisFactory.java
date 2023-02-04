package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;

/**
 * General interface for a contract analysis.
 *  
 * @author Martin Koelbl (C) 2023
 */
public interface UmlAnalysisFactory
{
	String getName();

	List<Element> searchAnalyzeElements(UmlModel2 model2);	

	UmlAnalysis generateAnalysis(UmlModel2 model, Element ele);
}
