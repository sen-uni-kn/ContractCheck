package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlElement;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze the contract is satisfiable for at least one contract execution.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class UmlAnalysisFactorySyntax extends UmlAnalysisFactoryAbstract
{
	public static final String Name = "Syntax";

	public UmlAnalysisFactorySyntax(Job j, String name)
	{
		super(j, name);
	}

	@Override
	public UmlAnalysis generateAnalysis(UmlModel2 model, UmlElement ele)
	{
		return null;
	}

}
