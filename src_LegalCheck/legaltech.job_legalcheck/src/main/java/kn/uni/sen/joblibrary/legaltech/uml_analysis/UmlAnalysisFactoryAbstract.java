package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitorAbstract;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * 
 * @author Martin Koelbl (C) 2023
 */
public abstract class UmlAnalysisFactoryAbstract extends LegalVisitorAbstract implements UmlAnalysisFactory
{
	String name;
	
	public UmlAnalysisFactoryAbstract(Job j, String name)
	{
		super(j);
		this.name = name;
	}

	@Override
	public String getName()
	{
		return name;
	}
}
