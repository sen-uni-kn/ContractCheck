package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.Map;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * 
 * @author Martin Koelbl (C) 2023
 */
public abstract class UmlAnalysisFactoryAbstract implements UmlAnalysisFactory
{
	String name;
	Job job;

	public UmlAnalysisFactoryAbstract(Job j, String name)
	{
		this.name = name;
		job = j;
	}

	@Override
	public String getName()
	{
		return name;
	}

	@Override
	public UmlAnalysis generateAnalysis(UmlModel2 model, Element ele)
	{
		// annotate contract and apply analysis
		Map<Element, UmlAnnotation> map = (new UmlAnnotateConstraints(job)).generate(model);
		// generate constraint system
		SmtModel smt = (new UmlCombineConstraints(job)).combine(model, map);
		return new UmlAnalysisSmt(job, name, smt);
	}
}
