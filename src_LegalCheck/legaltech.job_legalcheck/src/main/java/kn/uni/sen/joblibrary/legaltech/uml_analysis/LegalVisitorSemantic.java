package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitorAbstract;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

// traverses the UML node and adds legal semantic
public class LegalVisitorSemantic extends LegalVisitorAbstract
{
	UmlModel2 model = null;

	public LegalVisitorSemantic(Job job)
	{
		super(job);
	}

	protected void visitClaim(Element ele)
	{
	}
}
