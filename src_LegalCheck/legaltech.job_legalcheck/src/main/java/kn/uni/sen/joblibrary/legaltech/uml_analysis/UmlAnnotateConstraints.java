package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.HashMap;
import java.util.Map;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitor;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

public class UmlAnnotateConstraints extends LegalVisitor
{
	Map<Element, UmlAnnotation> map = new HashMap<>();

	public UmlAnnotateConstraints(Job job)
	{
		super(job);
	}
	
	protected void visitPrimaryClaim(Element ele)
	{
		super.visitPrimaryClaim(ele);
	}

	@Override
	protected void visitClaim(Element ele)
	{
		super.visitClaim(ele);
	}

	@Override
	protected void visitObject(Element ele)
	{
		super.visitObject(ele);
	}

	@Override
	protected void visitPerson(Element ele)
	{
		super.visitPerson(ele);
	}

	public Map<Element, UmlAnnotation> generate(UmlModel2 model)
	{
		return map;
	}
}
