package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Deep copy of legal object diagram.
 * 
 * @author Martin Koelbl (C) 2023
 */
public abstract class LegalMapper extends UmlTraverseMapper
{
	public LegalMapper(Job job)
	{
		super(job);
	}

	protected void visitContract(Element ele)
	{
		visitElement(ele);
	}

	protected void visitPrimaryClaim(Element ele)
	{
		visitClaim(ele);
	}

	protected void visitClaim(Element ele)
	{
		visitElement(ele);
	}

	protected void visitObject(Element ele)
	{
		visitElement(ele);
	}

	protected void visitPerson(Element ele)
	{
		visitElement(ele);
	}

	private void visitProperty(Element ele)
	{
		visitElement(ele);
	}

	private void visitRegistration(Element ele)
	{
		visitElement(ele);
	}

	private void visitPrice(Element ele)
	{
		visitElement(ele);
	}

	@Override
	public void visitElement(Element ele)
	{
		String ref = ele.getAttribute("ref");
		if ((ref == null) || !!!ref.isBlank())
			// references are not individual elements
			return;

		if (model == null)
		{
			error("Legal visitor misses model!");
			return;
		}

		if (model.inheritatesFrom(ele, LegalUml.SPA))
		{
			visitContract(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.PrimaryClaim))
		{
			visitPrimaryClaim(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Claim))
		{
			visitClaim(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Person))
		{
			visitPerson(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Object))
		{
			visitObject(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.PropertyRight))
		{
			visitProperty(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Registration))
		{
			visitRegistration(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Price))
		{
			visitPrice(ele);
		} else
			super.visitElement(ele);
	}
}
