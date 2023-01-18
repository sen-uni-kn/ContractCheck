package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.jobscheduler.common.model.Job;

// traverses the UML node and calls legal visitors
public abstract class LegalVisitorAbstract extends UmlVisitorAbstract
{
	UmlModel2 model = null;

	public LegalVisitorAbstract(Job job)
	{
		super(job);
	}

	// todo: make functions abstract
	protected void visitContract(Element ele)
	{
	}

	protected void visitClaim(Element ele)
	{
	}

	protected void visitObject(Element ele)
	{
	}

	protected void visitPerson(Element ele)
	{
	}

	private void visitProperty(Element ele)
	{
	}

	private void visitRegistration(Element ele)
	{
	}

	private void visitPrice(Element ele)
	{
	}

	protected void leaveContract(Element ele)
	{
	}

	protected void leaveClaim(Element ele)
	{
	}

	protected void leaveObject(Element ele)
	{
	}

	protected void leavePerson(Element ele)
	{
	}

	private void leaveProperty(Element ele)
	{
	}

	private void leaveRegistration(Element ele)
	{
	}

	private void leavePrice(Element ele)
	{
	}

	@Override
	public void visit(UmlModel2 model)
	{
		this.model = model;
	}

	@Override
	public void visitAttribute(Element ele, String name, String val)
	{
	}

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

		// String type = ele.getNodeName();
		// System.out.println(type);
		if (model.inheritatesFrom(ele, LegalUml.SPA))
		{
			visitContract(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.PrimaryClaim))
		{
			visitClaim(ele);
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
		}
	}

	public void leaveElement(Element ele)
	{
		if (model.inheritatesFrom(ele, LegalUml.SPA))
		{
			leaveContract(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Claim))
		{
			leaveClaim(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Person))
		{
			leavePerson(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Object))
		{
			leaveObject(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.PropertyRight))
		{
			leaveProperty(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Registration))
		{
			leaveRegistration(ele);
		} else if (model.inheritatesFrom(ele, LegalUml.Price))
		{
			leavePrice(ele);
		}
	}
}
