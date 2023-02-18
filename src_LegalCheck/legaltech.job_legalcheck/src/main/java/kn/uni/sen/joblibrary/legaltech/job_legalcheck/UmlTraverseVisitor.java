package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.RunContext;

/**
 * Traverses every element and attribute of an UML model.
 * 
 * @author Martin Koelbl (C) 2023
 */
public class UmlTraverseVisitor
{
	protected RunContext job;
	protected UmlModel2 model;

	public UmlTraverseVisitor(RunContext job)
	{
		this.job = job;
	}

	void warning(String val)
	{
		output(JobEvent.WARNING, val);
	}

	void error(String val)
	{
		output(JobEvent.ERROR, val);
	}

	protected void output(String type, String val)
	{
		if (job != null)
		{
			job.logEventStatus(type, val);
		} else
		{
			System.out.println(type + ":" + val);
		}
	}

	public void visitModel(UmlModel2 model)
	{
		Element ele = model.doc.getDocumentElement();
		this.model = model;
		visitElement(ele);
	}

	public void visitAttribute(Element ele, String name, String val)
	{

	}

	public void visitElement(Element ele)
	{
		// visit every attribute
		NamedNodeMap atts = ele.getAttributes();
		for (int i = 0; i < atts.getLength(); i++)
		{
			Node s = atts.item(i);
			String name = s.getNodeName();
			String val = s.getNodeValue();
			this.visitAttribute(ele, name, val);
		}
		// visit every child element
		NodeList children = ele.getChildNodes();
		for (int i = 0; i < children.getLength(); i++)
		{
			Node n = children.item(i);
			if (n.getNodeType() == Node.ELEMENT_NODE)
			{
				Element e = (Element) n;
				visitElement(e);
			}
		}
	}
}
