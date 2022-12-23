package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import org.w3c.dom.Element;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;

public abstract class UmlVisitorAbstract implements UmlVisitor
{
	Job job;

	public UmlVisitorAbstract(Job job)
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

	void traverse(UmlModel2 model)
	{
		this.visit(model);
		Element ele = model.doc.getDocumentElement();
		traverseNode(ele);
	}

	private void traverseNode(Element ele)
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
			Node e = children.item(i);
			if (e.getNodeType() == Node.ELEMENT_NODE)
			{
				this.visitElement((Element) e);
			}
		}
	}
}
