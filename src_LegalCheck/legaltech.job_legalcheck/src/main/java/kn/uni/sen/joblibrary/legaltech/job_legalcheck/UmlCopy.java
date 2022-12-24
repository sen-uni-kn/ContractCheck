package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.HashMap;
import java.util.Map;

import org.w3c.dom.Element;
import org.w3c.dom.Node;

import kn.uni.sen.jobscheduler.common.model.Job;

// Deep-copy of UML structure
public class UmlCopy extends UmlVisitorAbstract
{
	public UmlCopy(Job job)
	{
		super(job);
	}

	Map<Node, Element> nodeMap = new HashMap<>();

	UmlModel2 model = null;

	public UmlModel2 copyModel(UmlModel2 model)
	{
		traverse(model);
		return model;
	}

	UmlModel2 getModel()
	{
		return model;
	}

	@Override
	public void visit(UmlModel2 model)
	{
		if (model == null)
			return;
		if (this.model != null)
		{
			error("Copy failure since model already exists");
			return;
		}
		this.model = new UmlModel2(model);
		nodeMap.put(model.root, this.model.root);
	}

	@Override
	public void visitElement(Element ele)
	{
		if (nodeMap.containsKey(ele))
			// element is already created
			return;

		// copy element
		Element par = (Element) ele.getParentNode();
		String type = ele.getNodeName();
		Element ele2 = model.doc.createElement(type);
		nodeMap.put(ele, ele2);
		Element par2 = nodeMap.get(par);
		if (par2 != null)
			par2.appendChild(ele2);
	}

	@Override
	public void leaveElement(Element ele)
	{
	}

	@Override
	public void visitAttribute(Element ele, String name, String val)
	{
		Element ele2 = nodeMap.get(ele);
		ele2.setAttribute(name, val);
	}
}
