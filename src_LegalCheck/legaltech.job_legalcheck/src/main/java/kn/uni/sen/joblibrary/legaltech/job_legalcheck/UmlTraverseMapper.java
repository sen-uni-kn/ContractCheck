package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.HashMap;
import java.util.Map;

import org.w3c.dom.Element;
import org.w3c.dom.Node;

import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Deep-copy of UML structure.
 * 
 * @author Martin Koelbl (C) 2023
 */
public class UmlTraverseMapper extends UmlTraverseVisitor
{
	public UmlTraverseMapper(Job job)
	{
		super(job);
		clearModel();
	}

	Map<Node, Element> nodeMap;
	UmlModel2 model2;

	public UmlModel2 copyModel(UmlModel2 model)
	{
		visitModel(model);
		return this.model2;
	}

	UmlModel2 getModel()
	{
		return model2;
	}

	private void clearModel()
	{
		this.model2 = null;
		nodeMap = new HashMap<>();
	}

	@Override
	public void visitModel(UmlModel2 model)
	{
		clearModel();
		if (model == null)
			return;
		if (this.model2 != null)
		{
			error("Copy failure since model already exists");
			return;
		}
		this.model2 = new UmlModel2(model);
		nodeMap.put(model.root, this.model2.root);
	}

	protected Element copyElement(Element ele)
	{
		Element ele2 = nodeMap.get(ele);
		if (nodeMap.containsKey(ele))
			// element is already created
			return ele2;

		// copy element
		Element par = (Element) ele.getParentNode();
		String type = ele.getNodeName();
		ele2 = model2.doc.createElement(type);
		nodeMap.put(ele, ele2);
		Element par2 = nodeMap.get(par);
		if (par2 != null)
			par2.appendChild(ele2);
		return ele2;
	}

	@Override
	public void visitElement(Element ele)
	{
		copyElement(ele);
		super.visitElement(ele);
	}

	@Override
	public void visitAttribute(Element ele, String name, String val)
	{
		Element ele2 = nodeMap.get(ele);
		ele2.setAttribute(name, val);
	}
}
