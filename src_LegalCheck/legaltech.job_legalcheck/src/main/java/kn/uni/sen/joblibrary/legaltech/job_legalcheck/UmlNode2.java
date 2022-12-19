package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;

/**
 * stores a UML class node
 * 
 * @author Martin Koelbl
 */
public class UmlNode2
{
	Element ele = null;
	UmlModel2 model;

	public UmlNode2(UmlModel2 model, Element ele)
	{
		this.model = model;
		this.ele = ele;
	}

	public Element getElement()
	{
		return ele;
	}

	public UmlModel2 getModel()
	{
		return model;
	}

	public boolean isOfClass(String type)
	{
		return model.isOfClass(ele, type);
	}

	public boolean inheritatesFrom(String type)
	{
		return model.inheritatesFrom(ele, type);
	}

	public String getAttributeValue(String name)
	{
		return model.getAttributeValue(ele, name);
	}

	public String getContent()
	{
		return ele.getTextContent();
	}

	public UmlNode2 getAssoziationByName(String name)
	{
		return model.getAssoziationByName(ele, name);
	}

	public String getAttributeType(String name)
	{
		return getAttributeType(this.model, this.ele, name);
	}

	public static String getAttributeType(UmlModel2 model, Element eleFirst, String name)
	{
		// search all inherited classes
		Stack<Element> stack = new Stack<>();
		List<Element> list = new ArrayList<>();
		stack.push(eleFirst);
		while (!!!stack.isEmpty())
		{
			Element ele = stack.pop();
			list.add(ele);
			String query = "*/extension";
			List<Element> inherits = UmlModel2.xPathSearchElements(ele, query);
			for (Element e : inherits)
			{
				String base = e.getAttribute("base");
				if (base == null)
					continue;
				UmlNode2 ie = model.getClass(base);
				if (ie != null)
					stack.push(ie.ele);
			}
		}

		// search in for attribute type
		for (Element e : list)
		{
			// search in children for attribute
			String query = "*//element[@name='" + name + "']";
			Element ele = UmlModel2.xPathSearchElement(e, query);
			if (ele != null)
				return ele.getAttribute("type");
			// search in attributes for attribute
			String query2 = "*//attribute[@name='" + name + "']";
			ele = UmlModel2.xPathSearchElement(e, query2);
			if (ele != null)
				return ele.getAttribute("type");
		}
		// hack that work but above should do it
		for (Element e : list)
		{
			// searched attribute can also be in a reference
			String query2 = "*//element[@ref]";
			List<Element> refs = UmlModel2.xPathSearchElements(e, query2);
			for (Element r : refs)
			{
				String base = r.getAttribute("ref");
				if (base == null)
					continue;
				String query3 = "//*[@name='" + base + "']";
				Element ref = UmlModel2.xPathSearchElement(model.meta, query3);
				if (ref == null)
					continue;
				if (name.equals(ref.getAttribute("name")))
					return ref.getAttribute("type");
			}
		}
		return null;
	}

	public List<UmlNode2> getAssoziationsByName(String name)
	{
		return model.getAssoziationsByName(ele, name);
	}

	public List<UmlNode2> getAssoziationsByClass(String regelung)
	{
		return model.getAssoziationsByClass(ele, regelung);
	}

	public String getName()
	{
		return ele.getAttribute("name");
	}

	public String getNodeAttributeName()
	{
		String name = getAttributeValue(LegalUml.Name);
		if ((name != null) && !!!name.isEmpty())
			return name;
		return ele.getAttribute("name");
	}

	public void setAttributeValue(String name, String value)
	{
		Element attr = model.createElement("attr", null);
		attr.setAttribute("name", name);
		attr.setAttribute("value", value);
		ele.appendChild(attr);
	}

	public String getID()
	{
		return ele.getAttribute("id");
	}

	public UmlNode2 checkReference()
	{
		String ref = ele.getAttribute("ref");
		if ((ref == null) || ref.isEmpty())
			return this;

		return model.getNodeByID(ref);
	}

	public String getNodeName()
	{
		return ele.getNodeName();
	}
}
