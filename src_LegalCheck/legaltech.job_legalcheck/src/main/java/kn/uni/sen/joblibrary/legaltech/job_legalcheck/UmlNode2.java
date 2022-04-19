package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;

public class UmlNode2
{
	Element ele;
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

	public UmlNode2 getAssoziationByName(String name)
	{
		return model.getAssoziationByName(ele, name);
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
		return ele.getAttribute("id2");
	}

	public UmlNode2 checkReference()
	{
		String ref = ele.getAttribute("ref");
		if ((ref == null) || ref.isEmpty())
			return this;

		return model.getNodeByID(ref);
	}
}
