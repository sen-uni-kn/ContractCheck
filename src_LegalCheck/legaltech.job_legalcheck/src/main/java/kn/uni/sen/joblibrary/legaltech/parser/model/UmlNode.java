package kn.uni.sen.joblibrary.legaltech.parser.model;

import java.util.ArrayList;
import java.util.List;

public class UmlNode extends UmlElementSimple
{
	public UmlNode(String id, String name)
	{
		super(id);
		this.name = name;
	}

	UmlNode Class;
	boolean BInstance = false;
	String name;

	List<UmlAttribute> AttrList = new ArrayList<>();
	List<UmlOperation> OpList = new ArrayList<>();
	List<UmlAssociation> AssList = new ArrayList<>();
	List<UmlNode> InheritateList = new ArrayList<>();

	public void addAttribute(UmlAttribute a)
	{
		if ((a == null) || (a.getName() == null))
			return;
		UmlAttribute at = getAttribute(name);
		while (at != null)
		{
			removeAttribute(at);
			a = getAttribute(name);
		}

		AttrList.add(a);
	}

	public void removeAttribute(UmlAttribute a)
	{
		AttrList.remove(a);
	}

	public void addOperation(UmlOperation o)
	{
		if (o == null)
			return;
		OpList.add(o);
	}

	public boolean hasAttribute(String name)
	{
		for (UmlAttribute attr : AttrList)
		{
			if (name.equals(attr.getName()))
				return true;
		}
		return false;
	}

	public UmlAttribute getAttribute(String name)
	{
		for (UmlAttribute attr : AttrList)
		{
			if (name.equals(attr.getName()))
				return attr;
		}
		return null;
	}

	public String getAttributeValue(String name)
	{
		for (UmlAttribute attr : AttrList)
		{
			if (name.equals(attr.getName()))
			{
				return attr.getValue();
			}
		}
		return null;
	}

	public void addAssoziation(UmlAssociation a)
	{
		if (a == null)
			return;
		AssList.add(a);
	}

	public void setInstanceOf(UmlNode c)
	{
		Class = c;
		BInstance = true;
	}

	public boolean isInstance()
	{
		return (Class != null) || BInstance;
	}

	public UmlNode getClass2()
	{
		return Class;
	}

	public List<UmlAssociation> getAssoziationsByName(String name)
	{
		List<UmlAssociation> list = new ArrayList<>();
		if (name == null)
			return list;
		for (UmlAssociation ass : AssList)
			if (name.equals(ass.getName()))
				list.add(ass);
		if (list.isEmpty() && !!!isInstance())
		{
			for (UmlNode in : InheritateList)
			{
				list.addAll(in.getAssoziationsByName(name));
			}
		}

		return list;
	}

	public void setName(String n)
	{
		name = n;
	}

	public String getName()
	{
		return name;
	}

	public List<UmlAttribute> getAttributesByName(String name)
	{
		List<UmlAttribute> list = new ArrayList<>();
		if (name == null)
			return list;
		for (UmlAttribute attr : AttrList)
		{
			if (name.equals(attr.getName()))
				list.add(attr);
		}

		if (list.isEmpty() && !!!isInstance())
		{
			for (UmlNode in : InheritateList)
			{
				List<UmlAttribute> list2 = in.getAttributesByName(name);
				list.addAll(list2);
			}

		}

		return list;
	}

	public void addInheritate(UmlNode other)
	{
		if (other == null)
			return;
		InheritateList.add(other);
	}

	public List<UmlNode> getAssociationedClassInstance(UmlNode claimClass)
	{
		List<UmlNode> list = new ArrayList<>();

		for (UmlAssociation ass : AssList)
		{
			UmlNode node = ass.hasEndNodeClass(claimClass);
			if ((node != null) && (!!!list.contains(node)))
				list.add(node);
		}

		return list;
	}

	public List<UmlNode> getAssociatedNodeByKey(String key)
	{
		List<UmlNode> list = new ArrayList<>();

		for (UmlAssociation ass : AssList)
		{
			UmlNode node = ass.hasEndNodeKey(key);
			if (node != null)
				list.add(node);
		}

		return list;
	}

	public boolean inheritatesFrom(UmlNode classNode)
	{
		if (Class != null)
			if (Class == classNode)
				return true;
			else
				return Class.inheritatesFrom(classNode);
		for (UmlNode in : InheritateList)
		{
			if (in == classNode)
				return true;
			if (in.inheritatesFrom(classNode))
				return true;
		}
		return false;
	}

	public boolean inheritatesFrom(String className)
	{
		if (className == null)
			return false;

		if (Class != null)
		{
			String name = Class.getName();
			if ((name != null) && (name.equals(className)))
				return true;
			if (Class.inheritatesFrom(className))
				return true;
		}

		for (UmlNode in : InheritateList)
		{
			String name = in.getName();
			if (name.equals(className))
				return true;

			if (in.inheritatesFrom(className))
				return true;
		}
		return false;
	}

	public void addAtt(String name, String val)
	{
		UmlAttribute attr = new UmlAttribute("", name, null);
		attr.setValue(val);
		addAttribute(attr);
	}

	public void addAss(String name, UmlNode n)
	{
		UmlAssociation ass = new UmlAssociation("");
		ass.setName(name);
		ass.addAssNode(name, n);
		addAssoziation(ass);
	}

	public void addAttAss(String name, UmlNode n, boolean bAtt)
	{
		UmlNode cl = getClass2();
		if (cl != null)
		{
			List<UmlAttribute> list = cl.getAttributesByName(name);
			if (!!!list.isEmpty())
			{
				// addAtt(name, n, bAtt);
				return;
			} else
			{
				List<UmlAssociation> list2 = cl.getAssoziationsByName(name);
				if (!!!list2.isEmpty())
				{
					addAss(name, n);
					return;
				}
			}
		}
		if (bAtt)
			;// addAtt(name, n, bAtt);
		else
			addAss(name, n);
	}
}
