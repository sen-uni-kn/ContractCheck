package kn.uni.sen.joblibrary.legaltech.parser.model;

import java.util.ArrayList;
import java.util.List;

public class UmlModel
{
	List<UmlNode> NodeList = new ArrayList<>();
	List<UmlAssociation> AssList = new ArrayList<>();

	public void addNode(UmlNode n)
	{
		if (n == null)
			return;

		String id = n.getID();
		for (UmlNode c : NodeList)
		{
			if (id.equals(c.getID()))
				// todo: warning
				return;
		}

		NodeList.add(n);
	}

	public void addAssoziation(UmlAssociation a)
	{
		if (a == null)
			return;
		AssList.add(a);
	}

	public List<UmlNode> getClassInstances(String name)
	{
		List<UmlNode> list = new ArrayList<>();
		UmlNode cl = getClass(name);
		for (UmlNode n : NodeList)
		{
			UmlNode cl2 = n.getClass2();
			if (cl2 == null)
				continue;
			if (cl2 == cl)
				list.add(n);
			else if (cl2.inheritatesFrom(cl))
				list.add(n);
		}
		return list;
	}

	List<UmlNode> getInstances(UmlNode Class)
	{
		List<UmlNode> list = new ArrayList<>();
		for (UmlNode n : NodeList)
		{
			if (!!!n.isInstance())
				continue;
			if (n.getClass2() == Class)
				list.add(n);
		}
		return list;
	}

	public UmlNode getClass(String cl)
	{
		if (cl == null)
			return null;
		for (UmlNode n : NodeList)
		{
			if (n.isInstance())
				continue;
			if (cl.equals(n.getName()))
				return n;
		}

		if (cl.equals("String"))
		{
			UmlNode n = new UmlNode("String", "String");
			NodeList.add(n);
			return n;
		} else if (cl.equals("Integer"))
		{
			UmlNode n = new UmlNode("Integer", "Integer");
			NodeList.add(n);
			return n;
		}

		return null;
	}

	public UmlNode getClassByID(String cl)
	{
		if (cl == null)
			return null;
		for (UmlNode n : NodeList)
		{
			if (n.isInstance())
				continue;
			if (cl.equals(n.getID()))
				return n;
		}
		return null;
	}

	public UmlNode getClassByName(String cl)
	{
		if (cl == null)
			return null;
		for (UmlNode n : NodeList)
		{
			if (n.isInstance())
				continue;
			if (cl.equals(n.getName()))
				return n;
		}
		return null;
	}

	public UmlElement getByID(String id)
	{
		if (id == null)
			return null;
		for (UmlElement e : NodeList)
			if (id.equals(e.getID()))
				return e;
		for (UmlElement e : AssList)
			if (id.equals(e.getID()))
				return e;
		return null;
	}

	public UmlNode getNodeByID(String id)
	{
		if (id == null)
			return null;
		for (UmlNode e : NodeList)
			if (id.equals(e.getID()))
				return e;
		return null;
	}

	public UmlNode getNodeByName(String name)
	{
		if (name == null)
			return null;
		for (UmlNode e : NodeList)
			if (name.equals(e.getName()))
				return e;
		return null;
	}

	public boolean hasInstanceClass(String className)
	{
		List<UmlNode> cList = getClassInstances(className);

		for (UmlNode cl : cList)
		{
			List<UmlNode> list = getInstances(cl);
			if (list == null)
				continue;
			if (!!!list.isEmpty())
				return true;
		}
		return false;
	}
}
