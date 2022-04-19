package kn.uni.sen.joblibrary.legaltech.parser.model;

import java.util.ArrayList;
import java.util.List;

public class UmlAssociation extends UmlElementSimple
{
	public static final String ASS_INHERITATES = "inheritates";
	public static final String ASS_INSTANCES = "instances";

	String name;
	List<Pair<String, UmlNode>> NodeList = new ArrayList<Pair<String, UmlNode>>();

	public UmlAssociation(String id)
	{
		super(id);
	}

	public void setName(String name)
	{
		this.name = name;
	}

	public String getName()
	{
		return name;
	}

	public void addAssNode(String name, UmlNode n)
	{
		if (n == null)
			return;
		// if(name == null)
		// name = "";
		NodeList.add(new Pair<String, UmlNode>(name, n));
	}

	public List<UmlNode> getEndNodes()
	{
		List<UmlNode> list = new ArrayList<>();
		for (Pair<String, UmlNode> n : NodeList)
			list.add(n.getValue());
		return list;
	}

	public UmlNode hasEndNodeClass(UmlNode claimClass)
	{
		for (Pair<String, UmlNode> n : NodeList)
		{
			UmlNode o = n.value;
			UmlNode cl = o.getClass2();
			if (cl == null)
				continue;
			if ((cl == claimClass) || (cl.inheritatesFrom(claimClass)))
				return o;
		}
		return null;
	}

	public UmlNode hasEndNodeKey(String key)
	{
		if (key == null)
			return null;
		for (Pair<String, UmlNode> n : NodeList)
		{
			if (key.equals(n.key))
				return n.getValue();
		}
		return null;
	}

}
