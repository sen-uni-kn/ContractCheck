package kn.uni.sen.joblibrary.legaltech.parser.model;

/**
 * operation in an UML class node
 * 
 * @author Martin Koelbl
 */
public class UmlOperation extends UmlElementSimple
{
	public UmlOperation(String id, String name)
	{
		super(id);
	}

	String Name;

	String getName()
	{
		return Name;
	}

	void addParameter(String name, UmlNode c)
	{

	}

	void addResult(String name, UmlNode c)
	{

	}
}
