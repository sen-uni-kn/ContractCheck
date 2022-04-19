package kn.uni.sen.joblibrary.legaltech.parser.model;

public class UmlAttribute extends UmlElementSimple
{
	String Name;
	UmlNode Class;
	String Value;

	public UmlAttribute(String id, String n, UmlNode c)
	{
		super(id);
		Name = n;
		Class = c;
	}

	String getName()
	{
		return Name;
	}

	public UmlNode getClassType()
	{
		return Class;
	}

	public void setValue(String value)
	{
		Value = value;
	}

	public String getValue()
	{
		return Value;
	}
}
