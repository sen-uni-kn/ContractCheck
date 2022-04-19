package kn.uni.sen.joblibrary.legaltech.parser.model;

public class UmlElementSimple implements UmlElement
{
	String id;

	public UmlElementSimple(String id)
	{
		this.id = id;
	}

	@Override
	public String getID()
	{
		return id;
	}
}
