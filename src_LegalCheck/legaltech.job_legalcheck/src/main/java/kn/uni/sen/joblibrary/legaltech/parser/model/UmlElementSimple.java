package kn.uni.sen.joblibrary.legaltech.parser.model;

/**
 * every UML element has a unique id
 * 
 * @author Martin Koelbl
 */
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
