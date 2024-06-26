package kn.uni.sen.joblibrary.legaltech.parser.model;

/**
 * data structure e.g. to store two elements as one element in a list
 * 
 * @author Martin Koelbl
 */
public class Pair<T1, T2>
{
	protected T1 key;
	protected T2 value;

	public Pair(T1 name, T2 value)
	{
		this.key = name;
		this.value = value;
	}

	public T1 getKey()
	{
		return key;
	}

	public T2 getValue()
	{
		return value;
	}
}
