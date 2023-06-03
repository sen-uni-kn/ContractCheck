package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;

/**
 * stores the analysis results and hand them over to the job
 * 
 * @author Martin Koelbl
 */
public class UmlResult
{
	public String anaName;
	public String name;
	public UmlResultState rest;
	public String diagram;
	public String text;
	public List<String> actions;
	public String minMax;
	public String core;
}
