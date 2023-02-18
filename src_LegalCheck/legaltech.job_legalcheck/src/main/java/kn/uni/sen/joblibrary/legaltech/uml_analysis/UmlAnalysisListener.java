package kn.uni.sen.joblibrary.legaltech.uml_analysis;

/**
 * General interface for a contract analysis.
 * 
 * @author Martin Koelbl (C) 2023
 */
public interface UmlAnalysisListener
{
	public void reportError(String text);

	public void reportWarning(String text);

	public void reportGood(String text);
}
