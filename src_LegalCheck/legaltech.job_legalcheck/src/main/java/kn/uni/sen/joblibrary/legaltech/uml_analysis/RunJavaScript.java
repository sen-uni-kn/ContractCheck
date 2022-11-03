package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import javax.script.*;
import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;

/**
 * currently the sequence diagrams are generates by JavaScript in the web interface
 * todo: idea is to generate the sequence diagrams also for console executions
 *  
 * @author Martin Koelbl
 */
public class RunJavaScript
{
	void run(String script)
	{
		ScriptEngine ee = new ScriptEngineManager().getEngineByName("Nashorn");

		try
		{
			ee.eval(script);
		} catch (ScriptException e)
		{
			e.printStackTrace();
		}
	}

	static void runScript(String script, String folder)
	{
		//todo:
		//script = "print('Welcome to Geeks!!! ');";
		//(new RunJavaScript()).run(script);
	}
}
