package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

public abstract class UmlAnalysisSmtAbstract extends UmlAnalysisAbstract implements UmlAnalysis, UmlAnalysisFactory
{
	UmlModel2 model;

	String name = "";
	double timeZ3 = -1;
	double memZ3 = -1;
	int constraintCount = -1;
	int varCount = -1;
	int result = -1;

	public UmlAnalysisSmtAbstract(Job job, String name, String anaName, UmlModel2 model)
	{
		super(job, anaName);
		this.model = model;
		this.name = name;
	}

	abstract SmtModel createSMTCode(UmlModel2 model);

	ResourceFile createFile(String name, String app)
	{
		if (app == null)
			app = "";
		String folder = job.getFolderText();
		String filePath = ResourceFolder.appendFolder(folder, name + app) + ".z3";

		ResourceFile file = new ResourceFile(filePath);
		if (file.exists())
			file.removeFile();
		if (!!!file.createFile(false))
		{
			job.logEventStatus("Error", "Could not create analysis file: " + file.getData());
			return null;
		}
		return file;
	}

	int countText(String text, String val)
	{
		int counter = 0;
		int index = text.indexOf(val);
		while (index >= 0)
		{
			counter++;
			index = text.indexOf(val, index + 1);
		}
		return counter;
	}

	void codeStatistic(String code)
	{
		constraintCount = countText(code, "<");
		constraintCount += countText(code, "=");
		constraintCount += countText(code, ">");
		varCount = countText(code, "declare-const");
	}

	public String getStatisticString(String var, String text)
	{
		if (text == null)
			return null;
		int index = text.indexOf(var);
		if (index < 0)
			return null;
		index = text.indexOf(" ", index);
		int end = text.indexOf("\n", index);
		String mem = text.substring(index, end).replace(" ", "");
		return mem.replace(" ", "").replace(")", "");
	}

	public ParseSmtResult runSmtAnalysis(UmlModel2 model, String code, String app, SmtModel smtModel)
	{
		if (app != null)
			name = app;
		memZ3 = -1;
		timeZ3 = -1;
		constraintCount = -1;
		varCount = -1;
		String fileName = "Analysis" + (anaName + "_" + name).replace(" ", "_");
		ResourceFile file = createFile(fileName, app);
		if (code == null)
			return null;

		codeStatistic(code);
		file.appendText(code);
		file.closeFile();

		Z3Call call = new Z3Call();
		call.runFile(file.getData(), true);

		ParseSmtResult res = new ParseSmtResult(model, call, smtModel);

		// String cmd = "z3 -st " + ;
		// String text = HelperConsole.runCommand(cmd, null, true, 600);

		memZ3 = call.getMemory();
		timeZ3 = call.getTime();
		return res;
	}

	// used to output metadata (runtime, memory, ...) of analysis
	@Override
	void log(String statisticsFile)
	{
		if (statisticsFile == null)
			// file still not open
			return;

		String resultText = "unkown";
		if (result == 0)
			resultText = "violation";
		else if (result == 1)
			resultText = "hold";

		List<String> list = new ArrayList<>();
		list.add(anaName);
		list.add(name);
		list.add("" + resultText);
		list.add(timeZ3 + "s");
		list.add(memZ3 + "MB");
		list.add("" + constraintCount);
		list.add("" + varCount);
		ResourceFile.appendText2File(statisticsFile, String.join(" & ", list) + "\\\\\n");
	}
}
