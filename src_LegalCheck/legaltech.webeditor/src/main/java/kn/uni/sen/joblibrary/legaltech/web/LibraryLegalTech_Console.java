package kn.uni.sen.joblibrary.legaltech.web;

import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.jobscheduler.common.helper.Helper;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.console.Console_Library;
import kn.uni.sen.jobscheduler.experiment.Experiment_Console;
import kn.uni.sen.joblibrary.legaltech.experiment.Experiment_LegalTech_Console;
import kn.uni.sen.joblibrary.legaltech.library.JobLibrary_LegalTech;

public class LibraryLegalTech_Console extends Console_Library
{
	String folder = "result";

	public LibraryLegalTech_Console()
	{
		super(new JobLibrary_LegalTech());
	}

	@Override
	public List<String> getExperimentList()
	{
		return getStaticExperimentList();
	}

	public static List<String> getStaticExperimentList()
	{
		List<String> expList = new ArrayList<>();
		expList.add("experiment_test");
		expList.add("experiment_spin2022");
		expList.add("experiment_journal2023");
		return expList;
	}

	public static void main(String[] args)
	{
		Console_Library cons = new LibraryLegalTech_Console();
		cons.run(args);
	}

	@Override
	protected List<String> createHelp(List<String> helpList)
	{
		helpList = super.createHelp(helpList);
		helpList.add("-web --web: run legaltech web server");
		return helpList;
	}

	@Override
	protected Experiment_Console createExperiment(String name, List<String> args)
	{
		ResourceFile file = new ResourceFile(name);
		file.setExtension(".xml");
		String fileName = Helper.storeUrlFile(file.getData(), folder);
		if (fileName == null)
			return null;
		args.add(0, fileName);
		return new Experiment_LegalTech_Console();
	}

	public static List<String> getModelExperimentList()
	{
		List<String> modelList = new ArrayList<>();
		modelList.add("ContractBad");
		return modelList;
	}
}
