package kn.uni.sen.joblibrary.legaltech.experiment;

import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.jobscheduler.common.helper.Helper;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.experiment.Experiment_Console;
import kn.uni.sen.jobscheduler.experiment.Job_Experiment;

public class Experiment_LegalTech_Console extends Experiment_Console
{
	String[] runArgs;

	public Experiment_LegalTech_Console()
	{
		super();
		System.out.println("Java Version: " + Helper.getJavaVersion());
	}

	public static void loadDynamicLibrary(String libraryName)
	{
		int val = Helper.getJavaVersion();
		System.out.println("Java Version " + val);
		String libSource = libraryName.replace(".jar", "_v" + val + ".jar");

		ClassLoader classLoader = Experiment_LegalTech_Console.class.getClassLoader();
		URL urlFile = classLoader.getResource(libSource);
		if (urlFile == null)
		{
			System.out.println("Library " + libraryName + " not found. Only Java 11 and 12 are supported.");
			return;
		}
		String curLib = libraryName;
		ResourceFile.writeURL2File(urlFile, "lib/" + curLib);

		Helper.addLoadLib("./lib");
	}

	private String getLib()
	{
		String version = "1.2.0";
		String lib = "legaltech.webeditor-" + version /* + "-jar-with-dependencies" */ + ".jar";
		String libMaven = "target" + ResourceFolder.getSplitSign() + lib;
		if (ResourceFile.exists(libMaven))
			lib = libMaven;
		return lib;
	}

	static String storeFile(String nameFile)
	{
		if (ResourceFile.exists(nameFile))
			return nameFile;

		ClassLoader classLoader = Experiment_LegalTech_Console.class.getClassLoader();
		URL urlFile = classLoader.getResource(nameFile);
		if (urlFile == null)
			return nameFile;
		nameFile = urlFile.getPath();
		ResourceFile file = new ResourceFile(nameFile);

		if (file.exists())
			return nameFile;

		file.setFolder("result");
		String filePath = file.getData();

		// anaPath.createFolder();
		ResourceFile.writeURL2File(urlFile, filePath);
		return filePath;
	}

	@Override
	public void run(String[] args)
	{
		if (args.length <= 0)
		{
			logEventStatus(JobEvent.ERROR, "Missing input parameters");
			return;
		}

		String filePath = null;
		List<String> list = new ArrayList<>();
		for (String s : args)
			if (filePath == null)
				filePath = s;
			else
				list.add(s);

		// get QuantUM library path
		list.add(0, "-" + Job_Experiment.LIBRARY);
		list.add(1, getLib());
		list.add(2, "-" + Job_Experiment.EXPERIMENT);
		list.add(3, filePath);
		//list.add(4, "-" + Job_Experiment.PRE);
		//list.add(5, "kn/uni/sen/joblibrary/tartar/gui/LibraryQuantUM_Console \\\n");

		String[] runArgs = list.toArray(new String[] {});
		super.run(runArgs);
	}

	public static void main(String args[])
	{
		if (args.length == 0)
		{
			System.out.println("Give experiment file as argument.");
			return;
		}
		(new Experiment_LegalTech_Console()).run(args);
	}
}
