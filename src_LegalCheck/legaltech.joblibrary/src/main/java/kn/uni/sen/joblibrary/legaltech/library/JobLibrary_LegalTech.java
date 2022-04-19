package kn.uni.sen.joblibrary.legaltech.library;

import java.util.LinkedList;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.Job_LegalCheck;
//import kn.uni.sen.joblibrary.legaltech.job_legaltrace.Job_LegalTrace;
import kn.uni.sen.jobscheduler.common.impl.JobLibraryAbstract;
import kn.uni.sen.jobscheduler.common.model.Job;

public class JobLibrary_LegalTech extends JobLibraryAbstract
{
	public JobLibrary_LegalTech()
	{
		this(JobLibrary_LegalTech.class.getSimpleName());
	}

	public JobLibrary_LegalTech(String libraryName)
	{
		JobList = new LinkedList<Class<? extends Job>>();

		if (libraryName == null)
			return;

		if (getLibraryName().compareTo(libraryName) == 0)
		{
			JobList.add(Job_LegalCheck.class);
			// JobList.add(Job_LegalTrace.class);
			// JobList.add(Job_ContractCheck.class);
		}
	}

	@Override
	public String getLibaryVersion()
	{
		return "JV_1.0";
	}
}
