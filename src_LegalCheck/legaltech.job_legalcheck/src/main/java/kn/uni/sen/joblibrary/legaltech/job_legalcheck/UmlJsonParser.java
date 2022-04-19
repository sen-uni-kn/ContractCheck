package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.io.InputStream;

import kn.uni.sen.joblibrary.legaltech.parser.model.UmlModel;
import kn.uni.sen.jobscheduler.common.model.Job;

@Deprecated
public class UmlJsonParser
{
	Job job;

	public UmlJsonParser(Job j)
	{
		job = j;
	}

	public UmlModel parseFile(InputStream xmiStream)
	{
		return null;
	}
}
