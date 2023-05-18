package kn.uni.sen.joblibrary.legaltech.web.run;

import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.core.impl.JobRunAbstract;
import kn.uni.sen.jobscheduler.core.model.JobScheduler;

public class JobRun_Abstract extends JobRunAbstract
{
	JobRun_Web webRun;
	Job job = null;
	boolean running = false;
	ResourceFile analyzeFile = null;

	public JobRun_Abstract(Integer runID, EventHandler handler, ResourceFolder folder, JobRun_Web run,
			ResourceFile analyzeFile)
	{
		super(runID, handler, folder);
		this.webRun = run;
		this.analyzeFile = analyzeFile;
	}

	@Override
	protected JobScheduler createScheduler(ResourceFileXml jobFile, ResourceFolder folder, String schedulerType)
	{
		return null;
	}

	boolean isRunning()
	{
		return running;
	}

	public Job getJob()
	{
		return job;
	}
}
