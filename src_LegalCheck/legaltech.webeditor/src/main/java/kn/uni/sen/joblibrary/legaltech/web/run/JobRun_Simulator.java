package kn.uni.sen.joblibrary.legaltech.web.run;

import kn.uni.sen.joblibrary.legaltech.job_legalsimulator.Job_LegalSimulator;
import kn.uni.sen.jobscheduler.common.impl.JobDataInput;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

/**
 * This JobRun starts a Job_Simulator (red flag) simulation of a contract.
 * 
 * @author Martin Koelbl
 */
public class JobRun_Simulator extends JobRun_Abstract implements Runnable
{
	public JobRun_Simulator(Integer runID, EventHandler evHandler, ResourceFolder folder, JobRun_Web run,
			ResourceFile analyzeFile)
	{
		super(runID, evHandler, folder, run, analyzeFile);
	}

	@Override
	synchronized public void run()
	{
		logEventStatus(JobEvent.INFO, "--------------------");
		if (running)
			return;
		running = true;
		runSimulator();
	}

	protected void runSimulator()
	{
		job = new Job_LegalSimulator(this);
		if (analyzeFile == null)
		{
			String path = ResourceFolder.appendFolder(job.getFolderText(), "contractAna.json");
			ResourceFolder.createFolder(job.getFolderText());
			analyzeFile = new ResourceFile(path);
			webRun.saveContract(analyzeFile);
		}

		JobDataInput inData = new JobDataInput();
		inData.add(Job_LegalSimulator.CONTRACT_FILE, analyzeFile);
		//job.setEventHandler(webRun.eventHandler);
		job.addLogger(webRun.logger);

		ResourceDescription.setOwner(job.getInputDescription(), inData);
		if (job != null)
			job.start();
		analyzeFile = null;
		running = false;
		webRun.checkRun();
		logEventStatus(JobEvent.INFO, "end");
	}
}
