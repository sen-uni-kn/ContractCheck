package kn.uni.sen.joblibrary.legaltech.web.run;

import org.springframework.scheduling.annotation.Async;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.Job_LegalCheck;
import kn.uni.sen.jobscheduler.common.impl.JobDataInput;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

/** This JobRun starts a Job_LegalCheck (red flag) analysis of a contract.
 * 
 * @author Martin Koelbl
 */
public class JobRun_Check extends JobRun_Abstract implements Runnable
{
	public JobRun_Check(Integer runID, EventHandler handler, ResourceFolder folder, JobRun_Web run,
			ResourceFile analyzeFile)
	{
		super(runID, handler, folder, run, analyzeFile);
	}

	@Async("threadPoolTaskExecutor")
	public void analyzeContract(ResourceFile fileR)
	{
		if (running)
			return;

		running = true;
		analyzeFile = fileR;
		Thread thread = new Thread(this);
		thread.start();
	}

	@Override
	synchronized public void run()
	{
		logEventStatus(JobEvent.INFO, "--------------------");
		if (running)
			return;
		running = true;
		runAnalyzeModel();
	}

	private void runAnalyzeModel()
	{
		job = new Job_LegalCheck(this);
		if (analyzeFile == null)
		{
			String path = ResourceFolder.appendFolder(job.getFolderText(), "contractAna.json");
			ResourceFolder.createFolder(job.getFolderText());
			analyzeFile = new ResourceFile(path);
			webRun.saveContract(analyzeFile);
		}

		JobDataInput inData = new JobDataInput();
		inData.add(Job_LegalCheck.CONTRACT_FILE, analyzeFile);
		// job.setEventHandler(eventHandler);
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
