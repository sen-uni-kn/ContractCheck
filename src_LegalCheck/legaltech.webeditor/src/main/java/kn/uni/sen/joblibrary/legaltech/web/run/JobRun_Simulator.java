package kn.uni.sen.joblibrary.legaltech.web.run;

import java.util.LinkedList;
import java.util.List;

import kn.uni.sen.joblibrary.legaltech.job_legalsimulator.Job_LegalSimulator;
import kn.uni.sen.jobscheduler.common.impl.JobDataInput;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

/**
 * This JobRun starts a Job_Simulator (red flag) simulation of a contract.
 * 
 * @author Martin Koelbl
 */
public class JobRun_Simulator extends JobRun_Abstract implements Runnable
{
	List<String> selected_actions;
	int action_day;

	public JobRun_Simulator(Integer runID, EventHandler evHandler, ResourceFolder folder, JobRun_Web run,
			ResourceFile analyzeFile, List<String> selected_actions, int action_day)
	{
		super(runID, evHandler, folder, run, analyzeFile);
		this.selected_actions = selected_actions;
		this.action_day = action_day;
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

		ResourceString actions = null;
		for (String act : selected_actions)
		{
			ResourceString res_act = new ResourceString(act);
			if (actions == null)
				actions = res_act;
			else
				actions.addNext(res_act);
		}

		ResourceInteger res_action_day = new ResourceInteger();
		res_action_day.setData("" + this.action_day);

		JobDataInput inData = new JobDataInput();
		inData.add(Job_LegalSimulator.CONTRACT_FILE, analyzeFile);
		inData.add(Job_LegalSimulator.ACTIONS, actions);
		inData.add(Job_LegalSimulator.ACTION_DAY, res_action_day);
		job.addLogger(webRun.logger);

		ResourceDescription.setOwner(job.getInputDescription(), inData);
		if (job != null)
			job.start();
		analyzeFile = null;
		running = false;
		webRun.checkRun();
		logEventStatus(JobEvent.INFO, "end");
	}

	static String showNextActions(ResourceString s)
	{
		List<String> actions = new LinkedList<>();
		while (s != null)
		{
			String call = "analyzeActions('" + s.getData() + "')";
			String ele_text = "<input type='button' value='" + s.getData() + "' onclick=\"" + call + "\")'></input>";
			ele_text = "<tr><td>" + ele_text + "</tr>/<td>";
			actions.add(ele_text);
			s = (ResourceString) s.getChild();
		}
		String text = String.join("\n", actions);
		return "<form><table>" + text + "</table></form>";
	}
}
