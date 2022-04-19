package kn.uni.sen.joblibrary.legaltech.web.run;

import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.core.impl.JobServerAbstract;
import kn.uni.sen.jobscheduler.core.model.JobRun;
import kn.uni.sen.jobscheduler.core.model.JobSession;

public class JobServer_Web extends JobServerAbstract
{
	public JobServer_Web()
	{
		super("LegalTech", "result");
	}

	@Override
	protected JobRun createJobRun(Integer id)
	{
		ResourceFolder fol = createSessionFolder("result");
		return new JobRun_Contract(id, getEventHandler(), fol);
	}

	@Override
	protected JobSession createSessionInstance(String user)
	{
		return null;
	}
}
