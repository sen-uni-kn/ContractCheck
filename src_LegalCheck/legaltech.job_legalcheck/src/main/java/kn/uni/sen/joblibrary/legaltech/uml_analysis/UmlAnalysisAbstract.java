package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitorAbstract;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

public abstract class UmlAnalysisAbstract extends LegalVisitorAbstract implements UmlAnalysis
{
	SmtModel smtModel = new SmtModel();
	ReportResult report;
	String anaName;
	UmlAnalysisFactory anaFac;

	public UmlAnalysisAbstract(Job j, String name, UmlAnalysisFactory anaFac)
	{
		super(j);
		this.anaName = name;
		assertTrue(!!!anaName.isEmpty());
		this.anaFac = anaFac;
	}

	@Override
	public String getName()
	{
		return anaName;
	}

	String getCorrectedName(String n)
	{
		if (n == null)
			return null;
		n = n.replace("ö", "oe");
		n = n.replace("ä", "ae");
		n = n.replace("ü", "ue");
		n = n.replace("Ö", "Oe");
		n = n.replace("Ä", "Ae");
		n = n.replace("Ü", "Ue");
		return n.replaceAll("[^a-zA-Z0-9_]", "");
	}

	public void reportError(String text)
	{
		report(UmlResultState.ERROR, text);
	}

	public void reportWarning(String text)
	{
		report(UmlResultState.WARNING, text);
	}

	public void reportGood(String text)
	{
		report(UmlResultState.GOOD, text);
	}

	public void reportUnsat(String name, String text, String core, UmlResultState state)
	{
		UmlResult res = new UmlResult();
		res.rest = state;
		res.name = name;
		res.core = core;
		res.anaName = getName();
		res.text = text;
		if (report == null)
		{
			job.logEventStatus("Warning", "Report class is missing");
			return;
		}
		report.reportResult(this, res);
	}

	public void reportRun(String name, String text, String diagram, UmlResultState state)
	{
		UmlResult res = new UmlResult();
		res.rest = state;
		res.name = name;
		res.diagram = diagram;
		res.anaName = getName();
		res.text = text;
		if (report == null)
		{
			job.logEventStatus("Warning", "Report class is missing");
			return;
		}
		report.reportResult(this, res);
	}

	public void reportMinMax(String name, String text, String minMax, UmlResultState state)
	{
		UmlResult res = new UmlResult();
		res.rest = state;
		res.name = name;
		res.minMax = minMax;
		res.anaName = getName();
		res.text = text;
		if (report == null)
		{
			job.logEventStatus("Warning", "Report class is missing");
			return;
		}
		report.reportResult(this, res);
	}

	public void report(UmlResultState state, String text)
	{
		UmlResult res = new UmlResult();
		res.rest = state;
		res.diagram = null;
		res.anaName = getName();
		res.text = text;
		if (report == null)
		{
			job.logEventStatus(JobEvent.WARNING, "Report class is missing");
			return;
		}
		report.reportResult(this, res);
	}

	Set<UmlNode2> getDependentSet(List<UmlNode2> claimList, UmlNode2 claim)
	{
		Set<UmlNode2> set = new HashSet<>();
		String name = claim.getName();
		for (UmlNode2 c : claimList)
		{
			UmlNode2 cn = c.getAssoziationByName(LegalUml.Depend);
			if (cn == null)
				continue;
			String val = cn.getName();
			if (val == null)
				continue;
			if (val.contains(name))
				set.add(c);
		}
		return set;
	}

	Set<UmlNode2> getTriggerSet(List<UmlNode2> claimList, UmlNode2 claim)
	{
		Set<UmlNode2> set = new HashSet<>();
		String name = claim.getName();
		for (UmlNode2 c : claimList)
		{
			UmlNode2 cn = c.getAssoziationByName(LegalUml.Trigger);
			if (cn == null)
				continue;
			String val = cn.getName();
			if (val == null)
				continue;
			if (val.contains(name))
				set.add(c);
		}
		return set;
	}

	// used to output metadata (runtime, memory, ...) of analysis
	void log(String statisticsFile)
	{
		if (statisticsFile == null)
		{
			statisticsFile = ResourceFolder.appendFolder(job.getFolderText(), "statistics.txt");
			ResourceFile.removeFile(statisticsFile);
			String head = "name & time & mem & constraints & variables\\\\\n";
			ResourceFile.appendText2File(statisticsFile, head);
		}

		if (statisticsFile == null)
			return;
		// String fullName = anaName + name;
		// String text = fullName + " & " + timeZ3 + "s & " + memZ3 + "MB & " +
		// constraintCount + " & " + varCount
		// + "\\\\\n";
		//ResourceFile.appendText2File(statisticsFile, text);
	}

}
