package kn.uni.sen.joblibrary.legaltech.job_legalsimulator;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.ReportResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysis;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResultState;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlSearchClaims;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlSearchContracts;
import kn.uni.sen.jobscheduler.common.model.Job;

public class ActionAnalysis implements UmlAnalysis
{
	public static final String Name = "Actions";
	UmlModel2 model;
	Job job;
	List<String> actions;

	public ActionAnalysis(Job j, UmlModel2 model, List<String> actions)
	{
		job = j;
		this.model = model;
		this.actions = actions;
	}

	@Override
	public String getName()
	{
		return Name;
	}

	@Override
	public void runAnalysis(ReportResult report, String statisticsFile)
	{
		List<String> actions = computePossibleActions(0, model);

		UmlResult res = new UmlResult();
		res.rest = UmlResultState.NONE;
		res.name = Name + "_";
		res.diagram = "";
		res.anaName = getName();
		res.text = "";
		res.actions = actions;
		if (report == null)
		{
			job.logEventStatus("Warning", "Report class is missing");
			return;
		}
		report.reportResult(this, res);
		report.reportResult(this, null);
	}

	/**
	 * This function will compute possible actions on a concrete day. Currently
	 * it returns a list of claism
	 */
	List<String> computePossibleActions(int day, UmlModel2 model2)
	{
		List<String> list = new ArrayList<>();
		List<Element> contracts = (new UmlSearchContracts(job)).searchContracts(model2);
		for (Element conEle : contracts)
		{
			List<Element> claims = (new UmlSearchClaims(job)).searchContractClaims(model2, conEle);
			for (Element claimEle : claims)
			{
				String conName = (new UmlNode2(model2, conEle)).getName();
				String claimName = (new UmlNode2(model2, claimEle)).getName();
				String name = conName + "_" + claimName;

				if (!!!actions.contains(name))
					list.add(name);
			}
		}
		return list;
	}
}
