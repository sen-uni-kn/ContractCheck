package kn.uni.sen.joblibrary.legaltech.job_legalsimulator;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlSearchClaims;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlSearchContracts;
import kn.uni.sen.jobscheduler.common.model.Job;

public class ActionAnalysis
{
	Job job;

	public ActionAnalysis(Job j)
	{
		job = j;
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
				list.add(name);
			}
		}
		return list;
	}
}
