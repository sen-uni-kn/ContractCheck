package kn.uni.sen.joblibrary.legaltech.job_legalsimulator;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.Legal2Constraints;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.ParseSmtResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.ReportResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysis;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSmtAbstract;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResultState;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlSearchClaims;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlSearchContracts;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;

public class UmlAnalysis_Actions extends UmlAnalysisSmtAbstract implements UmlAnalysis
{
	public static final String Name = "Actions";

	Map<String, Integer> actions;
	int action_day;

	Element contractEle = null;
	Map<Element, Integer> claimEles;

	public UmlAnalysis_Actions(Job j, Map<String, Integer> actions, int action_day)
	{
		super(j, null, Name, null);
		this.actions = actions;
		this.action_day = action_day;
	}

	private UmlAnalysis_Actions(Job j, String name, UmlModel2 model, Element con, Map<Element, Integer> claims,
			int action_day)
	{
		super(j, name, Name + "_" + name, model);
		contractEle = con;
		claimEles = claims;
		this.action_day = action_day;
	}

	@Override
	public String getName()
	{
		return Name;
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

				if (!!!actions.containsKey(name))
					list.add(name);
			}
		}
		return list;
	}

	UmlAnalysis createActionsAnalysis(String name, Map<String, Integer> actions)
	{
		List<Element> contracts = (new UmlSearchContracts(job)).searchContracts(model);
		for (Element conEle : contracts)
		{
			Map<Element, Integer> claimAnalysisList = new HashMap<>();
			List<Element> claims = (new UmlSearchClaims(job)).searchContractClaims(model, conEle);
			for (Element claimEle : claims)
			{
				String conName = (new UmlNode2(model, conEle)).getName();
				String claimName = (new UmlNode2(model, claimEle)).getName();
				String nameContractClaim = conName + "_" + claimName;
				if (actions.containsKey(nameContractClaim))
				{
					int act_day = actions.get(nameContractClaim);
					claimAnalysisList.put(claimEle, act_day);
				}
			}
			if (claimAnalysisList.size() != actions.size())
				continue;
			return new UmlAnalysis_Actions(job, name, model, conEle, claimAnalysisList, action_day);
		}
		assertTrue(false);
		return null;
	}

	@Override
	public List<UmlAnalysis> createAnalyses(UmlModel2 model2)
	{
		// create the analysis to check which actions can be executed on a day
		model = model2;
		List<UmlAnalysis> anas = new ArrayList<>();
		List<String> next_actions = computePossibleActions(action_day, model);
		for (String act : next_actions)
		{
			Map<String, Integer> acts = new HashMap<>();
			acts.putAll(actions);
			acts.put(act, action_day);
			anas.add(createActionsAnalysis(act, acts));
		}
		// last analysis computes diagram of current actions
		anas.add(createActionsAnalysis("", actions));
		return anas;
	}

	@Override
	protected SmtModel createSMTCode(UmlModel2 model)
	{
		Legal2Constraints translator = new Legal2Constraints(this, job)
		{
			boolean isClaim = true;

			@Override
			protected void visitContract(Element ele)
			{
				if (ele != contractEle)
					return;
				super.visitContract(ele);
			}

			@Override
			protected void visitClaim(Element ele)
			{
				if (!!!claimEles.containsKey(ele) && !!!isClaim && !!!tmpClaimList.contains(ele))
					return;
				isClaim = true;
				super.visitClaim(ele);

				// todo: ensure that primary claims are encoded and do not occur

				// ensure that claim occurs
				if (claimEles.containsKey(ele))
				{
					int act_day = claimEles.get(ele);
					SmtConstraint as = smtModel.createAssert("claim_occurs", 10);
					UmlNode2 claimNode = new UmlNode2(model, ele);
					SmtElement conEvent = constraintClaimDate(claimNode);

					SmtConstraint occur = new SmtConstraint("=").addConstraint(conEvent)
							.addConstraint(new SmtConstraint("" + act_day));
					as.addConstraint(occur);
				}

				isClaim = false;
			}
		};
		SmtModel smt = translator.generate(model);
		return smt;
	}

	@Override
	public void runAnalysis(ReportResult report, String statisticsFile)
	{
		this.report = report;
		if (model == null)
		{
			job.logEventStatus(JobEvent.ERROR, "Contract model is missing.");
			return;
		}

		SmtModel smtModel = createSMTCode(model);
		if (smtModel == null)
			return;

		String code = smtModel.toText();
		if (code == null)
			return;

		ParseSmtResult res = runSmtAnalysis(model, code, null, smtModel);
		if (res != null)
		{
			if (res.isUnsatisfiable())
			{
				reportUnsat(name, "Contract not satisfiable", res.getUnsatCore(), UmlResultState.ERROR);
			} else
				reportRun(name, "Contract satisfiable", res.getDiagram(), UmlResultState.GOOD);
		}
		log(statisticsFile);
	}
}
