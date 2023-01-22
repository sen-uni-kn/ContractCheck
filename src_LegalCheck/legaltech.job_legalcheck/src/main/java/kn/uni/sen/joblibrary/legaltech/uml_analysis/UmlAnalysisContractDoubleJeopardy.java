package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze whether one short-coming of a contract party leads to several
 * punishments.
 * 
 * @author Martin Koelbl
 */
public class UmlAnalysisContractDoubleJeopardy extends UmlAnalysisContractAbstract
{
	public static final String Name = "DoubleJeopardy";

	public UmlAnalysisContractDoubleJeopardy(Job j, String name)
	{
		super(j, name);
	}

	void checkTriggers(UmlModel2 model, String name, SmtModel smtModel)
	{
		List<UmlNode2> claims = model.getClassInstances(LegalUml.Claim);
		Set<UmlNode2> triggers = getTriggerSet(claims, duty);
		// int trigCount = 0;
		SmtConstraint or = new SmtConstraint("or");
		if ((triggers == null) || (triggers.size() <= 1))
			return;

		Set<SmtConstraint> set = new HashSet<>();

		// several triggers occur
		for (UmlNode2 trigger : triggers)
		{
			// trigCount++;

			SmtDeclare conTrig = listDutyClaim.get(trigger.getElement());
			SmtConstraint trigCon = getDutyConstraint(model, trigger, conTrig);

			for (SmtConstraint con : set)
			{
				SmtConstraint and = new SmtConstraint("and");
				and.addConstraint(trigCon);
				and.addConstraint(con);
				or.addConstraint(and);
			}
			set.add(trigCon);
		}

		// not the main claim
		SmtDeclare con = listDutyClaim.get(duty.getElement());
		SmtConstraint dutyCon = getDutyConstraint(model, duty, con);
		SmtConstraint not = new SmtConstraint("not").addConstraint(dutyCon);

		String extra = "(assert (! " + not.toText() + " :named a_duty))\n";
		extra += "(assert (! " + or.toText() + " :named a_triggers))\n\n";

		String code = smtModel.toText(extra);
		if (code == null)
			return;

		// get trigger name
		String name2 = name + "_triggers";
		ParseSmtResult res = runSmtAnalysis(model, code, "_" + name2, smtModel);
		if (res != null)
		{
			if (res.isSatisfiable())
			{
				String core = res.getDiagram();
				reportRun(name2, "double jeopardy satisfiable", core, UmlResultState.ERROR);
				log(false);
			}

			if (res.isUnsatisfiable())
			{
				reportUnsat(name2, "unsatisfiable", null, UmlResultState.GOOD);
				log(true);
			}
		}
	}

	// hack: needed to specify the duties to generate
	// counts index of duty to generate
	int claimCounter = -1;
	int claimIdx = 0;
	// stores duty to generate
	UmlNode2 duty = null;

	@Override
	public void visitClaim(Element ele)
	{
		if ((claimCounter == -1) || (claimIdx == claimCounter))
		{
			super.visitClaim(ele);
			duty = new UmlNode2(model, ele);
		}
		claimIdx++;
	}

	void checkDutiesDoubleJeopardy(UmlModel2 model)
	{
		// for every primary claim and independent claim create code
		for (claimCounter = 0; claimCounter == 0 || duty != null; claimCounter++)
		{
			duty = null;
			SmtModel smtModel = createSMTCode(model);
			if ((smtModel == null) || (duty == null))
				return;
			SmtDeclare con = listDutyClaim.get(duty.getElement());
			String extra = getDutyConstraint(model, duty, con).toText();
			extra = "(assert (! " + extra + " :named a_duty))\n\n";

			String code = smtModel.toText(extra);
			if (code == null)
				return;
			// code = "(set-option :produce-unsat-cores true)\n" + code;
			// code += "(get-unsat-core)";

			String name = duty.getName();
			// if ((name == null) || name.isBlank())
			// name = "_" + (dutyCount + 1);

			checkTriggers(model, name, smtModel);
		}
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
	{
		this.report = report;
		checkDutiesDoubleJeopardy(model);
	}
}
