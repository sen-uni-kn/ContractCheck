package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;
import java.util.Set;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

public class UmlAnalysisContractDuties extends UmlAnalysisContractAbstract
{
	public static final String Name = "Sat";

	public UmlAnalysisContractDuties(Job j, String name)
	{
		super(j, name);
	}

	public void checkContractSatisfiable(UmlModel2 model)
	{
		SmtModel smtModel = createSMTCode(model);
		if (smtModel == null)
			return;

		String code = smtModel.toText();
		if (code == null)
			return;

		ParseSmtResult res = runSmtAnalysis(model, code, "_SPA", smtModel);
		if (res != null)
		{
			if (res.isUnsatisfiable())
			{
				reportUnsat("Contract", "Contract not satisfiable", res.getUnsatCore(), UmlResultState.ERROR);
			} else
				reportRun("Contract", "Contract satisfiable", res.getDiagram(), UmlResultState.GOOD);
		}
		log();
	}

	public void checkTriggers(UmlModel2 model, String name, SmtModel smtModel)
	{
		List<UmlNode2> claims = model.getClassInstances(LegalUml.Claim);
		Set<UmlNode2> triggers = getTriggerSet(claims, duty);
		int trigCount = 0;
		for (UmlNode2 trigger : triggers)
		{
			trigCount++;

			SmtDeclare con = listDutyClaim.get(duty.getElement());
			SmtConstraint dutyCon = getDutyConstraint(model, duty, con);

			SmtDeclare conTrig = listDutyClaim.get(trigger.getElement());
			SmtConstraint trigCon = getDutyConstraint(model, trigger, conTrig);

			SmtConstraint not = new SmtConstraint("not").addConstraint(dutyCon);
			SmtConstraint and = new SmtConstraint("and").addConstraint(not);
			and.addConstraint(trigCon);
			String extra = and.toText();
			extra = "(assert (! " + extra + " :named a_duty))\n\n";

			String code = smtModel.toText(extra);
			if (code == null)
				return;

			// get trigger name
			String name2 = trigger.getName();
			if ((name2 == null) || name2.isEmpty())
				name2 = "" + trigCount;
			ParseSmtResult res = runSmtAnalysis(model, code, "_" + name + "_" + name2, smtModel);
			log();
			if (res != null)
			{
				if (res.isSatisfiable())
				{
					String core = res.getDiagram();
					reportRun(name2, "satisfiable", core, UmlResultState.GOOD);
				}

				if (res.isUnsatisfiable())
				{
					String core = res.getUnsatCore();
					reportUnsat(name2, "unsatisfiable", core, UmlResultState.ERROR);
				}
			}
		}
	}

	public void checkClaimsSatisfiable(UmlModel2 model)
	{
		// for every primary claim and independent claim create code
		for (dutyCount = 0; dutyCount == 0 || duty != null; dutyCount++)
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

			String name = duty.getName();
			if ((name == null) || name.isBlank())
				name = "_" + (dutyCount + 1);
			ParseSmtResult res = runSmtAnalysis(model, code, "_" + name, smtModel);
			if (res != null)
			{
				if (res.isSatisfiable())
				{
					String core = res.getDiagram();
					reportRun(name, "satisfiable", core, UmlResultState.GOOD);
				}

				if (res.isUnsatisfiable())
				{
					String core = res.getUnsatCore();
					reportUnsat(name, "unsatisfiable", core, UmlResultState.ERROR);
				}
			}
			log();
			checkTriggers(model, name, smtModel);
		}
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
	{
		this.report = report;
		checkContractSatisfiable(model);
		checkClaimsSatisfiable(model);
	}
}
