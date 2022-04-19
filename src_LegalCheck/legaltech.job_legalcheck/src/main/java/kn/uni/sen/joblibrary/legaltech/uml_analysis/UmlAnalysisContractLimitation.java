package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;
import java.util.Set;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

public class UmlAnalysisContractLimitation extends UmlAnalysisContractAbstract
{
	public static final String Name = "Limitation";

	public UmlAnalysisContractLimitation(Job j, String name)
	{
		super(j, name);
	}

	// show date of pay in diagram
	//Date dateLimit = null;

	protected SmtConstraint getClaimAfter(UmlModel2 model, UmlNode2 duty, UmlNode2 trig, String limit)
	{
		//dateLimit = null;
		if (trig == null)
			return null;
		SmtElement decl = listDutyClaim.get(trig.getElement());

		SmtDeclare con = listDutyClaim.get(duty.getElement());
		SmtConstraint dutyCon = getDutyConstraint(model, duty, con);
		SmtConstraint not = new SmtConstraint("not").addConstraint(dutyCon);
		SmtConstraint and = new SmtConstraint("and").addConstraint(not);

		if ((decl == null) || (limit == null))
			return null;
		SmtConstraint limitCon = new SmtConstraint(limit);
		SmtConstraint smaller = new SmtConstraint("<").addConstraint(limitCon).addConstraint(decl);
		return and.addConstraint(smaller);
	}

	public void checkDutiesTiming(UmlModel2 model)
	{
		List<UmlNode2> claims = model.getClassInstances(LegalUml.Claim);
		for (dutyCount = 0; dutyCount == 0 || duty != null; dutyCount++)
		{
			duty = null;
			SmtModel smtModel = createSMTCode(model);
			if ((smtModel == null) || (duty == null))
				return;
			// SmtDeclare con = listDutyClaim.get(duty);
			String val = duty.getAttributeValue(LegalUml.Limitation);
			if ((val == null) || val.isEmpty())
				continue;
			
			Date dateLimit = new Date("Date_Limitation", val);

			Set<UmlNode2> triggers = getTriggerSet(claims, duty);
			for (UmlNode2 trig : triggers)
			{
				smtModel = createSMTCode(model);
				SmtConstraint extraCon = getClaimAfter(model, duty, trig, val);
				if (extraCon == null)
					continue;
				String extra = extraCon.toText();
				extra = "(assert (! " + extra + " :named a_time))\n\n";

				String code = smtModel.toText(extra);
				if (code == null)
					return;

				String name = trig.getName();
				if ((name == null) || name.isBlank())
					name = "_" + (dutyCount + 1);
				ParseSmtResult res = runSmtAnalysis(model, code, "_" + name, smtModel);
				if (res != null)
				{
					name = trig.getNodeAttributeName();
					String name2 = duty.getNodeAttributeName();
					String diagram = res.getDiagram(dateLimit);
					if (res.sat)
						reportRun(name, "" + name + " can occur after limitation of " + name2 + "!", diagram,
								UmlResultState.WARNING);
				}
				log();
			}
		}
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
	{
		this.report = report;
		checkDutiesTiming(model);
	}
}
