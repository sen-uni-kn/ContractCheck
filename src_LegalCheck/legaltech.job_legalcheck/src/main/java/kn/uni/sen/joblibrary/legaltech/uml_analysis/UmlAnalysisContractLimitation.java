package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze whether an execution exists where the limitation of a claim occurs
 * before the claim becomes due
 * 
 * @author Martin Koelbl
 */
public class UmlAnalysisContractLimitation extends UmlAnalysisContractAbstract
{
	public static final String Name = "Limitation";

	public UmlAnalysisContractLimitation(Job j, String name)
	{
		super(j, name);
	}

	// show date of pay in diagram
	// Date dateLimit = null;

	protected boolean getClaimAfter(UmlModel2 model, UmlNode2 duty, UmlNode2 trig, String limitT, SmtModel smtModel)
	{
		// dateLimit = null;
		if (trig == null)
			return false;
		SmtElement decl = listDutyClaim.get(trig.getElement());

		SmtDeclare con = listDutyClaim.get(duty.getElement());
		SmtElement conDue = getClaimDateMin(model, trig, duty);
		SmtConstraint dutyCon = getDutyConstraint(model, duty, con);
		SmtConstraint not = new SmtConstraint("not").addConstraint(dutyCon);
		SmtConstraint and = new SmtConstraint("and").addConstraint(not);

		if ((decl == null) || (limitT == null))
			return false;
		SmtConstraint limitCon = new SmtConstraint(limitT);

		SmtDeclare limit = new SmtDeclare("const", "clLimit", "Int");
		SmtDeclare due = new SmtDeclare("const", "clDue", "Int");
		smtModel.addDeclaration(limit);
		smtModel.addDeclaration(due);

		SmtConstraint lim = new SmtConstraint("=");
		lim.addConstraint(limit);
		lim.addConstraint(limitCon);
		and.addConstraint(lim);

		SmtConstraint du = new SmtConstraint("=");
		du.addConstraint(due);
		du.addConstraint(conDue);
		and.addConstraint(du);

		SmtConstraint sm = new SmtConstraint("<");
		sm.addConstraint(limit);
		sm.addConstraint(due);
		and.addConstraint(sm);
		// SmtConstraint and = new SmtConstraint("and");

		SmtConstraint ass = smtModel.createAssert("LimitCheck", 9);
		ass.addConstraint(and);
		return true;
		// SmtConstraint smaller = new
		// SmtConstraint("<").addConstraint(limitCon).addConstraint(decl);
		// return and.addConstraint(smaller);
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

	public void checkDutiesTiming(UmlModel2 model)
	{
		List<UmlNode2> claims = model.getClassInstances(LegalUml.Claim);
		for (claimCounter = 0; claimCounter == 0 || duty != null; claimCounter++)
		{
			duty = null;
			SmtModel smtModel = createSMTCode(model);
			if ((smtModel == null) || (duty == null))
				return;
			// SmtDeclare con = listDutyClaim.get(duty);

			Set<UmlNode2> triggers = getTriggerSet(claims, duty);
			triggers.add(duty);
			for (UmlNode2 trig : triggers)
			{
				// UmlNode2 trig = duty;
				trigLimit = trig;
				smtModel = createSMTCode(model);

				// String val = trig.getAttributeValue(LegalUml.Limitation);
				SmtElement min = getClaimDateMin(model, trig, duty);
				String val = getLimitation(model, trig, min);
				if ((val == null) || val.isEmpty())
					continue;

				if (!!!getClaimAfter(model, duty, trig, val, smtModel))
					continue;
				// String extra = extraCon.toText();
				// extra = "(assert (! " + extra + " :named a_time))\n\n";

				String code = smtModel.toText();
				if (code == null)
					return;

				String name = trig.getName();
				if ((name == null) || name.isBlank())
					name = "_" + (claimCounter + 1);
				ParseSmtResult res = runSmtAnalysis(model, code, "_" + name, smtModel);
				if (res != null && res.sat)
				{
					name = trig.getNodeAttributeName();
					String nameCon = trig.getName();
					// String name2 = duty.getNodeAttributeName();
					Float limVal = res.getValue("clLimit");
					Float dueVal = res.getValue("clDue");
					Date dateLimit = new Date("Date_" + nameCon + ".Limitation", "" + limVal);
					Date dateDue = new Date("Date_" + nameCon + ".DueDate", "" + dueVal);
					List<Date> list = new ArrayList<>();
					list.add(dateLimit);
					list.add(dateDue);
					String diagram = res.getDiagram(list);
					reportRun(name, "" + name + " can occur after limitation of " + name + "!", diagram,
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
