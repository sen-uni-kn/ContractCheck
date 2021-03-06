package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.resource.ResourceDouble;

public class UmlAnalysisContractPriceChangeTime extends UmlAnalysisContractAbstract
{
	public static final String Name = "Timing";

	public UmlAnalysisContractPriceChangeTime(Job j, String name)
	{
		super(j, name);
	}

	// show date of pay in diagram
	Date datePay = null;

	protected SmtConstraint getClaimLong(UmlModel2 model, UmlNode2 claim, UmlNode2 zahlung)
	{
		datePay = null;
		if (zahlung == null)
			return null;
		SmtElement decl2 = listDutyClaim.get(zahlung.getElement());
		String frist = zahlung.getAttributeValue(LegalUml.DueDate);

		if (frist != null)
		{
			String val = ResourceDouble.checkStringDouble(frist);
			if (val != null)
			{
				decl2 = new SmtConstraint(val);
				datePay = new Date("Date_" + zahlung.getName(), val);
			}
		}

		SmtDeclare decl = listDutyClaim.get(claim.getElement());

		if ((decl == null) || (decl2 == null))
			return null;
		return new SmtConstraint(">").addConstraint(decl).addConstraint(decl2);
	}

	public void checkDutiesTiming(UmlModel2 model)
	{
		for (dutyCount = 0; dutyCount == 0 || duty != null; dutyCount++)
		{
			duty = null;
			SmtModel smtModel = createSMTCode(model);
			if ((smtModel == null) || (duty == null))
				return;
			// SmtDeclare con = listDutyClaim.get(duty);

			List<UmlNode2> claims = duty.getAssoziationsByName(LegalUml.Trigger);
			for (UmlNode2 claim : claims)
			{
				if (!!!claim.inheritatesFrom(LegalUml.Compensation))
					continue;

				UmlNode2 payNode = getPayNode(model, claim);

				smtModel = createSMTCode(model);
				SmtConstraint extraCon = getClaimLong(model, claim, payNode);
				if (extraCon == null)
					continue;
				String extra = extraCon.toText();
				extra = "(assert (! " + extra + " :named a_duty))\n\n";

				String code = smtModel.toText(extra);
				if (code == null)
					return;

				String name = claim.getName();
				if ((name == null) || name.isBlank())
					name = "_" + (dutyCount + 1);
				ParseSmtResult res = runSmtAnalysis(model, code, "_" + name, smtModel);
				if (res != null)
				{
					name = claim.getNodeAttributeName();
					String name2 = payNode.getNodeAttributeName();
					String diagram = res.getDiagram(datePay);
					if (res.sat)
						reportRun(name, "" + name + " geschieht nach " + name2 + "!", diagram, UmlResultState.WARNING);
				}
				log();
			}
		}
	}

	/** returns duty that transfers the thing cl */
	private UmlNode2 getPflichtUebergabe(UmlModel2 model, UmlNode2 cl)
	{
		List<UmlNode2> pflichtList = model.getClassInstances(LegalUml.Claim);
		for (UmlNode2 pf : pflichtList)
		{
			List<UmlNode2> asL = pf.getAssoziationsByName(LegalUml.Performance);
			for (UmlNode2 n : asL)
			{
				List<UmlNode2> asL2 = n.getAssoziationsByName(LegalUml.Property);
				for (UmlNode2 n2 : asL2)
					if (n2 == cl)
						return pf;
			}
		}
		return null;
	}

	private UmlNode2 getPayNode(UmlModel2 model, UmlNode2 cl)
	{
		List<UmlNode2> asL = cl.getAssoziationsByName(LegalUml.Price);
		if ((asL == null) || asL.isEmpty())
			return null;

		UmlNode2 preis = asL.get(0);
		return getPflichtUebergabe(model, preis);
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
	{
		this.report = report;
		checkDutiesTiming(model);
	}
}
