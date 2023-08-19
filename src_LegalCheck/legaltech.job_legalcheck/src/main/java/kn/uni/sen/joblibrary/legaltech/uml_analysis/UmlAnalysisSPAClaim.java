package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze whether every contract claim is satisfiable.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class UmlAnalysisSPAClaim extends UmlAnalysisSmtAbstract
{
	public static final String Name = "SPAClaim";
	Element contractEle = null;
	Element claimEle = null;

	public UmlAnalysisSPAClaim(Job j, String anaName)
	{
		super(j, null, anaName, null);
	}

	public UmlAnalysisSPAClaim(Job j, String name, String anaName, UmlModel2 model, Element con, Element claim)
	{
		super(j, name, anaName, model);
		contractEle = con;
		claimEle = claim;
	}

	@Override
	public List<UmlAnalysis> createAnalyses(UmlModel2 model2)
	{
		List<UmlAnalysis> list = new ArrayList<>();
		List<Element> contracts = (new UmlSearchContracts(job)).searchContracts(model2);
		for (Element conEle : contracts)
		{
			List<Element> claims = (new UmlSearchClaims(job)).searchContractClaims(model2, conEle);
			for (Element claimEle : claims)
			{
				String conName = (new UmlNode2(model2, conEle)).getName();
				String claimName = (new UmlNode2(model2, claimEle)).getName();
				String name = conName + "_" + claimName;
				list.add(new UmlAnalysisSPAClaim(job, name, anaName, model2, conEle, claimEle));
			}
		}
		return list;
	}

	@Override
	SmtModel createSMTCode(UmlModel2 model)
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
				if ((ele != claimEle) && !!!isClaim && !!!tmpClaimList.contains(ele))
					return;
				isClaim = true;
				super.visitClaim(ele);

				// todo: ensure that primary claims are encoded and do not occur

				if (ele == claimEle)
				{
					SmtConstraint as = smtModel.createAssert("claim_occurs", 10);
					UmlNode2 claimNode = new UmlNode2(model, ele);
					SmtElement conEvent = constraintClaimDate(claimNode);
					SmtConstraint claimOccurs = getClaimOccursConstraint(claimNode, conEvent);
					as.addConstraint(claimOccurs);
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
				result = 0;
				reportUnsat(name, "Claim not satisfiable", res.getUnsatCore(), UmlResultState.ERROR);
			} else {
				result = 1;
				reportRun(name, "Claim satisfiable", res.getDiagram(), UmlResultState.GOOD);
			}
		}
		log(statisticsFile);
	}
}
