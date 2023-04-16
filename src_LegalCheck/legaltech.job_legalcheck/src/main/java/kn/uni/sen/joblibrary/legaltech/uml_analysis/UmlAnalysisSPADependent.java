package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlSearchDependentClaims.DependentPair;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze that any contract claim c is only due when its depend claim is
 * satisfied.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class UmlAnalysisSPADependent extends UmlAnalysisSmtAbstract
{
	public static final String Name = "ClaimDependent";
	Element contractEle = null;
	Element claimEle = null;
	Element claimDepEle = null;

	public UmlAnalysisSPADependent(Job j, String anaName)
	{
		super(j, null, anaName, null);
	}

	public UmlAnalysisSPADependent(Job j, String name, String anaName, UmlModel2 model, Element con, Element claim,
			Element dep)
	{
		super(j, name, anaName, model);
		contractEle = con;
		claimEle = claim;
		claimDepEle = dep;
	}

	@Override
	public List<UmlAnalysis> createAnalyses(UmlModel2 model2)
	{
		List<UmlAnalysis> list = new ArrayList<>();
		List<Element> contracts = (new UmlSearchContracts(job)).searchContracts(model2);
		for (Element conEle : contracts)
		{
			List<DependentPair> claims = (new UmlSearchDependentClaims(job)).searchContractClaims(model2, conEle);
			for (DependentPair pair : claims)
			{
				String claimName = (new UmlNode2(model2, pair.claim)).getName();
				String depName = (new UmlNode2(model2, pair.dependent)).getName();
				String name = claimName + "_" + depName;
				list.add(new UmlAnalysisSPADependent(job, name, anaName, model2, conEle, pair.claim, pair.dependent));
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

				if (ele == claimEle)
				{
					SmtConstraint as = smtModel.createAssert("claim_dep_smaller", 10);
					UmlNode2 claimNode = new UmlNode2(model, claimEle);
					UmlNode2 depNode = new UmlNode2(model, claimDepEle);
					SmtElement dutDue = getClaimDueDate(claimNode);
					SmtElement depDue = getClaimDueDate(depNode);
					// should be impossible that dependent claim is due before
					SmtConstraint smaller = new SmtConstraint("<").addConstraint(dutDue).addConstraint(depDue);
					as.addConstraint(smaller);
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
				reportUnsat(name, "Dependent not satisfiable", res.getUnsatCore(), UmlResultState.GOOD);
			} else
				reportRun(name, "Dependent satisfiable", res.getDiagram(), UmlResultState.ERROR);
		}
		log(statisticsFile);
	}
}
