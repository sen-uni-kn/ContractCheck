package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze whether the limitation of a claim can occur before it is due.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class UmlAnalysisSPAClaimLimit extends UmlAnalysisSmtAbstract
{
	public static final String Name = "SPAClaimLimit";
	Element contractEle = null;
	Element claimEle = null;

	public UmlAnalysisSPAClaimLimit(Job j, String anaName)
	{
		super(j, null, anaName, null);
	}

	public UmlAnalysisSPAClaimLimit(Job j, String name, String anaName, UmlModel2 model, Element con, Element claim)
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

				UmlNode2 claim = new UmlNode2(model2, claimEle);
				UmlNode2 limit = claim.getAssoziationByName(LegalUml.Limitation);
				if (limit == null)
					continue;
				list.add(new UmlAnalysisSPAClaimLimit(job, name, anaName, model2, conEle, claimEle));
			}
		}
		return list;
	}

	@Override
	SmtModel createSMTCode(UmlModel2 model)
	{
		Legal2Constraints translator = new Legal2Constraints(this, job)
		{
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
				if (ele != claimEle)
				{
					super.visitClaim(ele);
					return;
				}
				limit_check = true;
				super.visitClaim(ele);

				SmtConstraint as = smtModel.createAssert("limit_check", 10);
				SmtConstraint and = new SmtConstraint("and");
				as.addConstraint(and);

				// limit analysis checks whether limitation < due
				UmlNode2 claim = createNode(ele);
				SmtElement dueDate = getClaimDueDate(claim);
				SmtElement triggerDate = getTriggerDate(claim);
				SmtElement limit = getClaimLimitation(claim, triggerDate, dueDate);
				and.addConstraint(new SmtConstraint("<").addConstraint(limit).addConstraint(dueDate));

				// ensure claim occurs
				UmlNode2 claimNode = new UmlNode2(model, ele);
				SmtElement conEvent = constraintClaimDate(claimNode);
				SmtConstraint claimOccurs = getClaimOccursConstraint(claimNode, conEvent);
				and.addConstraint(claimOccurs);
				limit_check = false;
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
				reportRun(name, "Claim limitation after due", res.getDiagram(), UmlResultState.GOOD);
			} else
				reportUnsat(name, "Claim limitation before due", res.getUnsatCore(), UmlResultState.ERROR);
		}
		log(statisticsFile);
	}
}
