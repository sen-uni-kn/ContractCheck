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
 * Analyze whether claim is due before a dependent claim becomes due
 * 
 * @author Martin Koelbl
 */
public class UmlAnalysisContractClaimDependency extends UmlAnalysisContractAbstract
{
	public static final String Name = "ClaimDependency";

	public UmlAnalysisContractClaimDependency(Job j, String name)
	{
		super(j, name);
	}

	int nameCounter = 0;

	void checkClaimDependency(UmlModel2 model, UmlNode2 duty, UmlNode2 depClaim)
	{
		// get the due dates
		SmtElement dutDue = getClaimDateMin(model, duty, null);
		SmtElement depDue = getClaimDateMin(model, depClaim, null);
		// should be impossible that dependent claim is due before
		SmtConstraint greater = new SmtConstraint("<").addConstraint(dutDue).addConstraint(depDue);
		String extra = greater.toText();
		extra = "(assert (! " + extra + " :named a_duty))\n\n";

		String code = smtModel.toText(extra);
		if (code == null)
			return;
		// code = "(set-option :produce-unsat-cores true)\n" + code;
		// code += "(get-unsat-core)";

		String name = duty.getName() + "_" + depClaim.getName();
		if ((name == null) || name.isBlank())
			name = "_" + (++nameCounter);
		ParseSmtResult res = runSmtAnalysis(model, code, "_" + name, smtModel);
		if (res != null)
		{
			if (res.isSatisfiable())
			{
				String core = res.getDiagram();
				reportRun(name, "satisfiable", core, UmlResultState.ERROR);
			}

			if (res.isUnsatisfiable())
			{
				String core = res.getUnsatCore();
				reportUnsat(name, "unsatisfiable", core, UmlResultState.GOOD);
			}
		}
		log();
	}

	// first time model is encoded
	boolean first = true;
	List<List<Element>> anas = new ArrayList<>();

	// create analysis for every claim with a dependent claim
	void generateDependList(Element ele)
	{
		UmlNode2 claim = new UmlNode2(model, ele);
		// create analysis for every claim with a dependent claim
		for (UmlNode2 dep : claim.getAssoziationsByName(LegalUml.Depend))
		{
			// dependent element found
			List<Element> ana = new ArrayList<>();
			ana.add(claim.getElement());
			ana.add(dep.getElement());
			anas.add(ana);
		}
	}

	@Override
	public void visitClaim(Element ele)
	{
		if (first)
			generateDependList(ele);
		if (anas.isEmpty())
			return;
		List<Element> ana = anas.get(0);
		if (ana.contains(ele))
			super.visitClaim(ele);
	}

	void checkClaimDependencies(UmlModel2 model)
	{
		// iterate through dependency (!= consequence) analyses
		while (first || !!!anas.isEmpty())
		{
			// generate smt encoding
			SmtModel smtModel = createSMTCode(model);
			first = false;
			if (anas.isEmpty())
				return;
			List<Element> ana = anas.remove(0);
			if ((smtModel == null) || (ana == null))
				return;
			if (ana.size() != 2)
			{
				reportWarning("Error: dependency analysis has wrong number of claims");
				continue;
			}
			UmlNode2 c1 = new UmlNode2(model, ana.get(0));
			UmlNode2 c2 = new UmlNode2(model, ana.get(1));
			checkClaimDependency(model, c1, c2);
		}
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
	{
		this.report = report;
		checkClaimDependencies(model);
	}
}
