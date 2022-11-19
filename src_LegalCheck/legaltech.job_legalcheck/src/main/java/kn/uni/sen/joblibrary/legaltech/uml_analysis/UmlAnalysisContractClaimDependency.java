package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

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
		System.out.println(duty.getName());
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

	List<List<UmlNode2>> anas = null;
	List<UmlNode2> current_ana = null;

	// create analysis for every claim with a dependent claim
	void generateDependList(List<UmlNode2> duties)
	{
		anas = new ArrayList<List<UmlNode2>>();
		for (UmlNode2 duty : duties)
		{
			// create analysis for every claim with a dependent claim
			for (UmlNode2 dep : duty.getAssoziationsByName(LegalUml.Depend))
			{
				// search for dependent element in duties
				for (UmlNode2 node : duties)
				{
					if (node.getElement() == dep.getElement())
					{ // dependent element found
						List<UmlNode2> ana = new ArrayList<>();
						ana.add(duty);
						ana.add(node);
						anas.add(ana);
						break;
					}
				}
				// todo: dependent claims are not always
				System.out.println("Missing dependent element: " + dep.getName());
			}
		}
	}

	@Override
	protected List<UmlNode2> getDuties2Generate(List<UmlNode2> duties)
	{
		if (anas == null)
			generateDependList(duties);
		if (!!!anas.isEmpty())
			current_ana = anas.remove(0);
		return current_ana;
	}

	void checkClaimDependencies(UmlModel2 model)
	{
		// iterate through dependency (!= consequence) analyses
		while ((anas == null) || !!!anas.isEmpty())
		{
			current_ana = null;
			// generate smt encoding
			SmtModel smtModel = createSMTCode(model);
			if ((smtModel == null) || (current_ana == null))
				return;
			if (current_ana.size() != 2)
			{
				reportWarning("Error: dependency analysis has wrong number of claims");
				continue;
			}
			checkClaimDependency(model, current_ana.get(0), current_ana.get(1));
		}
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
	{
		this.report = report;
		checkClaimDependencies(model);
	}
}
