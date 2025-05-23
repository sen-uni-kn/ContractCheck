package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Analyze the contract is satisfiable for at least one contract execution.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class UmlAnalysisSyntax extends UmlAnalysisAbstract implements UmlAnalysis, UmlAnalysisFactory
{
	public static final String Name = "Syntax";
	UmlModel2 model;

	// factory constructor generates analysis
	public UmlAnalysisSyntax(Job job, String name)
	{
		super(job, name);
	}

	// analysis constructors can run analysis
	public UmlAnalysisSyntax(Job job, String name, UmlModel2 model)
	{
		super(job, name);
		this.model = model;
	}

	@Override
	public List<UmlAnalysis> createAnalyses(UmlModel2 model2)
	{
		List<UmlAnalysis> list = new ArrayList<>();
		list.add(new UmlAnalysisSyntax(job, anaName, model2));
		return list;
	}

	public boolean existsDueDateFormula(UmlModel2 model, UmlNode2 duty)
	{
		UmlNode2 formula = duty.getAssoziationByName(LegalUml.DueDate);
		if (formula != null)
		{
			String opVal = formula.getAttributeValue(LegalUml.Operator);
			if (!opVal.isBlank())
				return true;
		}
		return false;
	}

	public String getFrist(UmlModel2 model, UmlNode2 duty)
	{
		if (duty == null)
			return null;
		String val = duty.getAttributeValue(LegalUml.DueDate);
		if (val != null)
		{
			if ((val.startsWith("+")) || (val.startsWith("(")))
				return val;
			try
			{
				Float.parseFloat(val);
				return val;
			} catch (Exception e)
			{
				reportWarning("" + val + " is not a number!");
			}
		}
		return null;
	}

	@Override
	public void runAnalysis(ReportResult report, String statisticsFile)
	{
		this.report = report;

		// is there a contract element
		List<UmlNode2> list = model.getClassInstances(LegalUml.SPA);
		if (list.size() == 0)
		{
			reportError("Missing a contract");
			return;
		} else if (list.size() > 1)
		{
			reportWarning("Several contracts are found.");
		}

		// is there a seller element
		UmlNode2 contract = list.get(0);
		List<UmlNode2> nodes = contract.getAssoziationsByName(LegalUml.Seller);
		if (nodes.isEmpty())
		{
			reportError("Missing " + LegalUml.Seller);
			// return;
		}

		// is there a buyer element
		nodes = contract.getAssoziationsByName(LegalUml.Purchaser);
		if (nodes.isEmpty())
		{
			reportError("Missing " + LegalUml.Purchaser);
			// return;
		}

		nodes = model.getClassInstances(LegalUml.Claim);
		for (UmlNode2 node : nodes)
		{
			String name = node.getAttributeValue(LegalUml.Name);
			Set<UmlNode2> claims = getTriggerSet(nodes, node);
			if (claims.isEmpty() && !!!node.inheritatesFrom(LegalUml.Withdrawal)
					&& !!!node.inheritatesFrom(LegalUml.Supplementary)
					&& !!!node.inheritatesFrom(LegalUml.Compensation))
				reportError("" + name + " is missing a consequence claim!");

			// if ("ManagementApprove".equals(name))
			// System.out.println("me");

			String val = getFrist(model, node);
			if ((val == null) && existsDueDateFormula(model, node))
				continue;
			if (name == null)
				name = node.getName();
			if (val == null)
				reportError("" + name + " is missing a due date!");
		}
	}
}
