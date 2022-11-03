package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;
import java.util.Set;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Searches the contract for syntactic errors
 *  
 * @author Martin Koelbl
 */
public class UmlAnalysisSyntax extends UmlAnalysisAbstract
{
	public static final String Name = "Syntax";

	public UmlAnalysisSyntax(Job j, String name)
	{
		super(j, name);
	}

	@Override
	public void runAnalysis(UmlModel2 model, ReportResult report)
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
			String name = node.getAttributeValue("Name");
			Set<UmlNode2> claims = getTriggerSet(nodes, node);
			if (claims.isEmpty() && !!!node.inheritatesFrom(LegalUml.Withdrawal)
					&& !!!node.inheritatesFrom(LegalUml.Supplementary)
					&& !!!node.inheritatesFrom(LegalUml.Compensation))
				reportError("" + name + " is missing a consequence claim!");

			//if ("ManagementApprove".equals(name))
			//	System.out.println("me");

			String val = getFrist(model, node);
			if (name == null)
				name = node.getName();
			if (val == null)
				reportError("" + name + " is missing a due date!");
		}

		// has every duty and claim a deadline?
		// nodes = model.getClassInstances(LegalUml.PrimaryClaim);
		// for (UmlNode2 node : nodes)
		// {
		// String name = node.getAttributeValue("Name");
		// List<UmlNode2> claims = node.getAssoziationsByName(LegalUml.Trigger);
		// if ((claims == null) || (claims.isEmpty()))
		// reportError("" + name + " is missing a consequence claim!");
		// String val = getFrist(node);
		// if (val == null)
		// reportError("" + name + " is missing a due date!");
		// }
		// nodes = model.getClassInstances(LegalUml.SecondaryClaim);
		// for (UmlNode2 node : nodes)
		// {
		// String name = node.getName();
		// String val = getFrist(node);
		// if (val == null)
		// reportError("" + name + " is missing a due date!");
		// }
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
	public String getStatisticFile()
	{
		return null;
	}

	@Override
	public void setStatisticFile(String file)
	{
	}
}
