package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;
import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitor;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Search all contracts in a contract model.
 * 
 * @author Martin Koelbl (C) 2023
 */
public class UmlAnalysisSearchContracts extends LegalVisitor
{
	List<Element> contracts;

	public UmlAnalysisSearchContracts(Job job)
	{
		super(job);
	}

	@Override
	protected void visitContract(Element ele)
	{
		if (ele == null)
			return;
		contracts.add(ele);
	}

	List<Element> searchContracts(UmlModel2 model)
	{
		contracts = new ArrayList<>();
		visitModel(model);
		return contracts;
	}
}
