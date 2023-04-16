package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitor;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Search all claims in a contract model.
 * 
 * @author Martin Koelbl (C) 2023
 */
public class UmlSearchClaims extends LegalVisitor
{
	List<Element> claims;
	Element contract = null;

	public UmlSearchClaims(Job job)
	{
		super(job);
	}

	@Override
	protected void visitClaim(Element ele)
	{
		if (ele == null)
			return;
		claims.add(ele);
	}

	@Override
	protected void visitContract(Element ele)
	{
		if (ele != contract)
			return;
		super.visitContract(ele);
	}

	List<Element> searchContractClaims(UmlModel2 model, Element contract)
	{
		claims = new ArrayList<>();
		this.contract = contract;
		visitModel(model);
		return claims;
	}
}
