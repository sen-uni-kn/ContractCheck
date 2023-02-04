package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitorAbstract;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Search all claims in a contract.
 *  
 * @author Martin Koelbl (C) 2023
 */
public class UmlAnalysisSearchClaims  extends LegalVisitorAbstract
{
	List<Element> claims;
	
	public UmlAnalysisSearchClaims(Job job)
	{
		super(job);
	}

	@Override
	protected void visitClaim(Element ele)
	{
		if(ele==null)
			return;
		claims.add(ele);
	}
	
	List<Element> searchClaims(UmlModel2 model)
	{
		claims = new ArrayList<>();
		traverse(model);
		return claims;
	}
}
