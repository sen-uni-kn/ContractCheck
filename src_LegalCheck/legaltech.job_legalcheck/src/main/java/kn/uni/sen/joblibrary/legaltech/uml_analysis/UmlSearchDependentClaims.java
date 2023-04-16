package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.List;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitor;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.jobscheduler.common.model.Job;

/**
 * Search every claim that depends on another claim in a contract model.
 * 
 * @author Martin Koelbl (C) 2023
 */
public class UmlSearchDependentClaims extends LegalVisitor
{
	class DependentPair
	{
		public Element claim;
		public Element dependent;
	}

	List<DependentPair> claims;
	Element contract = null;

	public UmlSearchDependentClaims(Job job)
	{
		super(job);
	}

	@Override
	protected void visitClaim(Element ele)
	{
		if (ele == null)
			return;
		UmlNode2 node = new UmlNode2(model, ele);
		for (UmlNode2 dep : node.getAssoziationsByName(LegalUml.Depend))
		{
			DependentPair pair = new DependentPair();
			pair.claim = ele;
			pair.dependent = dep.getElement();
			claims.add(pair);
		}
	}

	@Override
	protected void visitContract(Element ele)
	{
		if (ele != contract)
			return;
		super.visitContract(ele);
	}

	List<DependentPair> searchContractClaims(UmlModel2 model, Element contract)
	{
		claims = new ArrayList<>();
		this.contract = contract;
		visitModel(model);
		return claims;
	}
}
