package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.Map;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;

public class UmlCombineConstraints
{
	Job job;

	public UmlCombineConstraints(Job j)
	{
	}

	public UmlAnalysis combine(UmlModel2 model2)
	{
		return null;
	}

	public SmtModel combine(UmlModel2 model, Map<Element, UmlAnnotation> map)
	{
		SmtModel smt = new SmtModel();
		for (Element e : map.keySet())
		{
			UmlAnnotation an = map.get(e);

			for (SmtDeclare dec : an.variables)
			{
				smt.addDeclaration(dec);
			}

			for (SmtConstraint con : an.constraints)
			{
				smt.addConstraint(con, 1);
			}
		}
		return smt;
	}
}
