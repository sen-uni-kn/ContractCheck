package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractParser;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.ReportResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysis;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisContractDuties;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisContractLimitation;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisContractMinMax;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisContractPriceChangeTime;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSyntax;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResult;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceDouble;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;

public class Job_LegalCheck extends JobAbstract implements ReportResult
{
	public static final String CONTRACT_FILE = "Contract";
	public static final String XSD_FILE = "XSDFile";
	public static final String VALUES = "VariableWerte";
	public static final String ANALYSEN = "Analyse";

	public static final String RESULT = "Result";
	public static final String SEQUENCE = "Sequence";
	public static final String MINMAX = "MinMax";
	public static final String RESULT_KIND = "Kind";
	public static final String UNSAT_CORE = "UnsatCore";

	ResourceString ResultNext = null;

	public Job_LegalCheck(RunContext parent)
	{
		super(parent);
		createInputDescr(CONTRACT_FILE, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(XSD_FILE, ResourceType.FILE);
		createInputDescr(ANALYSEN, ResourceType.STRING);
		createInputDescr(VALUES, ResourceType.DOUBLE);

		createResultDescr(RESULT, ResourceType.STRING);
	}

	public UmlModel2 parseUmlModel(ResourceFile resFile, ResourceFile xsd)
	{
		if (resFile == null)
			return null;

		InputStream xmiStream = resFile.getInputStream();
		if (xmiStream == null)
			return null;

		if (".xmi".equals(resFile.getExtension()))
		{
			return null; // (new UmlParser(this)).parseFile(xmiStream);
		} // if ("json".equals(resFile.getExtension()))
		Contract contract = (new ContractParser(this)).parseFile(resFile.getData());
		return (new Contract2Uml2(this, xsd)).convert(contract);
	}

	public JobState task()
	{
		ResourceFile res = getResourceWithType(CONTRACT_FILE, false);
		if (res == null)
			return endError("Missing input file");
		ResourceFile xsd = getResourceWithType(XSD_FILE, false);
		UmlModel2 model2 = parseUmlModel(res, xsd);
		if (model2 == null)
			return endError("Error with parsing of contract file!");
		if (model2.getClassInstances(LegalUml.SPA).isEmpty())
			return endError("Error Contract instance is missing!");

		ResourceDouble resV = getResourceWithType(VALUES, false);

		ResourceString resA = getResourceWithType(ANALYSEN, false);
		List<UmlAnalysis> anas = getAnalysen(resA, resV);

		// create different analyses
		String file = null;
		for (UmlAnalysis ana : anas)
		{
			ana.setStatisticFile(file);
			ana.runAnalysis(model2, this);
			file = ana.getStatisticFile();
		}

		return end(JobResult.OK);
	}

	private List<UmlAnalysis> getAnalysen(ResourceString resA, ResourceDouble resV)
	{
		List<UmlAnalysis> anas = new ArrayList<>();
		if (resA == null)
		{
			resA = new ResourceString(UmlAnalysisSyntax.Name);
			resA.addNext(new ResourceString(UmlAnalysisContractDuties.Name));
			resA.addNext(new ResourceString(UmlAnalysisContractPriceChangeTime.Name));
			resA.addNext(new ResourceString(UmlAnalysisContractMinMax.Name));
			resA.addNext(new ResourceString(UmlAnalysisContractLimitation.Name));
		}
		while (resA != null)
		{
			String val = resA.getData();
			if (val == null)
				continue;
			if (val.equals(UmlAnalysisSyntax.Name))
				anas.add(new UmlAnalysisSyntax(this, val));
			if (val.equals(UmlAnalysisContractDuties.Name))
				anas.add(new UmlAnalysisContractDuties(this, val));
			if (val.equals(UmlAnalysisContractPriceChangeTime.Name))
				anas.add(new UmlAnalysisContractPriceChangeTime(this, val));
			if (val.equals(UmlAnalysisContractMinMax.Name))
				anas.add(new UmlAnalysisContractMinMax(this, val, resV));
			if (val.equals(UmlAnalysisContractLimitation.Name))
				anas.add(new UmlAnalysisContractLimitation(this, val));
			resA = resA.getNextByType();
		}
		return anas;
	}

	private ResourceString addResult(UmlAnalysis ana, UmlResult result)
	{
		String name = RESULT + "_" + result.anaName;
		if (result.name != null)
			name += "_" + result.name;
		ResourceString res = new ResourceString(name);
		res.setData(name);

		ResourceEnum en = new ResourceEnum(name);
		en.setName(RESULT_KIND);
		en.setData(result.rest.name());
		res.addChild(en);

		if (result.diagram != null)
		{
			ResourceString res2 = new ResourceString(name);
			res2.setName(SEQUENCE);
			res2.setData(result.diagram);
			res.addChild(res2);
		}

		if (result.core != null)
		{
			ResourceString res2 = new ResourceString(name);
			res2.setName(UNSAT_CORE);
			res2.setData(result.core);
			res.addChild(res2);
		}

		if (result.text != null)
		{
			ResourceString res2 = new ResourceString(name);
			res2.setName("Text");
			res2.setData(result.text);
			res.addChild(res2);
		}

		if (result.minMax != null)
		{
			ResourceString res2 = new ResourceString(name);
			res2.setName(MINMAX);
			res2.setData(result.minMax);
			res.addChild(res2);
		}

		if (ResultNext == null)
			ResultNext = res;
		else
			ResultNext.addNext(res);
		return res;
	}

	@Override
	public ResourceInterface getResultResource(String name)
	{
		if (name == null)
			return null;
		if (RESULT.equals(name))
			return ResultNext;
		return null;
	}

	@Override
	public void reportResult(UmlAnalysis ana, UmlResult err)
	{
		if ((err == null) || (err.text == null))
			return;

		addResult(ana, err);
	}
}
