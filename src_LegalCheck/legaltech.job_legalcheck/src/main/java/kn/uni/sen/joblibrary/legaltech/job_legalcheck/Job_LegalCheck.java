package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractParser;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.ReportResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysis;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisExecutor;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisFactory;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPA;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPAClaim;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPAClaimUnsat;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPADependent;
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

/**
 * job that analyzes a contract, main function is task() as with any job
 * 
 * @author Martin Koelbl
 */
public class Job_LegalCheck extends JobAbstract implements ReportResult
{
	public static final String CONTRACT_FILE = "Contract";
	public static final String XSD_FILE = "XSDFile";
	public static final String MODEL_XML_FILE = "XmlFile";
	public static final String VALUES = "VariableWerte";
	public static final String ANALYSEN = "Analyse";

	public static final String ANA_RESULT = "Result";
	public static final String SEQUENCE = "Sequence";
	public static final String MINMAX = "MinMax";
	public static final String RESULT_KIND = "Kind";
	public static final String UNSAT_CORE = "UnsatCore";

	ResourceString ResultNext = null;
	ResourceFile xmlFile = null;

	public Job_LegalCheck(RunContext parent)
	{
		super(parent);
		createInputDescr(CONTRACT_FILE, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(XSD_FILE, ResourceType.FILE);
		createInputDescr(MODEL_XML_FILE, ResourceType.FILE);
		createInputDescr(ANALYSEN, ResourceType.STRING);
		createInputDescr(VALUES, ResourceType.DOUBLE);

		createResultDescr(ANA_RESULT, ResourceType.STRING);
		createResultDescr(MODEL_XML_FILE, ResourceType.FILE);
	}

	public UmlModel2 parseUmlModel(ResourceFile resFile, ResourceFile xmlFile, ResourceFile xsd)
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
		return (new Contract2Uml2(this, xmlFile, xsd)).convert(contract);
	}

	public JobState task()
	{
		ResourceFile res = getResourceWithType(CONTRACT_FILE, false);
		if (res == null)
			return endError("Missing input file");
		ResourceFile xsd = getResourceWithType(XSD_FILE, false);

		xmlFile = getResourceWithType(MODEL_XML_FILE, false);
		if ((xmlFile != null) && !!!xmlFile.isAbsolutePath())
			xmlFile.setFolder(getFolderText());

		UmlModel2 model2 = parseUmlModel(res, xmlFile, xsd);
		if (model2 == null)
			return endError("Error with parsing of contract file!");
		if (model2.getClassInstances(LegalUml.SPA).isEmpty())
			return endError("Error Contract instance is missing!");

		ResourceDouble resV = getResourceWithType(VALUES, false);

		ResourceString resA = getResourceWithType(ANALYSEN, false);
		List<UmlAnalysisFactory> anaFac = getAnalysisFactories(resA, resV);

		// run different analyses
		UmlAnalysisExecutor executor = new UmlAnalysisExecutor(this);
		for (UmlAnalysisFactory fac : anaFac)
		{
			// generate analyses instances
			for (UmlAnalysis ana : fac.createAnalyses(model2))
			{
				// run analysis
				executor.runAnalysis(ana, this);
			}
		}
		return end(JobResult.OK);
	}

	private List<UmlAnalysisFactory> getAnalysisFactories(ResourceString resA, ResourceDouble resV)
	{
		List<UmlAnalysisFactory> anaFacs = new ArrayList<>();
		if (resA == null)
		{
			resA = new ResourceString(UmlAnalysisSyntax.Name);
			resA.addNext(new ResourceString(UmlAnalysisSPA.Name));
			resA.addNext(new ResourceString(UmlAnalysisSPAClaim.Name));
			resA.addNext(new ResourceString(UmlAnalysisSPAClaimUnsat.Name));
			resA.addNext(new ResourceString(UmlAnalysisSPADependent.Name));
		}
		while (resA != null)
		{
			String val = resA.getData();
			if (val == null)
				continue;
			if (val.equals(UmlAnalysisSyntax.Name))
				anaFacs.add(new UmlAnalysisSyntax(this, val));
			if (val.equals(UmlAnalysisSPA.Name))
				anaFacs.add(new UmlAnalysisSPA(this, val));
			if (val.equals(UmlAnalysisSPAClaim.Name))
				anaFacs.add(new UmlAnalysisSPAClaim(this, val));
			if (val.equals(UmlAnalysisSPAClaimUnsat.Name))
				anaFacs.add(new UmlAnalysisSPAClaimUnsat(this, val));
			if (val.equals(UmlAnalysisSPADependent.Name))
				anaFacs.add(new UmlAnalysisSPADependent(this, val));
			resA = resA.getNextByType();
		}
		return anaFacs;
	}

	private ResourceString addResult(UmlAnalysis ana, UmlResult result)
	{
		String name = ANA_RESULT + "_" + result.anaName;
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
		if (ANA_RESULT.equals(name))
			return ResultNext;
		if (MODEL_XML_FILE.equals(name))
			return xmlFile;
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
