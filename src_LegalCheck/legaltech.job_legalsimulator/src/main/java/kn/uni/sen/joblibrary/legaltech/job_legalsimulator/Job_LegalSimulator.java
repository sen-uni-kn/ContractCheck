package kn.uni.sen.joblibrary.legaltech.job_legalsimulator;

import java.io.InputStream;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractParser;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.Contract2Uml2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.ReportResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysis;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResult;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;
import kn.uni.sen.jobscheduler.common.resource.ResourceTag;
import kn.uni.sen.jobscheduler.common.resource.ResourceType;

/**
 * Computes actions are possible for a contract.
 * 
 * @author Martin Koelbl
 */
public class Job_LegalSimulator extends JobAbstract implements ReportResult
{
	public static final String CONTRACT_FILE = "Contract";
	public static final String XSD_FILE = "XSDFile";
	public static final String MODEL_XML_FILE = "XmlFile";

	public static final String ANA_RESULT = "Result";

	ResourceString ResultNext = null;
	ResourceFile xmlFile = null;

	public Job_LegalSimulator(RunContext parent)
	{
		super(parent);
		createInputDescr(CONTRACT_FILE, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(XSD_FILE, ResourceType.FILE);
		createInputDescr(MODEL_XML_FILE, ResourceType.FILE);

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

		return end(JobResult.OK);
	}

	@Override
	public void reportResult(UmlAnalysis ana, UmlResult res)
	{
	}
}
