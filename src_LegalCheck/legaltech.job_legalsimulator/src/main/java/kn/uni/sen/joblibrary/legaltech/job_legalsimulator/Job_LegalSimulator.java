package kn.uni.sen.joblibrary.legaltech.job_legalsimulator;

import java.io.InputStream;
import java.util.List;
import java.util.ArrayList;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractParser;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.Contract2Uml2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.Job_LegalCheck;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.ReportResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysis;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResult;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResultState;
import kn.uni.sen.jobscheduler.common.impl.JobAbstract;
import kn.uni.sen.jobscheduler.common.model.JobResult;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.model.RunContext;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceInteger;
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
	public static final String ACTIONS = "Actions";
	public static final String ACTION_DAY = "day";

	public static final String ANA_RESULT = "Result";
	public static final String RESULT_KIND = Job_LegalCheck.RESULT_KIND;
	public static final String SEQUENCE = Job_LegalCheck.SEQUENCE;
	public static final String NEXT_ACTIONS = "NextActions";

	ResourceString ResultNext = null;
	ResourceFile xmlFile = null;

	public Job_LegalSimulator(RunContext parent)
	{
		super(parent);
		createInputDescr(CONTRACT_FILE, ResourceType.FILE).addTag(ResourceTag.NECESSARY);
		createInputDescr(XSD_FILE, ResourceType.FILE);
		createInputDescr(MODEL_XML_FILE, ResourceType.FILE);
		createInputDescr(ACTIONS, ResourceType.STRING);
		createInputDescr(ACTION_DAY, ResourceType.INTEGER);

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

		ResourceString res_actions = getResourceWithType(ACTIONS, false);
		List<String> actions = new ArrayList<>();
		while (res_actions != null)
		{
			actions.add(res_actions.getData());
			res_actions = (ResourceString) res_actions.getNext();
		}
		
		ResourceInteger res_day = getResourceWithType(ACTION_DAY, false);
		int action_day = res_day.getDataValue();

		xmlFile = getResourceWithType(MODEL_XML_FILE, false);
		if ((xmlFile != null) && !!!xmlFile.isAbsolutePath())
			xmlFile.setFolder(getFolderText());

		UmlModel2 model2 = parseUmlModel(res, xmlFile, xsd);
		if (model2 == null)
			return endError("Error with parsing of contract file!");
		if (model2.getClassInstances(LegalUml.SPA).isEmpty())
			return endError("Error Contract instance is missing!");

		ActionAnalysis ana = new ActionAnalysis(this, model2, actions, action_day);
		ana.runAnalysis(this, null);

		return end(JobResult.OK);
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
		if (result.rest != UmlResultState.NONE)
			res.addChild(en);

		if (result.diagram != null)
		{
			ResourceString res2 = new ResourceString(name);
			res2.setName(SEQUENCE);
			res2.setData(result.diagram);
			res.addChild(res2);
		}

		if (result.actions != null)
		{
			ResourceString actNext = null;
			for (String act : result.actions)
			{
				ResourceString res2 = new ResourceString(name);
				res2.setName(NEXT_ACTIONS);
				res2.setData(act);
				if (actNext == null)
					res.addChild(res2);
				else
					actNext.addChild(res2);
				actNext = res2;
			}
		}

		if (ResultNext == null)
			ResultNext = res;
		else
			ResultNext.addNext(res);
		return res;
	}

	@Override
	public void reportResult(UmlAnalysis ana, UmlResult res)
	{
		if ((res == null) || (res.text == null))
			return;

		addResult(ana, res);
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
}
