package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

public class Run_MainLegalCheck extends JobAbstractTest
{
	String projectName = "pretzelSPA3_bad";
	String nameFile = projectName + ".json";
	String xmlFile = projectName + ".xml";
	String xsdFile = "legal.xsd";

	@Override
	protected Job createJob()
	{
		// ignoreTest = true;
		return new Job_LegalCheck(this);
	}

	ResourceFile getFile(String file)
	{
		ClassLoader classLoader = getClass().getClassLoader();
		URL urlCmp = classLoader.getResource(file);
		assertTrue(urlCmp != null);
		String filePath = JobAbstractTest.getPath(urlCmp);
		ResourceFileXml resFile = new ResourceFileXml();
		resFile.setData(filePath);
		return resFile;
	}

	@Override
	protected ResourceInterface getResourceByName(String name, boolean out)
	{
		// add inputs
		if (Job_LegalCheck.CONTRACT_FILE.compareTo(name) == 0)
		{
			return getFile(nameFile);
		} else if (Job_LegalCheck.XSD_FILE.compareTo(name) == 0)
		{
			return getFile(xsdFile);
		} else if (Job_LegalCheck.MODEL_XML_FILE.compareTo(name) == 0)
		{
			// xml model output file
			ResourceFileXml resXml = new ResourceFileXml();
			resXml.setData(xmlFile);
			return resXml;
		} else if (Job_LegalCheck.ANALYSEN.compareTo(name) == 0)
		{
			// execute only a single analysis
			//ResourceString resAna = new ResourceString();
			//resAna.setData(UmlAnalysisContractClaimDependency.Name);
			// return resAna;
		}
		return null;
	}

	void outputResult(ResourceInterface res)
	{
		String buf = "";
		if (res instanceof ResourceString)
		{
			ResourceString rs = (ResourceString) res;
			buf += rs.getData() + " ";
		}
		ResourceInterface child = res.getChild();
		while (child != null)
		{
			if (child instanceof ResourceString)
			{
				ResourceString rs = (ResourceString) child;
				buf += rs.getData() + " ";
			}
			child = child.getNext();
		}
		logEventStatus(JobEvent.INFO, buf);
	}

	@Override
	public void endTest()
	{
		ResourceInterface res = this.jobTest.getResource(Job_LegalCheck.ANA_RESULT, true);
		while (res != null)
		{
			outputResult(res);
			res = res.getChild();
		}
	}

	public static void main(String args[])
	{
		(new Run_MainLegalCheck()).testAll();
	}
}
