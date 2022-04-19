package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

public class Test_MainLegalCheck extends JobAbstractTest
{
	String nameFile = "ContractBad.xml";
	{
		// nameFile = "ContractGood.xml";
		// nameFile = "ShareDeal5.6.xmi";
		// nameFile = "brezenvertrag_object.json";
		// nameFile = "brezenvertrag_bad.json";
		// nameFile = "pretzelSPA_bad.json";
		nameFile = "pretzelSPA2_bad.json";
	}

	String xsdFile = "legal.xsd";

	@Override
	protected Job createJob()
	{
		// ignoreTest = true;
		return new Job_LegalCheck(this);
	}

	@Override
	protected ResourceInterface getResourceByName(String name, boolean out)
	{
		// add inputs
		if (Job_LegalCheck.CONTRACT_FILE.compareTo(name) == 0)
		{
			ClassLoader classLoader = getClass().getClassLoader();
			URL res = classLoader.getResource(nameFile);
			assertTrue(res != null);
			// add inputs
			String data = JobAbstractTest.getPath(res);
			ResourceFileXml resXml = new ResourceFileXml();
			resXml.setData(data);
			return resXml;
		} else if (Job_LegalCheck.XSD_FILE.compareTo(name) == 0)
		{
			ClassLoader classLoader = getClass().getClassLoader();
			URL res = classLoader.getResource(xsdFile);
			assertTrue(res != null);
			// add inputs
			String data = JobAbstractTest.getPath(res);
			ResourceFileXml resXml = new ResourceFileXml();
			resXml.setData(data);
			return resXml;
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
		ResourceInterface res = this.jobTest.getResource(Job_LegalCheck.RESULT, true);
		while (res != null)
		{
			outputResult(res);
			res = res.getChild();
		}
	}

	public static void main(String args[])
	{
		(new Test_MainLegalCheck()).testAll();
	}
}
