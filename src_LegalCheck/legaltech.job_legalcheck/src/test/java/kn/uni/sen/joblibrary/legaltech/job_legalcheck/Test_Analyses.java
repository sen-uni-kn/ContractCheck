package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPAClaim;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPAClaimLimit;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPAClaimUnsat;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPADependent;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.JobDataTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

public class Test_Analyses extends JobAbstractTest
{
	class TestCase
	{
		public TestCase(String file, String analysis)
		{
			this.file = file;
			this.analysis = analysis;
		}

		public String file;
		public String analysis;
	}

	TestCase[] tests = { new TestCase("TestClaimSat", UmlAnalysisSPAClaim.Name),
			new TestCase("TestClaimUnsat", UmlAnalysisSPAClaimUnsat.Name),
			new TestCase("TestDepend", UmlAnalysisSPADependent.Name),
			new TestCase("TestClaimLimit", UmlAnalysisSPAClaimLimit.Name) };

	String nameFile = null;
	String xmlFile = null;
	String xsdFile = "legal.xsd";
	String analysis = null;

	@Override
	protected Job createJob()
	{
		// ignoreTest = true;
		return new Job_LegalCheck(this);
	}

	@Override
	protected JobDataTest createTest(Job jobTest2, int index)
	{
		if (index - 1 >= tests.length)
			return null;
		TestCase test = tests[index - 1];
		logEventStatus(JobEvent.INFO, ("\n" + index) + ": " + test.file + " " + test.analysis);
		nameFile = test.file + ".json";
		xmlFile = test.file + ".xml";
		analysis = test.analysis;
		return new JobDataTest();
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
			ResourceString resAna = new ResourceString();
			resAna.setData(analysis);
			return resAna;
		}
		return null;
	}

	boolean outputResult(ResourceInterface res)
	{
		boolean err = false;
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
				System.out.print("" + rs.getData());
				if ("ERROR".equals(rs.getData()))
					err = true;
				buf += rs.getData() + " ";
			}
			child = child.getNext();
		}
		logEventStatus(JobEvent.INFO, buf);
		return err;
	}

	@Override
	public void endTest()
	{
		ResourceInterface res = this.jobTest.getResource(Job_LegalCheck.ANA_RESULT, true);
		boolean err = false;
		while (res != null)
		{
			err |= outputResult(res);
			res = res.getChild();
		}
		assertTrue(err);
	}

	public static void main(String args[])
	{
		(new Test_Analyses()).testAll();
	}
}
