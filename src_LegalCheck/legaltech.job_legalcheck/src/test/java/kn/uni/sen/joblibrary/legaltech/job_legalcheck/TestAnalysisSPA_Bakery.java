package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPA;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.JobDataTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

/**
 * Checks whether SPA analysis returns the expected values.
 * 
 * @author Martin Koelbl
 */
public class TestAnalysisSPA_Bakery extends JobAbstractTest
{
	String projectName = null;
	String nameFile = null;
	String xmlFile = null;
	String xsdFile = "legal.xsd";

	String expectedResult = null;

	class TestCase
	{
		public TestCase(String file, String result)
		{
			this.nameFile = file;
			this.result = result;
		}

		public String nameFile;
		public String result;
	}

	TestCase[] tests = { new TestCase("pretzelSPA3_bad", Job_LegalCheck.SEQUENCE),
			new TestCase("unit/pretzelSPA3_noexe", Job_LegalCheck.UNSAT_CORE) };

	@Override
	protected Job createJob()
	{
		// ignoreTest = true;
		return new Job_LegalCheck(this);
	}

	@Override
	protected JobDataTest createTest(Job jobTest2, int index)
	{
		if (index > tests.length)
			// no further test
			return null;

		JobDataTest data = new JobDataTest();
		projectName = tests[index - 1].nameFile;
		expectedResult = tests[index - 1].result;

		nameFile = projectName + ".json";
		xmlFile = projectName + ".xml";
		return data;
	}

	ResourceFile getFile(String file)
	{
		ClassLoader classLoader = getClass().getClassLoader();
		URL urlCmp = classLoader.getResource(file);
		assert (urlCmp != null) : "Resource file is missing.";
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
			// execute only the claim analysis (SPA and single claims)
			ResourceString resAna = new ResourceString();
			resAna.setData(UmlAnalysisSPA.Name);
			return resAna;
		}
		return null;
	}

	void testResult(ResourceString res)
	{
		if (Job_LegalCheck.SEQUENCE.equals(res.getName()))
		{
			assertTrue(expectedResult.equals(Job_LegalCheck.SEQUENCE));
		} else if (Job_LegalCheck.UNSAT_CORE.equals(res.getName()))
		{
			assertTrue(expectedResult.equals(Job_LegalCheck.UNSAT_CORE));
		}
	}

	@Override
	public void endTest()
	{
		ResourceString res = jobTest.getResourceWithType(Job_LegalCheck.ANA_RESULT, true);
		assertTrue(res.getData() != null);
		res = (ResourceString) res.getChild();
		while (res != null)
		{
			testResult(res);
			res = (ResourceString) res.getNext();
		}
	}

	public static void main(String args[])
	{
		(new TestAnalysisSPA_Bakery()).testAll();
	}
}
