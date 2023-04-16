package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;
import java.util.HashMap;
import java.util.Map;

import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPADependent;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

/**
 * Checks whether claim analysis returns the expected values.
 * 
 * @author Martin Koelbl
 */
public class TestAnalysisDependent_Bakery extends JobAbstractTest
{
	String projectName = "unit/pretzelSPA3_depend";
	String nameFile = projectName + ".json";
	String xmlFile = projectName + ".xml";
	String xsdFile = "legal.xsd";

	String expectedResultName = null;
	String expectedResult = null;

	class ResultCase
	{
		public ResultCase(String result)
		{
			this.result = result;
		}

		public String result;
	}

	Map<String, ResultCase> expectedResults = new HashMap<>();
	{
		expectedResults.put("Result_ClaimDependent_Block1_transfer_Block2_payment",
				new ResultCase(Job_LegalCheck.SEQUENCE));
	}

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
			resAna.setData(UmlAnalysisSPADependent.Name);
			return resAna;
		}
		return null;
	}

	void testResult(ResourceString resC, ResultCase resCase)
	{
		assertTrue(resC != null);
		while (resC != null)
		{
			if (Job_LegalCheck.SEQUENCE.equals(resC.getName()))
			{
				assertTrue(resCase.result.equals(Job_LegalCheck.SEQUENCE));
			} else if (Job_LegalCheck.UNSAT_CORE.equals(resC.getName()))
			{
				assertTrue(resCase.result.equals(Job_LegalCheck.UNSAT_CORE));
			}
			resC = (ResourceString) resC.getNext();
		}
	}

	@Override
	public void endTest()
	{
		ResourceString res = jobTest.getResourceWithType(Job_LegalCheck.ANA_RESULT, true);
		assertTrue(res.getData() != null);
		while (res != null)
		{
			ResultCase resultCase = expectedResults.get(res.getData());
			assertTrue(resultCase != null);
			testResult((ResourceString) res.getChild(), resultCase);
			res = (ResourceString) res.getNext();
		}
	}

	public static void main(String args[])
	{
		(new TestAnalysisDependent_Bakery()).testAll();
	}
}
