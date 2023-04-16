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
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

/**
 * Check whether SPA analysis of a model is still the expected one.
 * 
 * @author Martin Koelbl
 */
public class TestStable_BakeryAnalysisSPA extends JobAbstractTest
{
	String projectName = "pretzelSPA3_bad";
	String nameFile = projectName + ".json";
	String xmlFile = projectName + ".xml";
	String xsdFile = "legal.xsd";

	String resultSpaFile = "AnalysisSPA.z3";
	String xmlCompareFile = ResourceFolder.appendFolder("unit", "AnalysisSpa_petzelSPA3.z3");
	String xmlCompareBadFile = ResourceFolder.appendFolder("unit", "AnalysisSpa_petzelSPA3_bad.z3");

	ResourceFile spaFile = new ResourceFileXml();
	{
		spaFile.setFolder("result");
		spaFile.setFileName(resultSpaFile);
	}

	@Override
	protected Job createJob()
	{
		// ignoreTest = true;
		return new Job_LegalCheck(this);
	}

	@Override
	protected JobDataTest createTest(Job jobTest2, int index)
	{
		JobDataTest data = super.createTest(jobTest2, index);
		if (data != null)
		// another test is executed
		{
			// delete old SPA analysis output if existing
			if (spaFile.exists())
				spaFile.removeFile();
			assertTrue("SPA analysis file exists!", !!!spaFile.exists());
		}
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

	void checkExpectedSPA()
	{
		assertTrue("Expected SPA Analysis file is missing.", spaFile.exists());

		// get comparison file
		ResourceFile cmpFile = getFile(xmlCompareFile);
		ResourceFile cmpFileBad = getFile(xmlCompareBadFile);

		String dataSpa = spaFile.getContent();
		String dataCmp = cmpFile.getContent();
		String dataCmpBad = cmpFileBad.getContent();

		// test whether test is working
		assertTrue("Test-test should fail but passes.", Helper.compareLines(dataSpa, dataCmpBad) != null);

		// do the actual test, compare line-wise since the sequence can change
		String dif = Helper.compareLines(dataSpa, dataCmp);
		assertTrue("Xml file of " + nameFile + " changed.\n" + dif, dif == null);
	}

	@Override
	public void endTest()
	{
		checkExpectedSPA();
	}

	public static void main(String args[])
	{
		(new TestStable_BakeryAnalysisSPA()).testAll();
	}
}
