package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisContractClaimDependency;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;

/**
 * Check whether xml model of a model is still the expected one.
 * 
 * @author Martin Koelbl
 */
public class TestStable_BakeryXml extends JobAbstractTest
{
	String projectName = "pretzelSPA3_bad";
	String nameFile = projectName + ".json";
	String xmlFile = projectName + ".xml";
	String xsdFile = "legal.xsd";

	String xmlCompareFile = ResourceFolder.appendFolder("unit", projectName + "_xml.xml");
	String xmlCompareFileBad = ResourceFolder.appendFolder("unit", projectName + "_xml_bad.xml");

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
			resAna.setData(UmlAnalysisContractClaimDependency.Name);
			// return resAna;
		}
		return null;
	}

	String compareLine(String line1, String line2)
	{
		String[] words1 = line1.split("\\s+");
		String[] words2 = line2.split("\\s+");
		int length = Integer.min(words1.length, words2.length);
		for (int i = 0; i < length; i++)
		{
			if (words1[i].compareTo(words2[i]) != 0)
			{
				String dif = "differs in words: " + words1[i] + " " + words2[i];
				return "line: " + line1 + "\n" + "line: " + line2 + "\n" + dif;
			}
		}
		if (words1.length != words2.length)
			return "line: " + line1 + "\n" + "line: " + line2 + "\n" + "Different number of words.";
		return null;
	}

	String compareText(String text1, String text2)
	{
		String[] lines1 = text1.split("\n");
		String[] lines2 = text2.split("\n");
		int length = Integer.min(lines1.length, lines2.length);
		for (int i = 0; i < length; i++)
		{
			String dif = compareLine(lines1[i], lines2[i]);
			if (dif != null)
				return dif;
		}
		if (lines1.length != lines2.length)
			return "Different number of lines";
		return null;
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
	public void endTest()
	{
		ResourceInterface res = this.jobTest.getResource(Job_LegalCheck.MODEL_XML_FILE, true);
		assert (res != null);
		ResourceFile xmlFile = (ResourceFile) res;

		// get comparison file
		ResourceFile cmpFile = getFile(xmlCompareFile);
		ResourceFile cmpFileBad = getFile(xmlCompareFileBad);

		String data1 = xmlFile.getContent();
		String dataCmp = cmpFile.getContent();
		String dataCmpBad = cmpFileBad.getContent();

		// test whether test is working
		String dif = compareText(data1, dataCmpBad);
		assert (dif != null) : "Test-test should fail but passes.";

		// do the real test test
		dif = compareText(data1, dataCmp);
		if (dif != null)
		{
			logError("Xml file of " + nameFile + " changed.\n" + dif);
		}
	}

	public static void main(String args[])
	{
		(new TestStable_BakeryXml()).testAll();
	}
}
