package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisSPA;
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
			resAna.setData(UmlAnalysisSPA.Name);
			return resAna;
		}
		return null;
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

		String dataXml = xmlFile.getContent();
		String dataCmp = cmpFile.getContent();
		String dataCmpBad = cmpFileBad.getContent();

		// test whether test is working
		assertTrue("Test-test should fail but passes.", Helper.compareText(dataXml, dataCmpBad) != null);

		// do the actual test
		String dif = Helper.compareText(dataXml, dataCmp);
		assertTrue("Xml file of " + nameFile + " changed.\n" + dif, dif == null);
	}

	public static void main(String args[])
	{
		(new TestStable_BakeryXml()).testAll();
	}
}
