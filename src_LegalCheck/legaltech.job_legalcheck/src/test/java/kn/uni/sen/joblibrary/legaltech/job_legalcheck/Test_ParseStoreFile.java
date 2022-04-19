package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import org.json.JSONArray;
import org.json.JSONObject;
import org.junit.Test;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractParser;
import kn.uni.sen.joblibrary.legaltech.cards.ContractSaver;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;
import kn.uni.sen.jobscheduler.common.impl.RunContextSimple;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

public class Test_ParseStoreFile
{
	RunContextSimple context = new RunContextSimple(null, "test", "result");

	JSONObject getTestObject()
	{
		JSONArray ar = new JSONArray();
		JSONObject obj = new JSONObject();
		obj.put("contract", ar);

		JSONObject jc = new JSONObject();
		jc.put("Name", "Name1");
		jc.put("Text", "Text1");
		jc.put("Assignment", "Assignment1");
		jc.put("Constraint", "Constraint1");

		ar.put(jc);
		return obj;
	}

	String getTestFile()
	{
		ClassLoader classLoader = getClass().getClassLoader();
		URL res = classLoader.getResource("vorlage_test.json");
		assertTrue(res != null);
		return JobAbstractTest.getPath(res);
	}

	@Test
	public void parseFileTest()
	{
		String file = getTestFile();
		Contract con = parseFile(file);
		assertTrue(con != null);
	}

	Contract parseFile(String file)
	{
		ContractParser parser = new ContractParser(context);
		Contract con = parser.parseFile(file);
		assertTrue(con != null);
		assertTrue(con.getCardList().size() != 0);
		return con;
	}

	@Test
	public void storeFile()
	{
		String fileOrg = getTestFile();
		Contract contract = parseFile(fileOrg);

		ResourceFolder folder = new ResourceFolder("result");
		if (!!!folder.exists())
			folder.createFolder();
		ContractSaver saver = new ContractSaver();
		String file = ResourceFolder.appendFolder(folder.getData(), "test.json");
		saver.saveFile(contract, file);

		ContractParser parser = new ContractParser(context);
		JSONObject obj1 = parser.parseJSONFile(fileOrg);
		JSONObject obj2 = parser.parseJSONFile(file);

		// String s1 = obj1.toString();
		// String s2 = obj2.toString();
		// System.out.println(s1);
		// System.out.println(s2);
		boolean val = obj1.similar(obj2);
		if (!!!val)
			System.out.println("Stored file differs from original file");
		assertTrue(val);
	}

	public static void main(String args[])
	{
		(new Test_ParseStoreFile()).storeFile();
	}
}
