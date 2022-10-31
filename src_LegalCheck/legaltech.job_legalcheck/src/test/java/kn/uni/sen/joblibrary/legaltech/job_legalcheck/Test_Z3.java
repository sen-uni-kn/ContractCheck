package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import static org.junit.Assert.assertTrue;

import java.net.URL;

import org.junit.Test;

import kn.uni.sen.joblibrary.legaltech.uml_analysis.Z3Call;
import kn.uni.sen.jobscheduler.common.JobAbstractTest;

public class Test_Z3
{
	String nameFile = "test.z3";

	@Test()
	public void Z3test()
	{
		ClassLoader classLoader = getClass().getClassLoader();
		URL res = classLoader.getResource(nameFile);
		assertTrue(res != null);
		// add inputs
		String file = JobAbstractTest.getPath(res);

		Z3Call call = new Z3Call();
		if (!!!call.runFile(file, true))
			assert (false);
	}

	public static void main(String args[])
	{
		(new Test_Z3()).Z3test();
	}
}
