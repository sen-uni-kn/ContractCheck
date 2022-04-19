package kn.uni.sen.joblibrary.legaltech.web.run;

public class JobData
{
	public JobData(String name, String version)
	{
		this.name = name;
		this.version = version;
	}

	public String name;
	public String version;

	public String getName()
	{
		return name;
	}

	public String getVersion()
	{
		return version;
	}
}
