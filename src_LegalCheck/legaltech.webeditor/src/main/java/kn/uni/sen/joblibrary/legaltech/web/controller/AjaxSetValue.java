package kn.uni.sen.joblibrary.legaltech.web.controller;

import java.util.ArrayList;
import java.util.List;

public class AjaxSetValue
{
	String variable = "";
	String value = "";
	Integer sessionID = 0;
	List<String> logList = new ArrayList<>();

	public void setValue(String title)
	{
		value = title;
	}

	public String getValue()
	{
		return value;
	}

	public void setVariable(String title)
	{
		variable = title;
	}

	public String getVariable()
	{
		return variable;
	}

	public void setsessionID(Integer title)
	{
		sessionID = title;
	}

	public Integer getsessionID()
	{
		return sessionID;
	}

	public void addLog(String log)
	{
		logList.add(log);
	}

	public List<String> getLogList()
	{
		return logList;
	}
}
