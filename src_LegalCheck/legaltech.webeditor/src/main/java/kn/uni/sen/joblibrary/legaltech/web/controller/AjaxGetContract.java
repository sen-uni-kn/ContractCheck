package kn.uni.sen.joblibrary.legaltech.web.controller;

import java.util.ArrayList;
import java.util.List;

public class AjaxGetContract
{
	String contractTitle = "";
	String contractCode = "";
	String msg = "";
	List<String> logList = new ArrayList<>();
	int sessionID;
	List<String> vars = null;

	public void setTitle(String title)
	{
		contractTitle = title;
	}

	public String getTitle()
	{
		return contractTitle;
	}

	// getters and setters
	public void setLogList(List<String> list)
	{
		logList = list;
	}

	public void addLog(String log)
	{
		logList.add(log);
	}

	public List<String> getLogList()
	{
		return logList;
	}

	public void addContract(String code)
	{
		contractCode = code;
	}

	public String getContract()
	{
		return contractCode;
	}

	public String getMsg()
	{
		return msg;
	}

	public void setMsg(String msg)
	{
		this.msg = msg;
	}

	public int getSessionID()
	{
		return sessionID;
	}

	public List<String> getVars()
	{
		return vars;
	}
}
