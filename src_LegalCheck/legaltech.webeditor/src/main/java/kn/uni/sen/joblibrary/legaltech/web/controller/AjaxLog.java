package kn.uni.sen.joblibrary.legaltech.web.controller;

import java.util.ArrayList;
import java.util.List;

public class AjaxLog
{
	Integer sessionID = 0;
	List<String> logList = new ArrayList<>();
	List<String> resultList = new ArrayList<>();

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

	public void addResult(String log)
	{
		resultList.add(log);
	}

	public List<String> getResultList()
	{
		return resultList;
	}

	public List<String> getLogList()
	{
		return logList;
	}
}
