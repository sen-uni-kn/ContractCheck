package kn.uni.sen.joblibrary.legaltech.web.controller;

public class AjaxAddCard
{
	String cardvalue = "";
	Integer sessionID = 0;
	String msg = "";

	public void setcardvalue(String title)
	{
		cardvalue = title;
	}

	public String getcardvalue()
	{
		return cardvalue;
	}
	
	public void setsessionID(Integer title)
	{
		sessionID = title;
	}

	public Integer getsessionID()
	{
		return sessionID;
	}

	public String getMsg() {
		return msg;
	}

	public void setMsg(String msg) {
		this.msg = msg;
	}
}
