package kn.uni.sen.joblibrary.legaltech.html;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractCard;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.ComputeClause;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;

public class HtmlCreator_ContractInput
{
	boolean bPlus = false;
	boolean bHide = false;

	int paragraph = 0;
	int absatz = 0;
	int satz = 0;

	public HtmlCreator_ContractInput(boolean p, boolean h)
	{
		bPlus = p;
		bHide = h;
	}

	public boolean isPlus()
	{
		return bPlus;
	}

	public boolean isHide()
	{
		return bPlus;
	}

	String getCardHead(ContractCard card, int cardIndex, boolean last)
	{
		String minus = "";
		if (isPlus())
			minus += "<input type='button' onclick=\"changeCard('remove_" + cardIndex + "')\" value='Remove' />";
		if (isHide())
		{
			String text = "Hide";
			if (card.isHidden())
				text = "Unhide";
			minus += "<input type='button' onclick=\"changeCard('hide_" + cardIndex + "')\" value='" + text + "' />";
		}

		String up = "";
		if (cardIndex > 1)
			up = "<input type='button' onclick=\"changeCard('switch_" + cardIndex + "_" + (cardIndex - 1)
					+ "')\" value='Up' />";

		String down = "";
		if (!!!last)
			down = "<input type='button' onclick=\"changeCard('switch_" + cardIndex + "_" + (cardIndex + 1)
					+ "')\" value='Down' />";
		return "<b>" + card.getID() + "</b>  " + minus + up + down;
	}

	List<String> getInstancesByClass(Contract contract, String cl)
	{
		List<String> list = new ArrayList<>();
		if (contract == null)
			return list;
		for (ContractCard card : contract.getCardList())
		{
			card.getInstancesByClass(list, cl);
		}
		return list;
	}

	ComputeClause clauseComputer = null;

	String getNodeValue(ContractCard card, String text, String type)
	{
		if (card == null)
			return "";
		if (type == null)
			return card.getNodeValue(text);
		if (type.startsWith(LegalUml.Clause))
		{
			//don't set value of reference
			String val2 = card.getVariableDeclare(text);
			if(val2.contains("$"))
			{
				String ref = card.getNodeValue(text);
				Contract con = card.getContract();
				String val4 = con.getNodeValueNice(ref);
				//String val3 = card.getNodeValue(ref);
				return val4;
			}

			String val = clauseComputer.getClause(type, null);
			//set value of current clause
			card.setVariableAssignment(text, val);
			return val;
		}
		return card.getNodeValue(text);
	}

	String getHtmlNode(ContractCard card, String text)
	{
		String type = card.getNodeType(text);
		String value = getNodeValue(card, text, type);
		String nameText = card.getID() + "." + text;

		if ("String".equals(type))
		{
			return "<input name='" + nameText + "' onfocusout='sendValue(this)' value='" + value
					+ "' placeholder='Input...'></input>";
		} else if ("Integer".equals(type))
		{
			return "<input type='number' name='" + nameText
					+ "' onfocusout='sendValue(this)' placeholder='10000' value='" + value + "'></input>";
		} else if (LegalUml.Head.equals(type))
		{
			return "<input class='header1' name='" + nameText
					+ "' onfocusout='sendValue(this)' placeholder='Vertragstitel' value='" + value + "'></input>";
		} else if (LegalUml.Head2.equals(type))
		{
			return "<input class='header2' name='" + nameText
					+ "' onfocusout='sendValue(this)' placeholder='Absatzname' value='" + value + "'></input>";
		} else if (LegalUml.DateS.equals(type))
		{
			return "<input type='number' name='" + nameText + "' onfocusout='sendValue(this)' placeholder='Tag' value='"
					+ value + "' min='0'></input>";
		} else if ((type != null) && type.startsWith(LegalUml.Clause))
			;
		else if (LegalUml.isNodeClass(type))
		{
			List<String> list = getInstancesByClass(card.getContract(), type);
			String select = "<select name='" + nameText + "' onchange='sendValue(this)' >";
			for (String s : list)
			{
				if (s == null)
					continue;
				String selected = s.equals(value) ? "selected" : "";
				select += "<option value='_" + s + "'" + selected + ">" + s + "</option>";
			}
			select += "</select>";
			return select;
		}
		if (value != null)
			return "" + value;
		return "";
	}

	String getCardHtml(ContractCard card)
	{
		if (card == null)
			return "";
		if (isHide() && card.isHidden())
			return "";

		String text = card.getPlainText();
		Pattern pattern = Pattern.compile("\\$([^\\s]+)");
		Matcher matcher = pattern.matcher(text);

		StringBuilder sb = new StringBuilder();
		while (matcher.find())
		{
			String pat = text.substring(matcher.start() + 1, matcher.end());
			String rep = getHtmlNode(card, pat);
			if (rep == null)
				continue;
			if (rep.contains("$"))
			{
				System.out.println("Warning: Replace elements recursively" + rep);
				rep = rep.replace("$", "");
				// continue;
			}
			matcher.appendReplacement(sb, rep);
		}
		matcher.appendTail(sb);
		String val = sb.toString();
		return val;
	}

	String getBrickPlus(Contract bricks, int cardIndex)
	{
		List<ContractCard> brickList = bricks.getCardList();

		String plus = "<div class='plus' action='addCard.html' method='post'><ul>";
		plus += "<input type='hidden' th:name='${_csrf.parameterName}' th:value='${_csrf.token}' />";
		plus += "<input type='hidden' name='runID' th:value='${runID}' />";
		plus += "<button onclick ='unhidePlus(this)'>+</button>";

		int counter = 1;
		for (ContractCard c : brickList)
		{
			plus += "<li hidden>"; // <em name='name' value='" + c.getID() +
									// "'>" + c.getID() + "</em>";
			plus += "<p>" + c.getID() + ": " + c.getPlainText() + "</p>";
			plus += "<input type='button' onclick=\"changeCard('add_" + cardIndex + "_" + counter++
					+ "')\" value='Add' />";
			plus += "</li>";
		}
		plus += "</ul></div>";
		return plus;
	}

	void reset()
	{
		paragraph = 0;
		absatz = 0;
		satz = 0;
	}

	public String getContractHtml(Contract contract, Contract bricks)
	{
		if (bricks == null)
			return "No Template Texts";
		reset();
		String html = "";
		if (isPlus())
			html += getBrickPlus(bricks, 0);
		List<ContractCard> cardList = null;
		if (contract != null)
			cardList = contract.getCardList();

		clauseComputer = new ComputeClause();
		int counter = 1;
		if (cardList != null)
			for (ContractCard card : cardList)
			{
				boolean last = cardList.size() == counter;
				html += "<p>" + getCardHead(card, counter, last) + "<br/>" + getCardHtml(card) + "</p>";
				if (isPlus())
					html += getBrickPlus(bricks, counter++);
			}
		return html;
	}
}
