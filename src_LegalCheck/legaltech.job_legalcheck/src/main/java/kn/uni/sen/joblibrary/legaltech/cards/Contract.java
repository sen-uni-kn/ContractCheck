package kn.uni.sen.joblibrary.legaltech.cards;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**	Contract is stored by a set of contract cards
 * 
 * @author Martin Koelbl
 */
public class Contract
{
	String id = "";
	public List<ContractCard> cardList = new ArrayList<>();
	int idCounter = 1;

	public void addCard(ContractCard card)
	{
		addCard(cardList.size(), null, card);
	}

	public List<ContractCard> getCardList()
	{
		return cardList;
	}

	public void addCard(int idx, String id, ContractCard c)
	{
		if (c == null)
			return;
		if (getContractCard(c.getID()) != null)
		{
			if (id == null)
				id = c.getID();
			String id2 = id + "_" + idCounter++;
			c.setID(id2);
			addCard(idx, id, c);
			// System.out.println("Warning: Card ID is not unique: " +
			// c.getID());
			return;
		}
		c.setContract(this);
		cardList.add(idx, c);
		return;
	}

	public ContractCard getContractCard(String id)
	{
		for (ContractCard c : cardList)
			if (c.getID().equals(id))
				return c;
		return null;
	}

	public String getCardText()
	{
		String txt = "" + id + "\n";
		for (ContractCard c : cardList)
		{
			txt += c.getCardText() + "\n";
		}
		return txt;
	}

	public ContractCard getCardById(String id)
	{
		if ((id == null) || id.isEmpty())
			return null;
		for (ContractCard c : cardList)
			if (id.equals(c.getID()))
				return c;
		return null;
	}

	public String getCardNameFromVariable(String name)
	{
		int idx = name.indexOf("_");
		if (idx == -1)
			return null;
		return name.substring(0, idx);
	}

	public String getVariableNameFromVariable(String name)
	{
		int idx = name.indexOf("_");
		if (idx == -1)
			return name;
		return name.substring(idx + 1);
	}

	public String getNodeValueNice(String name)
	{
		ContractCard c = getCardById(getCardNameFromVariable(name));
		if (c == null)
			return null;
		String var = getVariableNameFromVariable(name);
		return c.getNodeValueNice(var);
	}

	public void sortCards()
	{
		cardList.sort(new Comparator<>()
		{
			@Override
			public int compare(ContractCard c1, ContractCard c2)
			{
				return c1.getIndexValue() - c2.getIndexValue();
			}
		});
	}
}
