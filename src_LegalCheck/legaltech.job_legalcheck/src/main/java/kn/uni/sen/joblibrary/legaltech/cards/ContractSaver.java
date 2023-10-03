package kn.uni.sen.joblibrary.legaltech.cards;

import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Map;

import org.json.JSONArray;
import org.json.JSONObject;

import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

/**
 * stores the contract cards of a contract in json
 * 
 * @author Martin Koelbl
 */
public class ContractSaver
{
	public String saveFile(Contract contract, String file)
	{
		if ((contract == null) || (file == null))
			return "Missing";

		JSONObject jcon = createJsonContract(contract);
		try
		{
			ResourceFile.createFile(file, false);

			FileWriter writer = new FileWriter(file);
			// String val = jcon.toString();
			String val = jcon.toString(2);
			writer.write(val);
			writer.flush();
			writer.close();
		} catch (IOException ex)
		{
			return "Error Save Contract";
		}
		return null;
	}

	private JSONObject createJsonContract(Contract contract)
	{
		JSONArray ar = new JSONArray();

		JSONObject obj = new JSONObject();
		obj.put("contract", ar);

		int counter = 0;
		List<ContractCard> cards = contract.getCardList();
		for (ContractCard c : cards)
		{
			JSONObject o = saveCard(counter++, c);
			if (o != null)
				ar.put(o);
		}
		return obj;
	}

	JSONArray createArray(List<String> list)
	{
		JSONArray arr = new JSONArray();
		for (String s : list)
		{
			arr.put(s);
		}
		return arr;
	}

	JSONArray createArray(Map<String, String> map)
	{
		JSONArray arr = new JSONArray();
		for (String k : map.keySet())
		{
			String v = map.get(k);
			if (v != null)
			{
				JSONObject jc = new JSONObject();
				jc.put(ContractParser.Eval, k);
				jc.put(ContractParser.Text, v);
				arr.put(jc);
			}
		}
		return arr;
	}

	private JSONObject saveCard(int index, ContractCard c)
	{
		if (c == null)
			return null;

		JSONObject jc = new JSONObject();
		jc.put(ContractParser.ID, c.getID());
		jc.put(ContractParser.Index, c.getIndex());
		jc.put(ContractParser.Text, c.getPlainText());
		String multi = c.getMultiplicity();
		if (multi != null)
			jc.put("Multiplicity", multi);
		jc.put(ContractParser.Object, createArray(c.getVariableList()));
		jc.put(ContractParser.Assignment, createArray(c.getAssignmentList()));
		// jc.put(ContractParser.Constraint,
		// createArray(c.getConstraintList()));

		Map<String, String> map = c.getResultMap();
		if (!!!map.isEmpty())
			jc.put(ContractParser.Tatbestand, createArray(map));
		return jc;
	}
}
