package kn.uni.sen.joblibrary.legaltech.cards;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Iterator;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;
import org.json.JSONTokener;

import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.RunContext;

/** Parses a json string and stores contract in @see Contract by its @ContractCard 
 * 
 * @author Martin Koelbl
 */
public class ContractParser
{
	public static final String ID = "ID";
	public static final String Index = "Index";
	public static final String Multiplicity = "Multiplicity";
	public static final String Text = "Text";
	public static final String Eval = "Eval";
	public static final String Variable = "Variable";
	public static final String Object = "Object";
	public static final String Assignment = "Assignment";
	public static final String Constraint = "Constraint";
	public static final String Tatbestand = "Tatbestand";

	RunContext context = null;

	public ContractParser(RunContext context)
	{
		this.context = context;
	}

	public JSONObject parseJSONFile(String file)
	{
		try
		{
			FileReader read = new FileReader(file);
			JSONTokener tokener = new JSONTokener(read);
			JSONObject root = new JSONObject(tokener);
			read.close();
			return root;
		} catch (FileNotFoundException e)
		{
			e.printStackTrace();
		} catch (IOException e)
		{
			e.printStackTrace();
		} catch (JSONException e)
		{
			context.logEventStatus(JobEvent.ERROR, e.getMessage());
			// e.printStackTrace();
		}
		return null;
	}
	
	public JSONObject parseJSON(String content)
	{
		try
		{
			JSONTokener tokener = new JSONTokener(content);
			JSONObject root = new JSONObject(tokener);
			return root;
		} catch (JSONException e)
		{
			context.logEventStatus(JobEvent.ERROR, e.getMessage());
			// e.printStackTrace();
		}
		return null;
	}
	
	public Contract parseText(String text)
	{
		JSONObject root = parseJSON(text);
		return parseContent(root);
	}
	
	public Contract parseFile(String file)
	{
		JSONObject root = parseJSONFile(file);
		if (root == null)
		{
			context.logEventStatus(JobEvent.ERROR, "Error parsing file " + file);
			return null;
		}
		return parseContent(root);
	}

	public Contract parseContent(JSONObject root)
	{
		if (root == null)
		{
			context.logEventStatus(JobEvent.ERROR, "Error parsing JSON");
			return null;
		}
		// todo: need better parser for this stuff
		JSONArray js2 = root.getJSONArray("contract");

		Contract con = new Contract();
		for (Iterator<Object> iter = js2.iterator(); iter.hasNext();)
		{
			Object o = iter.next();
			if (o instanceof JSONObject)
			{
				ContractCard c = parseCard((JSONObject) o);
				if (c != null)
					con.addCard(c);
			}
		}
		con.sortCards();
		return con;
	}

	void parseVariable(JSONArray ass, ContractCard c)
	{
		for (Iterator<Object> iter = ass.iterator(); iter.hasNext();)
		{
			Object o = iter.next();
			if (o instanceof String)
				c.setPlainVariable((String) o);
		}
	}

	void parseAssignment(JSONArray ass, ContractCard c)
	{
		for (Iterator<Object> iter = ass.iterator(); iter.hasNext();)
		{
			Object o = iter.next();
			if (o instanceof String)
				c.setPlainAssignment((String) o);
		}
	}

	/*void parseConstraint(JSONArray ass, ContractCard c)
	{
		for (Iterator<Object> iter = ass.iterator(); iter.hasNext();)
		{
			Object o = iter.next();
			if (o instanceof String)
				c.setPlainConstraint((String) o);
		}
	}*/

	private void parseResult(JSONArray ass, ContractCard c)
	{
		for (Iterator<Object> iter = ass.iterator(); iter.hasNext();)
		{
			Object o = iter.next();
			if (o instanceof JSONObject)
			{
				JSONObject obj = (JSONObject) o;
				Object eO = obj.get(Eval);
				Object tO = obj.get(Text);

				if ((eO instanceof String) && (tO instanceof String))
					c.addResult((String) eO, (String) tO);
			}
		}
	}

	String getStringValue(JSONObject jo, String key)
	{
		Object o = jo.get(key);
		if (o instanceof String)
			return (String) o;
		if (o instanceof Integer)
			return "" + (Integer) o;
		return null;
	}

	private ContractCard parseCard(JSONObject js)
	{
		ContractCard c = new ContractCard();
		for (Iterator<String> iter = js.keys(); iter.hasNext();)
		{
			String key = iter.next();
			if (key.equals(ID))
			{
				c.setID(getStringValue(js, key));
			} else if (key.equals(Text))
			{
				c.setPlainText(getStringValue(js, key));
			} else if (key.equals(Index))
			{
				c.setIndex(getStringValue(js, key));
				// c.setIndex(js.getString(key));
			} else if (key.equals(Multiplicity))
			{
				c.setMultiplicity(getStringValue(js, key));
			} else if (key.equals(Variable) || key.equals(Object))
			{
				JSONArray ass = js.getJSONArray(key);
				parseVariable(ass, c);
			} else if (key.equals(Assignment))
			{
				JSONArray ass = js.getJSONArray(key);
				parseAssignment(ass, c);
			} /*else if (key.equals(Constraint))
			{
				JSONArray ass = js.getJSONArray(key);
				parseConstraint(ass, c);
			} */else if (key.equals(Tatbestand))
			{
				JSONArray ass = js.getJSONArray(key);
				parseResult(ass, c);
			}
			// System.out.println("" + key + " " + val);
		}
		return c;
	}
}
