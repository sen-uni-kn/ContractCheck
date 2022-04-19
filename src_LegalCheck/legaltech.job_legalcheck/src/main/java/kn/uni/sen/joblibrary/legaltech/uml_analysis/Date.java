package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import kn.uni.sen.jobscheduler.common.resource.ResourceDouble;

public class Date implements Comparable<Date>
{
	public String Name = "";
	public float Value = Float.NaN;
	public float ValueMin = Float.NaN;
	
	public Date()
	{	
	}
	
	public Date(String name, String value)
	{
		Name = name;
		setValue(value);
	}

	@Override
	public int compareTo(Date d2)
	{
		return (int) (Value - d2.Value);
	}
	
	public void setValue(String val)
	{
		setValue((float)ResourceDouble.parseStringDouble(val));
	}

	public void setValue(float val)
	{
		// several values are found for min/max analysis
		if (!!!Float.isNaN(Value))
		{
			if (Value < val)
				ValueMin = Value;
			if (Value > val)
				return;
		}
		Value = val;
	}

	public String getValue()
	{
		if ((Value - (int) Value) != 0)
			return "" + Value;
		return "" + (int) Value;
	}

	public String getValueMin()
	{
		if ((ValueMin - (int) ValueMin) != 0)
			return "" + ValueMin;
		return "" + (int) ValueMin;
	}
}