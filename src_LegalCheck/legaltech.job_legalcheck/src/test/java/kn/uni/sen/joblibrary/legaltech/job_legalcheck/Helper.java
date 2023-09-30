package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

public class Helper
{
	static String compareLine(String line1, String line2)
	{
		String[] words1 = line1.split("\\s+");
		String[] words2 = line2.split("\\s+");
		int length = Integer.min(words1.length, words2.length);
		for (int i = 0; i < length; i++)
		{
			if (words1[i].compareTo(words2[i]) != 0)
			{
				String dif = "differs in words: " + words1[i] + " " + words2[i];
				return "line: " + line1 + "\n" + "line: " + line2 + "\n" + dif;
			}
		}
		if (words1.length != words2.length)
			return "line: " + line1 + "\n" + "line: " + line2 + "\n" + " differs in length.";
		return null;
	}

	/**
	 * Compares whether text1 and text2 are equivalent and, otherwise, returns
	 * an error description.
	 * 
	 * @param text1
	 * @param text2
	 * @return null or first word that differs.
	 */
	public static String compareText(String text1, String text2)
	{
		String[] lines1 = text1.split("\n");
		String[] lines2 = text2.split("\n");
		int length = Integer.min(lines1.length, lines2.length);
		for (int i = 0; i < length; i++)
		{
			String dif = compareLine(lines1[i], lines2[i]);
			if (dif != null)
				return dif;
		}
		if (lines1.length != lines2.length)
			return "Different number of lines";
		return null;
	}

	static List<String> getArray(String split, String text)
	{
		List<String> lines = new ArrayList<>();
		if (text == null)
			return lines;
		for (String s : text.split(split))
			lines.add(s);
		return lines;
	}

	static void sortList(List<String> list)
	{
		list.sort(new Comparator<>()
		{
			@Override
			public int compare(String t1, String t2)
			{
				return t1.compareTo(t2);
			}
		});
	}

	/**
	 * @param line1
	 * @param line2
	 * @return null when equivalent words are used
	 */
	static String compareLineWords(String line1, String line2)
	{
		String ret = null;
		List<String> words1 = getArray("\\s+", line1);
		List<String> words2 = getArray("\\s+", line2);
		if (words1.size() != words2.size())
			ret = "line: " + line1 + "\n" + "line: " + line2 + "\n" + " differs in length.";

		int length = Integer.min(words1.size(), words2.size());
		for (int i = 0; i < length; i++)
		{
			if (words1.get(i).compareTo(":named") == 0)
			{
				// ignore changes in assert names
				words1 = words1.subList(0, i);
				words2 = words1.subList(0, i);
				length = Integer.min(words1.size(), words2.size());
			}
		}

		sortList(words1);
		sortList(words2);
		for (int i = 0; i < length; i++)
		{
			if (words1.get(i).compareTo(words2.get(i)) != 0)
			{

				String dif = "differs in words: " + words1.get(i) + " " + words2.get(i);
				return "line: " + line1 + "\n" + "line: " + line2 + "\n" + dif;
			}
		}
		return ret;
	}

	/**
	 * Compares whether every line in text1 and text2 exists in the other text,
	 * otherwise, returns an error description.
	 * 
	 * @param text1
	 * @param text2
	 * @return null or first line that is missing.
	 */
	public static String compareLines(String text1, String text2)
	{
		List<String> lines1 = getArray("\n", text1);
		List<String> lines2 = getArray("\n", text2);

		sortList(lines1);
		sortList(lines2);

		int length = Integer.min(lines1.size(), lines2.size());
		for (int i = 0; i < length; i++)
		{
			String line1 = lines1.get(i);
			String line2 = lines2.get(i);
			String dif = compareLineWords(line1, line2);
			if (dif != null)
				return dif;
		}
		if (lines1.size() != lines2.size())
			return "Different number of lines";
		return null;
	}
}
