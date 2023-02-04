package kn.uni.sen.joblibrary.legaltech.web.run;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import org.springframework.scheduling.annotation.Async;

import kn.uni.sen.joblibrary.legaltech.cards.Contract;
import kn.uni.sen.joblibrary.legaltech.cards.ContractCard;
import kn.uni.sen.joblibrary.legaltech.cards.ContractParser;
import kn.uni.sen.joblibrary.legaltech.cards.ContractSaver;
import kn.uni.sen.joblibrary.legaltech.html.HtmlCreator_ContractInput;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.Job_LegalCheck;
//import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlAnalysisContractMinMax;
import kn.uni.sen.joblibrary.legaltech.uml_analysis.UmlResultState;
import kn.uni.sen.jobscheduler.common.impl.JobDataInput;
import kn.uni.sen.jobscheduler.common.impl.JobEventStatus;
import kn.uni.sen.jobscheduler.common.model.EventHandler;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.model.JobState;
import kn.uni.sen.jobscheduler.common.model.ResourceInterface;
import kn.uni.sen.jobscheduler.common.resource.ResourceDescription;
import kn.uni.sen.jobscheduler.common.resource.ResourceDouble;
import kn.uni.sen.jobscheduler.common.resource.ResourceEnum;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFileXml;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;
import kn.uni.sen.jobscheduler.common.resource.ResourceString;
import kn.uni.sen.jobscheduler.core.impl.JobRunAbstract;
import kn.uni.sen.jobscheduler.core.model.JobScheduler;

public class JobRun_Contract extends JobRunAbstract implements Runnable
{
	Contract contract = new Contract();
	Contract bricks = null;
	Job job = null;
	ResourceString Result = null;
	ResourceInterface Result2 = null;
	boolean isResult = false;
	boolean running = false;
	ResourceFile analyzeFile = null;
	LegalLogger logger = new LegalLogger(1000);
	LegalLogger logger2 = new LegalLogger(1000);

	public JobRun_Contract(Integer runID, EventHandler handler, ResourceFolder folder)
	{
		super(runID, handler, folder);
		eventHandler.subscribe(logger);
	}

	@Override
	public void run()
	{
		logEventStatus(JobEvent.INFO, "--------------------");
		runAnalyzeModel();
	}

	@Override
	protected JobScheduler createScheduler(ResourceFileXml jobFile, ResourceFolder folder, String schedulerType)
	{
		return null;
	}

	public boolean hasBrick()
	{
		return bricks != null;
	}

	public void parseBricks(URL url)
	{
		StringBuilder build = new StringBuilder();
		try
		{
			Scanner s = new Scanner(url.openStream());
			while (s.hasNextLine())
				build.append(s.nextLine());
		} catch (IOException e)
		{
			logEventStatus(JobEvent.ERROR, "Url could not be loaded " + url);
			return;
		}
		ContractParser parser = new ContractParser(this);
		bricks = parser.parseText(build.toString());
	}

	void addCard(int idx1, int idx2)
	{
		List<ContractCard> l = bricks.getCardList();
		if (l.size() < idx2 - 1)
			return;

		ContractCard c = l.get(idx2 - 1);
		ContractCard c2 = new ContractCard(c);
		c2.setContract(contract);
		contract.addCard(idx1, null, c2);
	}

	void removeCard(int idx1)
	{
		List<ContractCard> l = contract.getCardList();
		idx1--;
		if ((idx1 < 0) || (l.size() < idx1 - 1))
			return;
		l.remove(idx1);
	}

	void hideCard(int idx1)
	{
		List<ContractCard> l = contract.getCardList();
		idx1--;
		if ((idx1 < 0) || (l.size() < idx1 - 1))
			return;
		ContractCard c = l.get(idx1);
		if (c == null)
			return;
		if (c.isHidden())
			c.setHide(false);
		else
			c.setHide(true);
	}

	void switchCard(int idx1, int idx2)
	{
		List<ContractCard> l = contract.getCardList();
		idx1--;
		idx2--;
		if ((idx1 < 0) || (l.size() < idx1 - 1))
			return;
		if ((idx2 < 0) || (l.size() < idx2 - 1))
			return;

		ContractCard c = l.get(idx1);
		ContractCard c2 = l.get(idx2);
		l.set(idx1, c2);
		l.set(idx2, c);
	}

	public void changeCard(String value)
	{
		String[] ss = value.split("_");
		if (ss.length < 2)
			return;

		int idx1 = Integer.parseInt(ss[1]);
		int idx2 = 0;
		if (ss.length >= 3)
			idx2 = Integer.parseInt(ss[2]);
		if ("add".equals(ss[0]))
		{
			addCard(idx1, idx2);
		} else if ("remove".equals(ss[0]))
		{
			removeCard(idx1);
		} else if ("hide".equals(ss[0]))
		{
			hideCard(idx1);
		} else if ("switch".equals(ss[0]))
		{
			switchCard(idx1, idx2);
		}
	}

	public void parseContract(ResourceFile file)
	{
		if (!!!file.exists())
			return;
		ContractParser parser = new ContractParser(this);
		contract = null;
		contract = parser.parseFile(file.getData());
	}

	public void saveContract(ResourceFile file)
	{
		ContractSaver saver = new ContractSaver();
		String val = saver.saveFile(contract, file.getData());
		if (val != null)
			logEventStatus(JobEventStatus.ERROR, val);
	}

	public void saveContractText(ResourceFile fileR)
	{
		if ((fileR == null) || (contract == null))
			return;
		String text = contract.getCardText();
		text = text.replace("<br/>", "\n");
		fileR.writeText2File(text);
	}

	public void setValue(String variable, String value)
	{
		if (contract == null)
			return;
		int index = variable.indexOf(".");
		if (index == -1)
			return;
		ContractCard card = contract.getCardById(variable.substring(0, index));
		if (card == null)
			return;
		if (value.startsWith("_"))
			value = "$" + value.substring(1);
		String rest = variable.substring(index + 1);
		card.setVariableAssignment(rest, value);
	}

	@Async("threadPoolTaskExecutor")
	public void analyzeContract(ResourceFile fileR)
	{
		if (running)
			return;

		running = true;
		analyzeFile = fileR;
		Thread thread = new Thread(this);
		thread.start();
	}

	void runAnalyzeModel()
	{
		job = new Job_LegalCheck(this);
		if (analyzeFile == null)
		{
			String path = ResourceFolder.appendFolder(job.getFolderText(), "contractAna.json");
			ResourceFolder.createFolder(job.getFolderText());
			analyzeFile = new ResourceFile(path);
			saveContract(analyzeFile);
		}

		JobDataInput inData = new JobDataInput();
		inData.add(Job_LegalCheck.CONTRACT_FILE, analyzeFile);
		// job.setEventHandler(eventHandler);
		job.addLogger(logger);

		ResourceDescription.setOwner(job.getInputDescription(), inData);
		if (job != null)
			job.start();
		isResult = true;
		analyzeFile = null;
		running = false;
		logEventStatus(JobEvent.INFO, "end");
	}

	public JobEvent getNextEvent()
	{
		if (logger == null)
			return null;
		return logger.getNextEvent();
	}

	synchronized public String getNextResult()
	{
		if (!!!isResult)
			return null;

		if (Result2 != null)
		{
			// return of several result values
			ResourceInterface res = Result2;
			Result2 = Result2.getNext();
			return getResultValue(res);
		}

		ResourceString res = null;
		if (Result == null)
		{
			// get first Result intance
			Result = job.getResourceWithType(Job_LegalCheck.ANA_RESULT, true);
			res = Result;
		} else
			res = Result.getNextByType();
		if (res == null)
		{
			if (job.getJobState() == JobState.FINISHED)
			{
				// stop checking for results
				isResult = false;
				Result = null;
			}
			return null;
		}

		// check whether another analysis finished
		Result = res;
		Result2 = res.getChild();
		return "------------------<br/>" + res.getData();
	}

	private String getResultValue(ResourceInterface res)
	{
		if (res == null)
			return null;
		if (res instanceof ResourceEnum)
		{
			ResourceEnum s = (ResourceEnum) res;
			if (Job_LegalCheck.RESULT_KIND.equals(s.getName()))
			{
				if (UmlResultState.ERROR.name().equals(s.getData()))
					return "&#x1F6A9;";
				if (UmlResultState.WARNING.name().equals(s.getData()))
					return "&#x26A0;";
				if (UmlResultState.GOOD.name().equals(s.getData()))
					return "&#x2705;";
			}
		}
		if (res instanceof ResourceString)
		{
			ResourceString s = (ResourceString) res;
			if (Job_LegalCheck.SEQUENCE.equals(s.getName()))
			{
				return getSequenceDiagram(s.getData());
			} else if (Job_LegalCheck.UNSAT_CORE.equals(s.getName()))
			{
				return getUnsatCore(s.getData());
			} else if (Job_LegalCheck.MINMAX.equals(s.getName()))
			{
				return parseMinMax(s.getData());
			}
			return s.getData();
		}
		return null;
	}

	private String getCard(String var)
	{
		int idx = var.indexOf("_");
		if (idx < 0)
			return null;
		return var.substring(0, idx);
	}

	private String getUnsatCore(String data)
	{
		String[] buf = data.split(",");
		Set<ContractCard> list = new HashSet<>();
		String text = "";
		for (String s : buf)
		{
			String card = getCard(s);
			ContractCard c = contract.getCardById(card);
			if (c == null)
				continue;
			if (list.contains(c))
				continue;
			list.add(c);
			text += "<td valign='top'><b>" + c.getID() + ":</b><br/>" + c.getCardText() + "</td>";
		}

		String table = "<table class='unsat'><tr>";
		if (list.size() > 0)
		{
			int size = 100 / list.size();
			for (int i = 0; i < list.size(); i++)
				table += "<col style='width:" + size + "%'>";
		}
		return table + text + "</tr></table>";
	}

	class Variable
	{
		String name = null; // name of variable
		double min = Float.NaN;
		double val = Float.NaN;
		double max = Float.NaN;
		String name2 = null; // name in GUI
	};

	List<Variable> varList = null;

	private String parseMinMax(String data)
	{
		varList = new ArrayList<>();
		String[] list = data.split("\n");
		for (String val : list)
		{
			String[] vals = val.split(",");
			if (vals.length < 5)
				continue;
			Variable var = new Variable();
			var.name = vals[0];
			var.val = ResourceDouble.parseStringDouble(vals[1]);
			var.min = ResourceDouble.parseStringDouble(vals[2]);
			var.max = ResourceDouble.parseStringDouble(vals[3]);
			var.name2 = vals[4];
			varList.add(var);
		}
		return data.replace("\n", "</br>");
	}

	int diagramCounter = 1;

	private String getSequenceDiagram(String data)
	{
		if ((data == null) || (data.isEmpty()))
			return "";
		int id = diagramCounter++;
		String text = "<div id='diagram" + id + "'></div><script>\n" + "var d = Diagram.parse(\"" + data + "\");\n"
				+ "var options = {theme : 'simple'};" + "d.drawSVG('diagram" + id + "', options);" + "</script>";
		return text;
	}

	synchronized void runAnalyzeModelMinMax(ResourceDouble vars)
	{
		job = new Job_LegalCheck(this);
		if (analyzeFile == null)
		{
			String path = ResourceFolder.appendFolder(job.getFolderText(), "contractAna.json");
			ResourceFolder.createFolder(job.getFolderText());
			analyzeFile = new ResourceFile(path);
			saveContract(analyzeFile);
		}

		ResourceString ana = null; //todo: new ResourceString(UmlAnalysisContractMinMax.Name);

		JobDataInput inData = new JobDataInput();
		inData.add(Job_LegalCheck.CONTRACT_FILE, analyzeFile);
		inData.add(Job_LegalCheck.ANALYSEN, ana);
		if (vars != null)
		{
			inData.add(Job_LegalCheck.VALUES, vars);
		}
		job.addLogger(logger);

		ResourceDescription.setOwner(job.getInputDescription(), inData);
		if (job != null)
			job.start();
		isResult = true;
		analyzeFile = null;
		running = false;
		logEventStatus(JobEvent.INFO, "end");
	}

	public void wait4List()
	{
		// wait for results but at most 5 seconds
		for (int i = 0; i < 50; i++)
		{
			try
			{
				TimeUnit.MILLISECONDS.sleep(100);
			} catch (InterruptedException e)
			{
				e.printStackTrace();
			}
			if (varList != null)
				return;
		}
	}

	public String getParasHtml(List<String> vars)
	{
		if (contract == null)
			return "Missing Contract";
		ResourceDouble varR = parseVars(vars);
		// if ((varList == null) || (varR != null))
		{
			varList = null;
			runAnalyzeModelMinMax(varR);
			wait4List();
			if (varList == null)
				return "Missing Parameters of Contract. Load Contract?";
		}
		// List<> paraList = contract.getParameter(LegalUml.DateS);
		String text = "<tr><th>Name</th><th>Choose Day</th><th>Value</th><th>Use Value?</th></tr>";
		int i = 0;
		for (Variable var : varList)
		{
			i++;
			text += "<tr><td>";

			String name = var.name2;
			if (name.isEmpty())
				name = var.name;

			text += name + "</td><td>";
			if ((var.min == Float.NaN) || (var.max == Float.NaN))
				continue;

			int on = hasNext(varR, var.name) ? 1 : 0;

			text += var.min;
			text += "<input id='var" + i + "' type='range' min='" + var.min + "' max='" + var.max + "' value='"
					+ var.val + "' onchange='changeRangeVal(this)'>";
			text += var.max + "</td><td>";
			text += "<input type='text' name='" + var.name + "' style='width:50px' id='var" + i
					+ "_value' readonly value = '" + var.val + "'/></td><td>";
			text += "<input id='var" + i + "_on' style='width:40px' type='range' min='0' max='1' value='" + on + "'"
					+ "onchange='changeValOn(this)'>";
			text += "</td></tr>";
		}

		text += "<tr><td></td><td></td><td></td>";
		text += "<td><input type='button' value='Simulate' onclick='fire_ajax_getParas()' ></input></td></tr>";

		return "<form><table>" + text + "</table></form>";
	}

	private boolean hasNext(ResourceDouble varR, String name)
	{
		while (varR != null)
		{
			if (name.equals(varR.getName()))
				return true;
			varR = varR.getNextByType();
		}
		return false;
	}

	private ResourceDouble parseVars(List<String> vars)
	{
		ResourceDouble first = null;
		if (vars == null)
			return null;
		ResourceDouble rest = first;
		for (int i = 0; i < vars.size(); i += 2)
		{
			String name = vars.get(i);
			String val = vars.get(i + 1);
			if ((name == null) || name.isEmpty() || (val == null) || val.isEmpty())
				continue;

			ResourceDouble var = new ResourceDouble();
			var.setName(name);
			var.setDataValue(val);
			if (first == null)
			{
				first = var;
				rest = first;
			} else
				rest.addNext(var);
		}
		return first;
	}

	public String getContractHtml()
	{
		return (new HtmlCreator_ContractInput(true, true)).getContractHtml(contract, bricks);
	}
}
