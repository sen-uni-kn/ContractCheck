package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.FormulaParser;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;
import kn.uni.sen.jobscheduler.common.resource.ResourceFolder;

/**
 * An abstract class that generates a contract constraint system that encodes a
 * single execution of the contract and is modified for a concrete analysis
 * 
 * @author Martin Koelbl
 */
public abstract class UmlAnalysisContractAbstract extends UmlAnalysisSMTAbstract
{
	public UmlAnalysisContractAbstract(Job j, String name)
	{
		super(j, name);
	}

	// currenct context
	List<UmlNode2> registerList = new ArrayList<>();
	UmlModel2 model;
	Element contract;
	Element claim;

	SmtDeclare closingDate;
	Map<Element, SmtDeclare> varList = new HashMap<>();
	Map<Element, SmtDeclare> personMap = new HashMap<>();
	Map<Element, SmtDeclare> thingMap = new HashMap<>();
	Map<Element, SmtDeclare> listDutyClaim = new HashMap<>();
	List<SmtDeclare> schadenList = new ArrayList<>();

	public static final String owner = "owner";
	public static final String registration = "registration";

	UmlNode2 trigLimit = null;
	boolean withSoft = true;

	String statisticsFile;

	// function owner uses uninterpreted functions
	// to ensure single owner exists.
	SmtDeclare ownerFunc = null;
	// function reg uses uninterpreted functions
	// to store known registrations
	SmtDeclare regFunc = null;

	void clearModel()
	{
		varList.clear();
		personMap.clear();
		thingMap.clear();
		listDutyClaim.clear();
		schadenList.clear();
		smtModel = new SmtModel();
		SmtConstraint.Count = 0;
		ownerFunc = null;
		regFunc = null;
	}

	SmtDeclare createVariable(UmlModel2 model, UmlNode2 cn, String nameD)
	{
		SmtDeclare decl = varList.get(cn.getElement());
		if (decl != null)
			// variable was already created
			return decl;

		String name;
		if ((nameD != null) && !!!nameD.isEmpty())
			name = nameD;
		else
			name = cn.getName();
		if ((name == null) || name.isEmpty())
		{
			reportWarning("Missing name in claim " + name);
			return null;
		}

		String type = cn.getNodeName();
		if (LegalUml.DateS.equals(type))
		{
			decl = new SmtDeclare("const", "Date_" + name, "Int");
			decl = smtModel.addDeclaration(decl);
		} else if (LegalUml.IntegerS.equals(type))
		{
			decl = new SmtDeclare("const", "Int_" + name, "Int");
			decl = smtModel.addDeclaration(decl);
		} else if (LegalUml.RealS.equals(type))
		{
			decl = new SmtDeclare("const", "Real_" + name, "Real");
			decl = smtModel.addDeclaration(decl);
		}
		if (decl == null)
		{
			System.out.println("Error SMT Encoding: Type " + type + " is unkown");
			return null;
		}
		varList.put(cn.getElement(), decl);
		return decl;
	}

	// core function to generate the SMT code of a contract
	@Override
	public SmtModel createSMTCode(UmlModel2 model)
	{
		clearModel();
		this.model = model;
		// todo:
		// 1. add analysis
		// 2. traverse model and add semantic
		// 3. output model in smt
		createDefault();
		traverse(model);
		afterwards();
		return smtModel;
	}

	void createDefault()
	{
		ownerFunc = smtModel.addDeclaration(new SmtDeclare("fun", owner, "(Int) Int"));
		regFunc = smtModel.addDeclaration(new SmtDeclare("fun", registration, "(Int) Bool"));
	}

	@Override
	public void visitContract(Element ele)
	{
		this.contract = ele;

		// get closing date
		UmlNode2 contract = new UmlNode2(model, ele);
		UmlNode2 cn = contract.getAssoziationByName(LegalUml.Closing);
		closingDate = createVariable(model, cn, null);
		if (closingDate == null)
		{
			System.out.println("Error Closing of " + contract.getName() + " not created!");
		}
	}

	@Override
	public void leaveContract(Element ele)
	{
		contract = null;
	}

	@Override
	public void visitClaim(Element ele)
	{
		claim = ele;
		UmlNode2 claim = new UmlNode2(model, ele);
		addClaimConstraint(model, claim);
	}

	@Override
	public void leaveClaim(Element ele)
	{
		claim = null;
	}

	@Override
	public void visitPerson(Element ele)
	{
		UmlNode2 node = new UmlNode2(model, ele);
		String name = node.getName();
		// todo: use block + name
		for (Element key : personMap.keySet())
		{
			UmlNode2 n = new UmlNode2(model, key);
			String name2 = n.getName();
			if (name.equals(name2))
				return;
		}
		if (personMap.containsKey(ele))
			return;
		UmlNode2 person = new UmlNode2(model, ele);
		addPersonConstraint(model, person);
	}

	public void visitObject(Element ele)
	{
		UmlNode2 object = new UmlNode2(model, ele);
		addThingConstraint(model, object);
	}

	public void visitProperty(Element ele)
	{
		UmlNode2 property = new UmlNode2(model, ele);
		createEigentumConstraint(model, property, ownerFunc);
	}

	public void visitRegister(Element ele)
	{
		UmlNode2 register = new UmlNode2(model, ele);
		registerList.add(register);
	}

	public void visitPrice(Element ele)
	{
		UmlNode2 price = new UmlNode2(model, ele);
		createPreisConstraint(model, price);
	}

	// after everthing is parsed
	private void afterwards()
	{
		for (Element dc : listDutyClaim.keySet())
		{
			SmtDeclare c = listDutyClaim.get(dc);
			UmlNode2 node2 = new UmlNode2(model, dc);
			generateClaimDuty(model, node2, c);
		}

		List<UmlNode2> ownerShipList = model.getClassInstances(LegalUml.PropertyRight);
		for (UmlNode2 own : ownerShipList)
		{
			createEigentumConstraint(model, own, ownerFunc);
		}

		List<UmlNode2> regs = model.getClassInstances(LegalUml.Registration);
		createEintragungConstraint(model, regs, regFunc);

		// create preis variable
		List<UmlNode2> preiss = model.getClassInstances(LegalUml.Price);
		for (UmlNode2 p : preiss)
		{
			createPreisConstraint(model, p);
		}

		// ignore already encoded constraints
		Set<Element> consEncoded = new HashSet<>();
		// store encoded variables
		Set<Element> done = new HashSet<>();
		// while since varList can change during encoding
		while (varList.size() != done.size())
		{
			Set<Element> list = new HashSet<>(varList.keySet());
			list.removeAll(done);
			for (Element var : list)
			{
				done.add(var);
				createConstraints(model, var, consEncoded);
			}
		}
	}

	private SmtElement createFormula(UmlModel2 model, UmlNode2 form)
	{
		String type = form.getNodeName();
		if (LegalUml.Formula.equals(type))
		{
			UmlNode2 op1 = form.getAssoziationByName(LegalUml.Op1);
			SmtElement con1 = createFormula(model, op1);
			UmlNode2 op2 = form.getAssoziationByName(LegalUml.Op2);
			SmtElement con2 = createFormula(model, op2);
			String op = form.getAttributeValue(LegalUml.Operator);
			if ((op == null) || (con1 == null) || (con2 == null))
			{
				System.out.println("Error formula could not be parsed");
				return null;
			}
			SmtConstraint con = new SmtConstraint(op);
			con.addConstraint(con1).addConstraint(con2);
			return con;
		} else if (LegalUml.IntegerS.equals(type))
		{
			String val = form.getContent();
			return new SmtConstraint(val);
		} else if (LegalUml.RealS.equals(type))
		{
			String val = form.getContent();
			return new SmtConstraint(val);
		} else if (model.inheritatesFrom(type, LegalUml.Type))
		{
			SmtDeclare sd = createVariable(model, form, null);
			return sd;
		}
		System.out.println("Error unkown formula element");
		return null;
	}

	private void createConstraints(UmlModel2 model, Element ele, Set<Element> cons)
	{
		List<UmlNode2> list = model.getAssoziationsByName(ele, LegalUml.Constraint);
		for (UmlNode2 n : list)
		{
			Element ef = n.getElement();
			if ((ef == null) || cons.contains(ef))
				continue;
			cons.add(ef);
			SmtConstraint ass = smtModel.createAssert(LegalUml.Constraint + "_" + cons.size(), 4);
			SmtElement con = createFormula(model, n);
			if (con != null)
				ass.addConstraint(con);
		}
	}

	protected List<UmlNode2> getDuties2Generate(List<UmlNode2> duties)
	{
		return duties;
	}

	private void createEintragungConstraint(UmlModel2 model, List<UmlNode2> regList, SmtDeclare einFunc)
	{
		if (regList.isEmpty())
			return;

		SmtConstraint ass = smtModel.createAssert(LegalUml.Registration, 9);
		SmtConstraint and = new SmtConstraint("and");
		ass.addConstraint(and);
		// true is just added to ensure that create file is not failing because
		// of empty and
		and.addConstraint(new SmtConstraint("true"));

		List<UmlNode2> list = model.getClassInstances(LegalUml.LegalPerson);
		for (UmlNode2 ein : regList)
		{
			List<UmlNode2> attrs = ein.getAssoziationsByName(LegalUml.Person);
			if (attrs.isEmpty())
				continue;

			for (UmlNode2 p : attrs)
			{
				list.remove(p);
				SmtDeclare per = personMap.get(p.getElement());
				if (per == null)
					continue;
				SmtConstraint con = new SmtConstraint("=")
						.addConstraint(new SmtConstraint(einFunc.getName()).addConstraint(per))
						.addConstraint(new SmtConstraint("true"));
				and.addConstraint(con);
			}
		}
		for (UmlNode2 ein : list)
		{
			SmtDeclare per = personMap.get(ein.getElement());
			if (per == null)
				continue;
			SmtConstraint con = new SmtConstraint("=")
					.addConstraint(new SmtConstraint(einFunc.getName()).addConstraint(per))
					.addConstraint(new SmtConstraint("false"));
			and.addConstraint(con);
		}
	}

	private void createEigentumConstraint(UmlModel2 model, UmlNode2 eigen, SmtDeclare eigFunc)
	{
		List<UmlNode2> pers = eigen.getAssoziationsByName(LegalUml.Owner);
		List<UmlNode2> gegens = eigen.getAssoziationsByName(LegalUml.Property);

		if (pers.isEmpty() || gegens.isEmpty())
			return;

		UmlNode2 per = pers.get(0).checkReference();
		UmlNode2 thing = gegens.get(0).checkReference();

		if ((per == null) || (thing == null))
			return;

		SmtDeclare perDec = personMap.get(per.getElement());
		SmtDeclare itemDec = thingMap.get(thing.getElement());

		if (itemDec == null)
		{
			System.out.println("Error: missing " + thing.getName() + " " + thing.getID());
			return;
		}

		SmtConstraint as = smtModel.createAssert(getCorrectedName(eigen.getName()), 7);
		SmtConstraint wert = new SmtConstraint("=");
		as.addConstraint(wert);
		wert.addConstraint(new SmtConstraint("(" + eigFunc.getName() + " " + itemDec.getName() + ")"))
				.addConstraint(perDec);
	}

	private void createPreisConstraint(UmlModel2 model, UmlNode2 p)
	{
		String val = p.getAttributeValue(LegalUml.Price);
		if ((val == null) || (val.isEmpty()))
			return;

		SmtDeclare preis = smtModel.addDeclaration(new SmtDeclare("const", "Preis_" + p.getName(), "Int"));
		SmtDeclare anpas = smtModel.addDeclaration(new SmtDeclare("const", "Preis_Anpassung", "Int"));
		SmtConstraint ass = smtModel.createAssert(getCorrectedName(p.getName()), 7);

		SmtConstraint preisCon = new SmtConstraint(val.replace("€", ""));
		if (schadenList.isEmpty())
		{
			// no claim changes the price
			SmtConstraint con2 = new SmtConstraint("=").addConstraint(preis).addConstraint(preisCon);
			ass.addConstraint(con2);
			return;
		}

		// sum of all claims
		SmtConstraint sum = new SmtConstraint("+");
		SmtConstraint gl = new SmtConstraint("=").addConstraint(anpas).addConstraint(sum);
		for (SmtDeclare sch : schadenList)
			sum.addConstraint(sch);
		smtModel.createAssert("ClaimSum", 8).addConstraint(gl);

		// get min and max values
		SmtConstraint min = getAttributeConstraint(p, LegalUml.ChangeMin);
		SmtConstraint max = getAttributeConstraint(p, LegalUml.ChangeMax);

		// compute price - change of value
		SmtConstraint minC = null;
		if (min != null)
		{
			SmtConstraint m = new SmtConstraint("<").addConstraint(anpas).addConstraint(min);
			SmtConstraint s = new SmtConstraint("=").addConstraint(preis).addConstraint(preisCon);
			minC = new SmtConstraint("and").addConstraint(m).addConstraint(s);
		}
		SmtConstraint maxC = null;
		if (max != null)
		{
			SmtConstraint m = new SmtConstraint(">").addConstraint(anpas).addConstraint(max);
			SmtConstraint red = new SmtConstraint("-").addConstraint(preisCon).addConstraint(max);
			SmtConstraint s = new SmtConstraint("=").addConstraint(preis).addConstraint(red);
			maxC = new SmtConstraint("and").addConstraint(m).addConstraint(s);
		}
		SmtConstraint othC = new SmtConstraint("");
		{
			SmtConstraint mi = null;
			SmtConstraint ma = null;
			SmtConstraint red = new SmtConstraint("-").addConstraint(preisCon).addConstraint(anpas);
			SmtConstraint s = new SmtConstraint("=").addConstraint(preis).addConstraint(red);
			if (min != null)
				mi = new SmtConstraint(">=").addConstraint(anpas).addConstraint(min);
			if (max != null)
				ma = new SmtConstraint("<=").addConstraint(anpas).addConstraint(max);
			othC = new SmtConstraint("and").addConstraint(mi).addConstraint(ma).addConstraint(s);
		}
		SmtConstraint con2 = new SmtConstraint("or").addConstraint(minC).addConstraint(maxC).addConstraint(othC);
		ass.addConstraint(con2);
	}

	private void generateClaimDuty(UmlModel2 model, UmlNode2 dc, SmtDeclare c)
	{
		if (dc == null)
			return;

		// todo: implement other duties
		if (dc.inheritatesFrom(LegalUml.PrimaryClaim))
		{
			createSchuldverhaeltnis(model, dc, c);
		} else if (dc.inheritatesFrom(LegalUml.Warranty))
		{
			createSchuldverhaeltnis(model, dc, c);
		} else if (dc.inheritatesFrom(LegalUml.Supplementary))
		{
			createNacherfuellung(model, dc, c);
		} else if (dc.inheritatesFrom(LegalUml.Compensation))
		{
			createSchadensersatz(model, dc, c);
		} else if (dc.inheritatesFrom(LegalUml.Withdrawal))
		{
			createRuecktritt(model, dc, c);
		} else
			reportWarning("Duty or Claim " + dc.getName() + " without classifier.");
	}

	private void createNacherfuellung(UmlModel2 model, UmlNode2 dc, SmtDeclare c)
	{
		createRuecktritt(model, dc, c);
	}

	private void createRuecktritt(UmlModel2 model, UmlNode2 dc, SmtDeclare c)
	{
	}

	private void createSchuldverhaeltnis(UmlModel2 model, UmlNode2 dc, SmtDeclare dec)
	{
		List<UmlNode2> asss = dc.getAssoziationsByName(LegalUml.Performance);
		for (UmlNode2 ass : asss)
		{
			// List<UmlNode2> refs =
			// ass.getAssoziationsByClass(LegalUml.Eigentumsuebergang);
			// if (refs.isEmpty())
			// continue;
			// UmlNode2 ref = refs.get(0);
			if (ass.inheritatesFrom(LegalUml.PropertyTransfer))
				createUebergangBedingung(model, ass, dc, dec);
			else
				createPerformance(model, ass, dc, dec);
		}
		if (asss.size() != 0)
			// claim is not a warranty
			return;

		// below handle warranties
		List<UmlNode2> attrs = dc.getAssoziationsByName(LegalUml.Content);
		for (UmlNode2 attr : attrs)
		{
			String bed = attr.getAttributeValue("value");
			if ((bed == null) || (bed.isEmpty()))
				continue;

			// create Bedingungen
			// smtModel.addConstraint(new SmtConstraint(bed), 5);
			// System.out.println(bed);
			// todo: use other duties
			UmlNode2 ref = model.getNodeByName(bed);
			if (ref == null)
				ref = createNode(model, bed);

			if (ref != null)
			{
				if (ref.inheritatesFrom(LegalUml.PropertyTransfer))
					createUebergangBedingung(model, ref, dc, dec);
				else if (ref.inheritatesFrom(LegalUml.PropertyRight))
					createEigentumBedingung(model, ref, dc, dec);
				else if (ref.inheritatesFrom(LegalUml.Registration))
					createEintragungBedingung(model, ref, dc, dec);
			} else
			{
				SmtConstraint con = new FormulaParser().parseFormula(bed, smtModel);
				if (con == null)
					job.logEventStatus("Error", "Bedingung " + bed + " was not parsed");
				else
					createVerpflichtung(model, con, dc, dec);
			}
		}
	}

	private void createPerformance(UmlModel2 model, UmlNode2 ass, UmlNode2 dc, SmtDeclare dec)
	{
		String val = dc.getAttributeValue(LegalUml.Performance);
		if ((val == null) || (val.isEmpty()))
			return;

		Pattern p = Pattern.compile("(.*?).transfer");
		Matcher m = p.matcher(val);

		// now try to find at least one match
		String thingVar = "";
		if (m.find())
		{
			thingVar = m.group(1).substring(1);
			// System.out.println(thingVar);
		} else
		{
			reportWarning("Performance " + val + " is not encoded ");
			return;
		}

		UmlNode2 per = dc.getAssoziationByName(LegalUml.Debtor);
		if (per == null)
		{
			System.out.println("Claim " + dc.getName() + " misses Debtor");
			return;
		}

		UmlNode2 thing = model.getNodeByName(thingVar);
		if (thing == null)
		{
			System.out.println("Missing " + thingVar);
			return;
		}
		SmtDeclare thingDec = thingMap.get(thing.getElement());
		SmtDeclare perDec = personMap.get(per.getElement());

		SmtConstraint as = smtModel.createAssert(getCorrectedName(per.getName()), 7);
		SmtConstraint con2 = new SmtConstraint("(" + owner + " " + thingDec.getName() + ")");
		SmtConstraint con = new SmtConstraint("=").addConstraint(con2).addConstraint(perDec);

		SmtConstraint decCon = new SmtConstraint("not").addConstraint(getDutyConstraint(model, dc, dec));
		SmtConstraint or = new SmtConstraint("or").addConstraint(decCon).addConstraint(con);
		as.addConstraint(or);

		// System.out.println(val);
	}

	private void createVerpflichtung(UmlModel2 model, SmtConstraint con, UmlNode2 dc, SmtDeclare dec)
	{
		SmtConstraint date = getDutyConstraint(model, dc, dec);
		SmtConstraint notDate = new SmtConstraint("not").addConstraint(date);
		SmtConstraint and = new SmtConstraint("and").addConstraint(date).addConstraint(con);
		SmtConstraint or = new SmtConstraint("or").addConstraint(notDate).addConstraint(and);
		smtModel.createAssert(getCorrectedName(dc.getName()), 7).addConstraint(or);
	}

	private UmlNode2 createNode(UmlModel2 model, String bed)
	{
		String[] ss = bed.split("[(,)]");
		if (ss == null)
			return null;
		UmlNode2 node = null;
		Element cl = null;
		for (int i = 0; i < ss.length; i++)
		{
			String s = ss[i];
			// System.out.println(s);
			if (i == 0)
			{
				cl = model.getClassElement(s);
				if (cl == null)
				{
					job.logEventStatus("Warning", "Missing class in" + bed);
					return null;
				}
				Element ele = model.createElement(s, s);
				node = new UmlNode2(model, ele);
			} else
			{
				String[] as = s.split("=");
				if (as.length != 2)
					continue;
				as[0] = as[0].replace(" ", "");
				as[1] = as[1].replace(" ", "");

				node.setAttributeValue(as[0], as[1]);
			}
		}
		return node;
	}

	private void createUebergangBedingung(UmlModel2 model, UmlNode2 ueber, UmlNode2 dc, SmtDeclare dec)
	{
		UmlNode2 von = ueber.getAssoziationByName(LegalUml.From);
		UmlNode2 g = ueber.getAssoziationByName(LegalUml.Property);
		UmlNode2 an = ueber.getAssoziationByName(LegalUml.To);

		if (von == null || g == null || an == null)
		{
			job.logEventStatus(JobEvent.WARNING, "" + ueber.getName() + " is missing an element");
			return;
		}

		SmtDeclare perDec = personMap.get(von.getElement());
		SmtDeclare thingDec = thingMap.get(g.getElement());

		if (thingDec == null)
		{
			System.out.println("Missing thing " + g.getName());
			return;
		}

		// String vonN = getCorrectedName(von);
		// String gN = getCorrectedName(g);
		// String anN = getCorrectedName(an);

		SmtConstraint as = smtModel.createAssert(getCorrectedName(ueber.getName()), 7);
		SmtConstraint con2 = new SmtConstraint("(" + owner + " " + thingDec.getName() + ")");
		SmtConstraint con = new SmtConstraint("=").addConstraint(con2).addConstraint(perDec);

		SmtConstraint decCon = new SmtConstraint("not").addConstraint(getDutyConstraint(model, dc, dec));
		SmtConstraint or = new SmtConstraint("or").addConstraint(decCon).addConstraint(con);
		as.addConstraint(or);
	}

	private void createEigentumBedingung(UmlModel2 model, UmlNode2 eit, UmlNode2 dc, SmtDeclare dec)
	{
		// check eigentümer is eigentümer of Eigentum
		List<UmlNode2> pers = eit.getAssoziationsByName(LegalUml.Owner);
		List<UmlNode2> things = eit.getAssoziationsByName(LegalUml.Property);

		if (pers.isEmpty() || things.isEmpty())
			return;

		String idP1 = pers.get(0).getName();
		String idI1 = things.get(0).getName();

		UmlNode2 per = model.getNodeByName(idP1);
		UmlNode2 item = model.getNodeByName(idI1);

		if ((per == null) || (item == null))
			return;

		SmtDeclare perDec = personMap.get(per.getElement());
		SmtDeclare thingDec = thingMap.get(item.getElement());
		SmtConstraint con2 = new SmtConstraint("(" + owner + " " + thingDec.getName() + ")");
		SmtConstraint con = new SmtConstraint("=").addConstraint(con2).addConstraint(perDec);

		SmtConstraint dutyCon = getDutyConstraint(model, dc, dec);
		SmtConstraint decCon = new SmtConstraint("not").addConstraint(dutyCon);
		SmtConstraint or = new SmtConstraint("or").addConstraint(decCon).addConstraint(con);
		smtModel.createAssert(getCorrectedName(eit.getName()), 7).addConstraint(or);
	}

	@Deprecated
	private void createEintragungBedingung(UmlModel2 model, UmlNode2 eit, UmlNode2 dc, SmtDeclare dec)
	{
		// check Eintragung exists for Person eit
		String p1 = eit.getAttributeValue(LegalUml.Person);
		if (p1.isEmpty())
			return;

		UmlNode2 per = model.getNodeByName(p1);
		if (per == null)
			return;

		SmtDeclare perDec = personMap.get(per.getElement());
		SmtConstraint con2 = new SmtConstraint("(eintragung " + perDec.getName() + ")");
		SmtConstraint con = new SmtConstraint("=").addConstraint(con2).addConstraint(new SmtConstraint("true"));

		SmtConstraint decCon = new SmtConstraint("not").addConstraint(getDutyConstraint(model, dc, dec));
		SmtConstraint or = new SmtConstraint("or").addConstraint(decCon).addConstraint(con);
		smtModel.createAssert(getCorrectedName(eit.getName()), 7).addConstraint(or);
	}

	String getAttributeValue(UmlNode2 dc, String name)
	{
		String val = dc.getAttributeValue(name);
		if (val != null)
			return val;
		return null;
	}

	String getAttributeValueCorrected(UmlNode2 dc, String name)
	{
		String val = getAttributeValue(dc, name);
		if (val != null)
		{
			val = getCorrectedName(val);
			if (val != null)
				return val;
		}
		return null;
	}

	SmtConstraint getAttributeConstraint(UmlNode2 dc, String name)
	{
		String val = getAttributeValueCorrected(dc, name);
		if (val != null)
			return new SmtConstraint(val);
		return null;
	}

	private void createSchadensersatz(UmlModel2 model, UmlNode2 dc, SmtDeclare c)
	{
		SmtDeclare sch = smtModel.addDeclaration(new SmtDeclare("const", "Schaden_" + dc.getName(), "Int"));
		// helper variable to store real damage
		SmtDeclare sch2 = smtModel.addDeclaration(new SmtDeclare("const", "Schaden2_" + dc.getName(), "Int"));
		SmtConstraint as2 = smtModel.createAssert(getCorrectedName(dc.getName()), 6);
		SmtConstraint gr = new SmtConstraint(">=").addConstraint(sch).addConstraint(new SmtConstraint("0"));
		as2.addConstraint(gr);

		SmtConstraint min = getAttributeConstraint(dc, LegalUml.Min);
		SmtConstraint max = getAttributeConstraint(dc, LegalUml.Max);

		SmtConstraint schFunc = parseFormula(getAttributeValue(dc, LegalUml.Damage));
		if (schFunc == null)
			return;
		schadenList.add(sch); // damage to pay

		{
			// no claim -> no damage to pay
			SmtConstraint and1 = new SmtConstraint("and");
			SmtConstraint noC = new SmtConstraint("=").addConstraint(c).addConstraint(new SmtConstraint("-1"));
			SmtConstraint nix = new SmtConstraint("=").addConstraint(sch2).addConstraint(new SmtConstraint("0"));
			and1.addConstraint(noC).addConstraint(nix);

			// claim -> damage to pay
			SmtConstraint and2 = new SmtConstraint("and");
			SmtConstraint ein = new SmtConstraint(">=").addConstraint(c).addConstraint(new SmtConstraint("0"));
			SmtConstraint schC2 = new SmtConstraint("=").addConstraint(sch2).addConstraint(schFunc);
			and2.addConstraint(ein).addConstraint(schC2);

			SmtConstraint as = smtModel.createAssert(getCorrectedName(dc.getName()), 6);
			SmtConstraint or = new SmtConstraint("or");
			as.addConstraint(or);
			or.addConstraint(and1).addConstraint(and2);
		}

		// compute damage to pay
		SmtConstraint notC = null;
		{
			notC = new SmtConstraint("and");
			notC.addConstraint(new SmtConstraint("=").addConstraint(c).addConstraint(new SmtConstraint("-1")));
			notC.addConstraint(new SmtConstraint("=").addConstraint(sch).addConstraint(new SmtConstraint("0")));
		}

		SmtConstraint minC = null;
		if (min != null)
		{
			SmtConstraint m = new SmtConstraint("<").addConstraint(sch2).addConstraint(min);
			SmtConstraint s = new SmtConstraint("=").addConstraint(sch).addConstraint(new SmtConstraint("0"));
			minC = new SmtConstraint("and").addConstraint(m).addConstraint(s);
		}
		SmtConstraint maxC = null;
		if (max != null)
		{
			SmtConstraint m = new SmtConstraint(">").addConstraint(sch2).addConstraint(max);
			SmtConstraint s = new SmtConstraint("=").addConstraint(sch).addConstraint(max);
			maxC = new SmtConstraint("and").addConstraint(m).addConstraint(s);
		}
		SmtConstraint othC = new SmtConstraint("");
		{
			SmtConstraint mi = null;
			SmtConstraint ma = null;
			SmtConstraint s = new SmtConstraint("=").addConstraint(sch).addConstraint(sch2);

			if (min != null)
				mi = new SmtConstraint(">=").addConstraint(sch2).addConstraint(min);
			if (max != null)
				ma = new SmtConstraint("<=").addConstraint(sch2).addConstraint(max);
			othC = new SmtConstraint("and").addConstraint(mi).addConstraint(ma).addConstraint(s);
		}

		SmtConstraint as3 = smtModel.createAssert(getCorrectedName(dc.getName()), 6);
		SmtConstraint or2 = new SmtConstraint("or");
		as3.addConstraint(or2);
		or2.addConstraint(notC).addConstraint(minC).addConstraint(maxC).addConstraint(othC);
	}

	private SmtConstraint parseFormula(String val)
	{
		if ((val == null) || val.isEmpty())
			return null;

		SmtConstraint con = new FormulaParser().parseFormula(val, smtModel);
		if (con == null)
			reportError("Error with parsing formula:" + val);
		return con;
	}

	private void addPersonConstraint(UmlModel2 model, UmlNode2 person)
	{
		String name1 = getCorrectedName("Person_" + person.getName());
		if ((name1 == null) || (name1.isEmpty()))
			job.logEventStatus("Warning", "Missing name of Person " + name1);

		SmtDeclare pers = smtModel.addDeclaration(new SmtDeclare("const", name1, "Int"));
		personMap.put(person.getElement(), pers);
		SmtConstraint as = smtModel.createAssert(getCorrectedName(person.getName()), 1);
		as.addConstraint(
				new SmtConstraint("=").addConstraint(pers).addConstraint(new SmtConstraint("" + personMap.size())));
	}

	private void addThingConstraint(UmlModel2 model, UmlNode2 thing)
	{
		String name1 = getCorrectedName("Thing_" + thing.getName());
		if ((name1 == null) || (name1.isEmpty()))
			job.logEventStatus("Warning", "Missing name of Thing " + name1);

		SmtDeclare thi = smtModel.addDeclaration(new SmtDeclare("const", name1, "Int"));
		thingMap.put(thing.getElement(), thi);
		SmtConstraint as = smtModel.createAssert(getCorrectedName(thing.getName()), 2);
		as.addConstraint(
				new SmtConstraint("=").addConstraint(thi).addConstraint(new SmtConstraint("" + thingMap.size())));
	}

	boolean isDutyGarantie(UmlNode2 duty)
	{
		return duty.isOfClass(LegalUml.Warranty);
	}

	public String getFormulaDueDate(UmlModel2 model, UmlNode2 duty, String val)
	{
		if (val.startsWith("("))
			return val;

		String start = null;
		UmlNode2 node = duty.getAssoziationByName(LegalUml.Trigger);
		if (isDutyGarantie(node))
		{
			if (node != null)
			{
				SmtDeclare c = listDutyClaim.get(node.getElement());
				if (c != null)
					start = c.getName();
			}
		} else
			start = getDueDate(model, node);

		val = val.replace("+", "");
		if ((start != null) && (!!!start.isEmpty()))
			return "(+ " + start + " " + " " + val + ")";
		return val;
	}

	public String getDueDate(UmlModel2 model, UmlNode2 duty)
	{
		if (duty == null)
			return null;
		String val = duty.getAttributeValue(LegalUml.DueDate);
		if (val != null)
		{
			if ((val.startsWith("+")) || (val.startsWith("(")))
				return getFormulaDueDate(model, duty, val);

			try
			{
				Float.parseFloat(val);
				return val;
			} catch (Exception e)
			{
				reportWarning("" + val + " is not a number!");
			}
		}
		return null;
	}

	public String getFormulaLatest(UmlModel2 model, UmlNode2 duty, String val, SmtElement min)
	{
		if (val.startsWith("("))
			return val;

		String start = null;
		if (min != null)
			start = min.toText();
		if ((start == null) || start.isEmpty())
			start = "0";

		val = val.replace("+", "");
		if ((start != null) && (!!!start.isEmpty()))
			return "(+ " + start + " " + " " + val + ")";
		return val;
	}

	public String getLimitation(UmlModel2 model, UmlNode2 duty, SmtElement min)
	{
		if (duty == null)
			return null;

		String val = duty.getAttributeValue(LegalUml.Limitation);
		if (val != null)
		{
			if ((val.startsWith("+")) || (val.startsWith("(")))
				return getFormulaLatest(model, duty, val, min);

			try
			{
				Float.parseFloat(val);
				return val;
			} catch (Exception e)
			{
				reportWarning("" + val + " is not a number!");
			}
		}
		return null;
	}

	protected SmtElement getClaimDateMin(UmlModel2 model, UmlNode2 claim, UmlNode2 duty)
	{
		if (claim == null)
			return new SmtConstraint("0");
		if (claim.inheritatesFrom(LegalUml.PrimaryClaim) || (duty == null))
		// if (duty == null)
		{
			// claim is a duty (primary claim)
			String val = getDueDate(model, claim);
			if ((val != null) && !!!val.isEmpty())
				return new SmtConstraint(val);
			return new SmtConstraint("0");
		}

		if (isDutyGarantie(duty))
		{
			String val = getDueDate(model, claim);
			if (val != null)
			{
				SmtConstraint con = new SmtConstraint(val);
				return con;
			}
			return listDutyClaim.get(duty.getElement());
		}

		String val = getDueDate(model, duty);
		if (val == null)
			return closingDate;
		return new SmtConstraint(val);
	}

	private SmtElement getClaimDateMax(UmlModel2 model, UmlNode2 claim, UmlNode2 duty, SmtElement min)
	{
		if (claim.inheritatesFrom(LegalUml.PrimaryClaim))
		{
			String val = getLimitation(model, claim, min);
			if ((val != null) && !!!val.isEmpty())
				return new SmtConstraint(val);
			return null;
		} else if (duty == null)
		{
			// claim has no trigger
			String val = getLimitation(model, claim, min);
			if (val == null)
				return null;
			return new SmtConstraint(val);
		}

		String claimFrist = getLimitation(model, claim, min);
		if (claimFrist == null)
			return null;

		SmtElement dutyCon = null;
		if (isDutyGarantie(duty))
		{
			// Date garantieverletzung ist datum der Verletzung
			dutyCon = listDutyClaim.get(duty.getElement());
		} else
		{
			String frist = getDueDate(model, duty);
			if (frist == null)
				dutyCon = closingDate;
			else
				dutyCon = new SmtConstraint(frist);
		}

		SmtConstraint claim2 = getNachClaim(model, claim, duty);

		SmtConstraint claimCon = new SmtConstraint(claimFrist);
		if ((dutyCon == null) && (claim2 == null))
			return claimCon;
		SmtConstraint plus = new SmtConstraint("+");
		// .addConstraint(dutyCon);
		if (dutyCon != null)
			plus.addConstraint(claimCon);
		// if (claim2 != null)
		// plus.addConstraint(claim2);
		return plus;
	}

	private SmtConstraint getNachClaim(UmlModel2 model, UmlNode2 claim, UmlNode2 duty)
	{
		if (!!!claim.inheritatesFrom(LegalUml.Compensation))
			return null;

		List<UmlNode2> nL = duty.getAssoziationsByName(LegalUml.Consequence);
		for (UmlNode2 n : nL)
		{
			if (!!!n.inheritatesFrom(LegalUml.Supplementary))
				continue;
			String frist = getDueDate(model, n);
			if (frist != null)
				return new SmtConstraint(frist);
		}
		return null;
	}

	private SmtDeclare createDutyClaim(UmlModel2 model, UmlNode2 dc, UmlNode2 duty)
	{
		UmlNode2 ed = dc.getAssoziationByName(LegalUml.EventDate);
		SmtDeclare dutyFunc = createVariable(model, ed, dc.getName());
		if (dutyFunc == null)
			return null;
		SmtConstraint and = new SmtConstraint("and");
		SmtElement min = getClaimDateMin(model, dc, duty);
		if (min != null)
		{
			// if(dc.inheritatesFrom(LegalUml.SecondaryClaim))
			if (duty == null)
				and.addConstraint(new SmtConstraint("<=").addConstraint(min).addConstraint(dutyFunc));
			else
				and.addConstraint(new SmtConstraint("<").addConstraint(min).addConstraint(dutyFunc));
		}
		SmtElement max = getClaimDateMax(model, dc, duty, min);
		if ((trigLimit != null) && (dc.getElement() == trigLimit.getElement()))
			// ignore Limitation of trigger in Limitation Analysis
			; // System.out.println("ignore Limit");
		else if (max != null)
			and.addConstraint(new SmtConstraint("<").addConstraint(dutyFunc).addConstraint(max));
		// else if ((min != null) && (duty == null))
		// and.addConstraint(new
		// SmtConstraint("<=").addConstraint(dutyFunc).addConstraint(min));

		String name1 = dutyFunc.getName();
		SmtConstraint as2 = smtModel.createAssert(name1, 3);
		SmtConstraint or = new SmtConstraint("or");
		as2.addConstraint(or);
		or.addConstraint(new SmtConstraint("=").addConstraint(new SmtConstraint("-1")).addConstraint(dutyFunc));
		or.addConstraint(and);
		return dutyFunc;
	}

	private void addClaimConstraint(UmlModel2 model, UmlNode2 duty)
	{
		String name = duty.getAttributeValue("Name");
		if (name == null)
			name = duty.getName();
		List<UmlNode2> claims = model.getClassInstances(LegalUml.Claim);
		Set<UmlNode2> consequences = getTriggerSet(claims, duty);
		List<UmlNode2> bedList = duty.getAssoziationsByName(LegalUml.Performance);
		if (bedList.size() <= 0)
		{
			reportWarning("Missing Performance in Claim " + name);
			// return;
		} else if (bedList.size() >= 2)
			reportWarning("Several attributes Performance in Claim " + name);

		// if (claims.isEmpty())
		// reportWarning("Missing claims for Duty " + duty.getName());

		SmtDeclare dutyFunc = createDutyClaim(model, duty, null);
		listDutyClaim.put(duty.getElement(), dutyFunc);
		String eventName = dutyFunc.getName();
		SmtConstraint as = smtModel.createAssert(eventName, 4);
		SmtConstraint or = new SmtConstraint("or");
		as.addConstraint(or);
		or.addConstraint(getDutyConstraint(model, duty, dutyFunc));

		if (withSoft)
		{
			SmtConstraint asS = smtModel.createAssertSoft(null, 4);
			asS.addConstraint(getDutyConstraint(model, duty, dutyFunc));
		}

		for (UmlNode2 claim : consequences)
		{
			SmtDeclare clFunc = createDutyClaim(model, claim, duty);
			listDutyClaim.put(claim.getElement(), clFunc);
			or.addConstraint(new SmtConstraint(">=").addConstraint(clFunc).addConstraint(new SmtConstraint("0")));
			if (withSoft)
			{
				if ((trigLimit != null) && (claim.getElement() == trigLimit.getElement()))
					// ignore soft-assert of trigger in Limitation Analysis
					continue; // System.out.println("ignore Limit");

				SmtConstraint asD = smtModel.createAssertSoft(null, 4);
				asD.addConstraint(new SmtConstraint("<").addConstraint(clFunc).addConstraint(new SmtConstraint("0")));
			}
		}
	}

	protected SmtConstraint getDutyConstraint(UmlModel2 model, UmlNode2 duty, SmtDeclare dutyFunc)
	{
		if (isDutyGarantie(duty))
			return new SmtConstraint("=").addConstraint(dutyFunc).addConstraint(new SmtConstraint("-1"));
		return new SmtConstraint(">=").addConstraint(dutyFunc).addConstraint(new SmtConstraint("0"));
	}

	public String getStatisticFile()
	{
		return statisticsFile;
	}

	public void setStatisticFile(String file)
	{
		statisticsFile = file;
	}

	// used to output metadata (runtime, memory, ...) of analysis
	void log()
	{
		if (statisticsFile == null)
		{
			statisticsFile = ResourceFolder.appendFolder(job.getFolderText(), "statistics.txt");
			ResourceFile.removeFile(statisticsFile);
			String head = "name & time & mem & constraints & variables\\\\\n";
			ResourceFile.appendText2File(statisticsFile, head);
		}

		String fullName = anaName + name;
		String text = fullName + " & " + timeZ3 + "s & " + memZ3 + "MB & " + constraintCount + " & " + varCount
				+ "\\\\\n";
		ResourceFile.appendText2File(statisticsFile, text);
	}
}
