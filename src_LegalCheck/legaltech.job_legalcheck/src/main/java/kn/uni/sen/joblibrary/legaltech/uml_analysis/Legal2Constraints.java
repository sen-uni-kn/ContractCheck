package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.w3c.dom.Element;

import kn.uni.sen.joblibrary.legaltech.job_legalcheck.LegalVisitor;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlModel2;
import kn.uni.sen.joblibrary.legaltech.job_legalcheck.UmlNode2;
import kn.uni.sen.joblibrary.legaltech.parser.model.LegalUml;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtElement;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtModel;
import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;

/**
 * Encoding of an legal contract in SMT. This is the core of the legal SMT
 * encoding.
 * 
 * @author Martin Koelbl (C) 2023
 * 
 */
public class Legal2Constraints extends LegalVisitor
{
	LegalEncodingContext context;

	public Legal2Constraints(UmlAnalysisListener ana, Job job)
	{
		super(job);
		context = new LegalEncodingContext(ana, job);
	}

	public static final String owner = "owner";
	public static final String registration = "registration";

	Map<Element, UmlAnnotation> map = new HashMap<>();
	SmtModel smtModel = new SmtModel();
	// SmtElement closingDate;

	// function owner uses uninterpreted functions
	// to ensure single owner exists.
	SmtDeclare ownerFunc = null;
	// function reg uses uninterpreted functions
	// to store known registrations
	SmtDeclare regFunc = null;

	// create soft constraints if true
	boolean withSoft = true;

	// limit check for the current claim
	boolean limit_check;

	Map<Element, SmtDeclare> varMap = new HashMap<>();
	Map<Element, SmtDeclare> triggerMap = new HashMap<>();
	Map<Element, SmtDeclare> dueMap = new HashMap<>();
	Map<Element, SmtDeclare> claimDateMap = new HashMap<>();
	Map<Element, SmtDeclare> limitMap = new HashMap<>();
	Map<Element, SmtDeclare> personMap = new HashMap<>();
	Map<Element, SmtDeclare> thingMap = new HashMap<>();

	// stores claims that are need but not traversed
	List<Element> tmpClaimList = new LinkedList<>();

	static String getCorrectedName(String n)
	{
		if (n == null)
			return null;
		n = n.replace("ö", "oe");
		n = n.replace("ä", "ae");
		n = n.replace("ü", "ue");
		n = n.replace("Ö", "Oe");
		n = n.replace("Ä", "Ae");
		n = n.replace("Ü", "Ue");
		return n.replaceAll("[^a-zA-Z0-9_]", "");
	}

	static boolean isClaimPrimary(UmlNode2 claim)
	{
		return claim.isOfClass(LegalUml.PrimaryClaim);
	}

	static boolean isClaimWarranty(UmlNode2 claim)
	{
		boolean sec = claim.inheritatesFrom(LegalUml.SecondaryClaim);
		String f1 = claim.getAttributeValue(LegalUml.WarrantyCondition);
		UmlNode2 f2 = claim.getAssoziationByName(LegalUml.WarrantyCondition);
		boolean is_wc = (f1 != null && !!!f1.isBlank()) || (f2 != null);
		return sec && is_wc;
	}

	static boolean isClaimConsequence(UmlNode2 claim)
	{
		UmlNode2 trig = claim.getAssoziationByName(LegalUml.Trigger);
		return (trig != null) && !!!isClaimPrimary(claim);
		//return !isClaimWarranty(claim) && !isClaimPrimary(claim);
	}
	
	static boolean isIndemnity(UmlNode2 claim)
	{
		return claim.inheritatesFrom(LegalUml.Indemnity);
	}

	void createDefault()
	{
		ownerFunc = smtModel.addDeclaration(new SmtDeclare("fun", owner, "(Int) Int"));
		regFunc = smtModel.addDeclaration(new SmtDeclare("fun", registration, "(Int) Bool"));
	}

	SmtDeclare createVariable(UmlNode2 cn, String nameD)
	{
		String type = cn.getNodeName();
		return createVariable(cn, type, varMap, nameD);
	}

	SmtDeclare getDateOfMap(UmlNode2 cn, Map<Element, SmtDeclare> map)
	{
		return map.get(cn.getElement());
	}

	SmtDeclare createDate(UmlNode2 cn, Map<Element, SmtDeclare> map, String extra)
	{
		String name = null;
		if (extra != null)
			name = cn.getName() + "_" + extra;
		return createVariable(cn, LegalUml.DateS, map, name);
	}

	SmtDeclare createVariable(UmlNode2 cn, String type, Map<Element, SmtDeclare> map, String nameDefault)
	{
		SmtDeclare decl = getDateOfMap(cn, map);
		if (decl != null)
			// variable was already created
			return decl;

		String name;
		if ((nameDefault != null) && !!!nameDefault.isEmpty())
			name = nameDefault;
		else
			name = cn.getName();
		if ((name == null) || name.isEmpty())
		{
			context.reportWarning("Missing name in claim " + name);
			return null;
		}

		if (LegalUml.DateS.equals(type))
		{
			decl = new SmtDeclare("const", "Date_" + name, "Int");
			decl = smtModel.addDeclaration(decl);
		} else if (LegalUml.IntegerS.equals(type))
		{
			decl = new SmtDeclare("const", "Int_" + name, "Int");
			decl = smtModel.addDeclaration(decl);
		} else if (LegalUml.BoolS.equals(type))
		{
			decl = new SmtDeclare("const", "Bool_" + name, "Bool");
			decl = smtModel.addDeclaration(decl);
		} else if (LegalUml.RealS.equals(type))
		{
			decl = new SmtDeclare("const", "Real_" + name, "Real");
			decl = smtModel.addDeclaration(decl);
		} else
		{
			context.reportError("Unkown type " + type);
		}

		if (decl == null)
		{
			context.reportWarning("Error SMT Encoding: Type " + type + " is unkown");
			return null;
		}
		map.put(cn.getElement(), decl);
		return decl;
	}

	protected void visitProperty(Element ele)
	{
		encodeOwnership(createNode(ele));
	}

	private void encodeOwnership(UmlNode2 prop)
	{
		List<UmlNode2> pers = prop.getAssoziationsByName(LegalUml.Owner);
		List<UmlNode2> gegens = prop.getAssoziationsByName(LegalUml.Property);

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

		SmtConstraint as = smtModel.createAssert(getCorrectedName(prop.getName()), 5);
		SmtConstraint wert = new SmtConstraint("=");
		as.addConstraint(wert);
		wert.addConstraint(new SmtConstraint("(" + ownerFunc.getName() + " " + itemDec.getName() + ")"))
				.addConstraint(perDec);
	}

	@Override
	protected void visitRegistration(Element ele)
	{
		encodeRegistration(createNode(ele));
	}

	private void encodeRegistration(UmlNode2 node)
	{
		SmtDeclare perDec = personMap.get(node.getElement());

		if (perDec == null)
		{
			System.out.println("Error: missing " + node.getName() + " " + node.getID());
			return;
		}

		SmtConstraint as = smtModel.createAssert(getCorrectedName(node.getName()), 4);
		SmtConstraint eq = new SmtConstraint("=");
		as.addConstraint(eq);
		eq.addConstraint(new SmtConstraint("(" + regFunc.getName() + " " + perDec.getName() + ")"))
				.addConstraint(new SmtConstraint("true"));
	}

	@Override
	protected void visitPrimaryClaim(Element ele)
	{
		super.visitPrimaryClaim(ele);
	}

	@Override
	protected void visitClaim(Element ele)
	{
		// 1. create claim date
		SmtDeclare decl = constraintClaimDate(createNode(ele));
		// 2. create performance
		createPerformance(createNode(ele), decl);
		// 3. either claim or a consequence occurs.
		combineConsequenceClaims(createNode(ele));

		tmpClaimList.remove(ele);
		super.visitClaim(ele);
	}

	private SmtElement encodeTriggerFormula(UmlNode2 claim, UmlNode2 trigger)
	{
		UmlNode2 trigNode = claim.getAssoziationByName(LegalUml.Trigger);
		if (isClaimWarranty(trigger))
		{
			if (claim == trigger)
			{
				context.reportError("Claim equals to its trigger.");
				return null;
			}

			if (trigNode != null)
			{
				return getClaimDueDate(trigger);
			}
			return null;
		}
		SmtElement ele = getClaimDueDate(trigger);
		return ele;
	}

	protected SmtElement getTriggerDate(UmlNode2 claim)
	{
		SmtElement triggerDate = getDateOfMap(claim, triggerMap);
		if (triggerDate != null)
			// dueData already exists
			return triggerDate;
		UmlNode2 trigNode = claim.getAssoziationByName(LegalUml.Trigger);
		if (trigNode == null)
			return null;
		SmtElement conTrigger = encodeTriggerFormula(claim, trigNode);
		if (conTrigger == null)
			// claim has no trigger
			return null;
		triggerDate = createDate(claim, triggerMap, "trigger");
		String name1 = claim.getName();
		SmtConstraint ass = smtModel.createAssert("trigger_" + name1, 1);
		SmtConstraint plus = new SmtConstraint("+");
		plus.addConstraint(conTrigger);
		plus.addConstraint(new SmtConstraint("1"));

		SmtConstraint con = new SmtConstraint("=");
		con.addConstraint(triggerDate);
		con.addConstraint(plus);
		ass.addConstraint(con);
		return triggerDate;
	}

	protected SmtElement getClaimDueDate(UmlNode2 claim)
	{
		SmtElement dueDate = getDateOfMap(claim, dueMap);
		if (dueDate != null)
			// dueData already exists
			return dueDate;

		dueDate = createDate(claim, dueMap, "due");
		SmtElement triggerDate = getTriggerDate(claim);
		if (triggerDate == null)
			// claim is a primary claim
			triggerDate = new SmtConstraint("0");

		SmtConstraint dueVal = encodeDueDateCondition(claim, triggerDate);
		SmtElement conDue = dueVal;
		if (conDue == null)
			conDue = triggerDate;
		String name1 = claim.getName();
		SmtConstraint ass = smtModel.createAssert("due_" + name1, 6);
		SmtConstraint con = new SmtConstraint("=");
		ass.addConstraint(con);
		con.addConstraint(dueDate);
		con.addConstraint(conDue);
		return dueDate;
	}

	private SmtConstraint encodeFormula(UmlNode2 formNode)
	{
		if (formNode.inheritatesFrom(LegalUml.IntegerS) || formNode.inheritatesFrom(LegalUml.DateS)
				|| formNode.inheritatesFrom(LegalUml.BoolS))
		{
			String val = formNode.getContent();
			if (val.isBlank())
			{
				String xmlName = formNode.getName();
				SmtDeclare decl = createVariable(formNode, xmlName);
				return new SmtConstraint(decl.getName());
			}
			return new SmtConstraint(val);
		}

		String opVal = formNode.getAttributeValue(LegalUml.Operator);
		UmlNode2 op1 = formNode.getAssoziationByName(LegalUml.Op1);
		UmlNode2 op2 = formNode.getAssoziationByName(LegalUml.Op2);
		if (opVal == null)
		{
			context.reportError("Operator is missing in formula!");
			return null;
		}
		opVal = opVal.replaceAll("==", "=");
		if (op1 == null)
		{
			context.reportError("Op1 is missing in formula!");
			return null;
		}
		if (op2 == null)
		{
			context.reportError("Op2 is missing in formula!");
			return null;
		}

		SmtConstraint op = new SmtConstraint(opVal);
		return op.addConstraint(encodeFormula(op1)).addConstraint(encodeFormula(op2));
	}

	private SmtConstraint encodeDueDateCondition(UmlNode2 claim, SmtElement triggerDate)
	{
		String val = claim.getAttributeValue(LegalUml.DueDate);
		if (val != null)
		{
			try
			{
				Float.parseFloat(val);
				return new SmtConstraint(val);
			} catch (Exception e)
			{
				context.reportWarning("" + val + " is not a number!");
			}
			return null;
		}

		UmlNode2 dueDate = claim.getAssoziationByName(LegalUml.DueDate);
		if (dueDate == null)
		{
			dueDate = claim.getAssoziationByName(LegalUml.Trigger);
		}
		if ((dueDate != null) && dueDate.isOfClass(LegalUml.DateS))
		{
			SmtElement ele = encodeFormula(dueDate);
			return new SmtConstraint(ele.toText());
		} else if ((dueDate != null) && dueDate.inheritatesFrom(LegalUml.Formula))
		{
			SmtConstraint con = encodeFormula(dueDate);
			String conText = con.toText();
			if ((triggerDate != null) && (conText != null) && conText.startsWith("(+"))
				con.addConstraint(triggerDate);
			return con;
		}
		return null;
	}

	private SmtConstraint getLimitation(UmlNode2 claim, SmtElement dueDate)
	{
		if (claim == null)
			return null;

		String val = claim.getAttributeValue(LegalUml.Limitation);
		if (val != null)
		{
			try
			{
				Float.parseFloat(val);
				return new SmtConstraint(val);
			} catch (Exception e)
			{
				context.reportWarning("" + val + " is not a number!");
			}
		}

		UmlNode2 form = claim.getAssoziationByName(LegalUml.Limitation);
		if (form != null)
			return encodeFormula(form);
		return null;
	}

	protected SmtElement getClaimLimitation(UmlNode2 claim, SmtElement triggerDate, SmtElement dueDate)
	{
		if (claim.inheritatesFrom(LegalUml.PrimaryClaim))
		{
			return getLimitation(claim, dueDate);
		} else if (triggerDate == null)
		{
			// claim has no trigger
			return getLimitation(claim, null);
		}

		SmtConstraint limitCon = getLimitation(claim, dueDate);
		if (limitCon == null)
			return null;

		SmtElement dutyCon = null;
		if (isClaimWarranty(claim))
		{
			// warranty becomes due on the trigger date
			dutyCon = dueDate;
		} else
		{
			dutyCon = triggerDate;
		}

		String name1 = claim.getName();
		SmtElement limitDate = createDate(claim, limitMap, "limit");
		SmtConstraint ass = smtModel.createAssert("due_" + name1, 7);
		SmtConstraint con = new SmtConstraint("=");
		ass.addConstraint(con);
		con.addConstraint(limitDate);

		if (dutyCon != null)
		{
			SmtConstraint plus = new SmtConstraint("+");
			plus.addConstraint(limitCon);
			limitCon = plus;
		}
		con.addConstraint(limitCon);
		return limitDate;
	}

	/**
	 * The occurrence of a claim is encoded by date_claim_event. Either the
	 * claim does not occur (=-1) or it occurs between due date and limitation.
	 * 
	 * @param claim
	 * @return
	 */
	protected SmtDeclare constraintClaimDate(UmlNode2 claim)
	{
		SmtDeclare claimDate = getDateOfMap(claim, claimDateMap);
		if (claimDate != null)
			// claimDate already exists
			return claimDate;

		// ensure that claim is processed
		tmpClaimList.add(claim.getElement());

		// create claim date
		claimDate = createDate(claim, claimDateMap, "event");
		if (claimDate == null)
			return null;
		SmtConstraint and = new SmtConstraint("and");
		// encode trigger if existing
		SmtElement triggerDate = getTriggerDate(claim);

		// encode due date
		SmtElement dueDate = getClaimDueDate(claim);
		if (dueDate != null)
		{
			// if(dc.inheritatesFrom(LegalUml.SecondaryClaim))
			if (triggerDate == null)
				and.addConstraint(new SmtConstraint("<=").addConstraint(dueDate).addConstraint(claimDate));
			else
				and.addConstraint(new SmtConstraint("<").addConstraint(dueDate).addConstraint(claimDate));
		}
		// encode limitation
		SmtElement limit = getClaimLimitation(claim, triggerDate, dueDate);
		if (limit != null && !limit_check)
			and.addConstraint(new SmtConstraint("<").addConstraint(claimDate).addConstraint(limit));

		// combine due date, claim date and limitation
		String name1 = claim.getName();
		SmtConstraint as2 = smtModel.createAssert(name1, 8);
		SmtConstraint or = new SmtConstraint("or");
		as2.addConstraint(or);
		or.addConstraint(new SmtConstraint("=").addConstraint(new SmtConstraint("-1")).addConstraint(claimDate));
		or.addConstraint(and);
		return claimDate;
	}

	private void createPerformance(UmlNode2 claim, SmtDeclare dec)
	{
		List<UmlNode2> asList1 = claim.getAssoziationsByName(LegalUml.Performance);
		List<UmlNode2> asList2 = claim.getAssoziationsByName(LegalUml.WarrantyCondition);
		asList1.addAll(asList2);

		for (UmlNode2 ass : asList1)
		{
			if (ass.inheritatesFrom(LegalUml.PropertyTransfer))
				createTransferCondition(ass, claim, dec);
			else if (ass.inheritatesFrom(LegalUml.Formula))
				createPerformanceFormula(ass, claim, dec);
			else
				createPerformanceCondition(ass, claim, dec);
		}
	}

	private void createTransferCondition(UmlNode2 transfer, UmlNode2 dc, SmtDeclare dec)
	{
		UmlNode2 von = transfer.getAssoziationByName(LegalUml.From);
		UmlNode2 g = transfer.getAssoziationByName(LegalUml.Property);
		UmlNode2 an = transfer.getAssoziationByName(LegalUml.To);

		if (von == null || g == null || an == null)
		{
			job.logEventStatus(JobEvent.WARNING, "" + transfer.getName() + " is missing an element");
			return;
		}

		SmtDeclare perDec = personMap.get(von.getElement());
		SmtDeclare thingDec = thingMap.get(g.getElement());

		if (thingDec == null)
		{
			System.out.println("Missing thing " + g.getName());
			return;
		}

		SmtConstraint as = smtModel.createAssert(getCorrectedName(transfer.getName()), 8);
		SmtConstraint con2 = new SmtConstraint("(" + ownerFunc.getName() + " " + thingDec.getName() + ")");
		SmtConstraint con = new SmtConstraint("=").addConstraint(con2).addConstraint(perDec);

		SmtConstraint decCon = new SmtConstraint("not").addConstraint(getClaimOccursConstraint(dc, dec));
		SmtConstraint or = new SmtConstraint("or").addConstraint(decCon).addConstraint(con);
		as.addConstraint(or);
	}

	private void createPerformanceFormula(UmlNode2 ass, UmlNode2 dc, SmtDeclare dec)
	{
		SmtConstraint as = smtModel.createAssert(getCorrectedName(ass.getName()), 8);
		SmtConstraint decCon = getClaimOccursConstraint(dc, dec);
		SmtConstraint conFormula = encodeFormula(ass);
		SmtConstraint or = null;
		if (Legal2Constraints.isClaimWarranty(dc))
		{
			// for warranties, either event==-1 then formula holds or event>=0
			// then formula does not hold
			or = new SmtConstraint("=").addConstraint(decCon).addConstraint(conFormula);
		} else
		{
			decCon = new SmtConstraint("not").addConstraint(decCon);
			or = new SmtConstraint("or").addConstraint(decCon).addConstraint(conFormula);
		}
		as.addConstraint(or);
	}

	private void createPerformanceCondition(UmlNode2 ass, UmlNode2 dc, SmtDeclare dec)
	{
		String val = dc.getAttributeValue(LegalUml.Performance);
		if (val == null)
			val = dc.getAttributeValue(LegalUml.WarrantyCondition);
		if ((val == null) || (val.isEmpty()))
			return;
		Pattern p = Pattern.compile("(.*?).transfer");
		Matcher m = p.matcher(val);

		// now try to find at least one match
		String thingVar = "";
		if (m.find())
		{
			thingVar = m.group(1).substring(1);
		} else
		{
			job.logEventStatus(JobEvent.WARNING, "Performance " + val + " is not encoded ");
			return;
		}

		UmlNode2 per = dc.getAssoziationByName(LegalUml.Debtor);
		if (per == null)
		{
			job.logEventStatus(JobEvent.ERROR, "Claim " + dc.getName() + " misses Debtor");
			return;
		}

		UmlNode2 thing = model.getNodeByName(thingVar);
		if (thing == null)
		{
			job.logEventStatus(JobEvent.ERROR, "Missing uml thing " + thingVar);
			return;
		}
		SmtDeclare thingDec = thingMap.get(thing.getElement());
		if (thingDec == null)
		{
			job.logEventStatus(JobEvent.ERROR, "Missing thing " + thingVar);
			return;
		}
		SmtDeclare perDec = personMap.get(per.getElement());
		if (perDec == null)
		{
			job.logEventStatus(JobEvent.ERROR, "Missing Person " + perDec);
			return;
		}

		SmtConstraint as = smtModel.createAssert(getCorrectedName(per.getName()), 8);
		SmtConstraint con2 = new SmtConstraint("(" + ownerFunc.getName() + " " + thingDec.getName() + ")");
		SmtConstraint con = new SmtConstraint("=").addConstraint(con2).addConstraint(perDec);

		SmtConstraint decCon = new SmtConstraint("not").addConstraint(getClaimOccursConstraint(dc, dec));
		SmtConstraint or = new SmtConstraint("or").addConstraint(decCon).addConstraint(con);
		as.addConstraint(or);
	}

	Set<UmlNode2> getTriggerSet(List<UmlNode2> claimList, UmlNode2 claim)
	{
		Set<UmlNode2> set = new HashSet<>();
		String name = claim.getName();
		for (UmlNode2 c : claimList)
		{
			List<UmlNode2> triggers = c.getAssoziationsByName(LegalUml.Trigger);
			if (triggers == null)
				continue;
			for (UmlNode2 t : triggers)
			{
				String val = t.getName();
				if (val == null)
					continue;
				if (val.contains(name))
					set.add(c);
			}
		}
		return set;
	}

	/**
	 * Either the primary/warranty claim or one of its consequences has to
	 * occur.
	 * 
	 * @param claim
	 *            primary/warranty claim
	 */
	protected void combineConsequenceClaims(UmlNode2 claim)
	{
		if (isClaimConsequence(claim) || isIndemnity(claim))
			// ignore consequence claims
			return;

		SmtElement claimEvent = constraintClaimDate(claim);
		List<UmlNode2> claims = model.getClassInstances(LegalUml.Claim);
		Set<UmlNode2> consequences = getTriggerSet(claims, claim);
		String eventName = claim.getName();

		SmtConstraint as = smtModel.createAssert(eventName, 9);
		SmtConstraint or = new SmtConstraint("or");
		as.addConstraint(or);
		or.addConstraint(getClaimOccursConstraint(claim, claimEvent));

		if (withSoft)
		{
			SmtConstraint asS = smtModel.createAssertSoft(null, 9);
			asS.addConstraint(getClaimOccursConstraint(claim, claimEvent));
		}

		for (UmlNode2 conClaim : consequences)
		{
			SmtElement conEvent = constraintClaimDate(conClaim);
			or.addConstraint(getClaimOccursConstraint(conClaim, conEvent));
			if (withSoft)
			{
				SmtConstraint asD = smtModel.createAssertSoft(null, 9);
				asD.addConstraint(getClaimPreventedConstraint(conClaim, conEvent));
			}
		}
	}

	protected SmtConstraint getClaimOccursConstraint(UmlNode2 claim, SmtElement claimEvent)
	{
		if (isClaimWarranty(claim))
			return new SmtConstraint("=").addConstraint(claimEvent).addConstraint(new SmtConstraint("-1"));
		return new SmtConstraint(">=").addConstraint(claimEvent).addConstraint(new SmtConstraint("0"));
	}

	protected SmtConstraint getClaimPreventedConstraint(UmlNode2 claim, SmtElement claimEvent)
	{
		if (isClaimWarranty(claim))
			return new SmtConstraint(">=").addConstraint(claimEvent).addConstraint(new SmtConstraint("0"));
		return new SmtConstraint("=").addConstraint(claimEvent).addConstraint(new SmtConstraint("-1"));
	}

	@Override
	protected void visitObject(Element ele)
	{
		UmlNode2 object = new UmlNode2(model, ele);
		addThingConstraint(model, object);
		super.visitObject(ele);
	}

	private void addThingConstraint(UmlModel2 model, UmlNode2 thing)
	{
		String name1 = getCorrectedName("Thing_" + thing.getName());
		if ((name1 == null) || (name1.isEmpty()))
			job.logEventStatus("Warning", "Missing name of Thing " + name1);

		SmtDeclare thi = smtModel.addDeclaration(new SmtDeclare("const", name1, "Int"));
		thingMap.put(thing.getElement(), thi);
		SmtConstraint as = smtModel.createAssert(getCorrectedName(thing.getName()), 5);
		as.addConstraint(
				new SmtConstraint("=").addConstraint(thi).addConstraint(new SmtConstraint("" + thingMap.size())));
	}

	@Override
	protected void visitPerson(Element ele)
	{
		addPersonConstraint(createNode(ele));
		super.visitPerson(ele);
	}

	protected UmlNode2 createNode(Element ele)
	{
		return new UmlNode2(model, ele);
	}

	private void addPersonConstraint(UmlNode2 person)
	{
		String name1 = getCorrectedName("Person_" + person.getName());
		if ((name1 == null) || (name1.isEmpty()))
			job.logEventStatus("Warning", "Missing name of Person " + name1);

		SmtDeclare pers = smtModel.addDeclaration(new SmtDeclare("const", name1, "Int"));
		personMap.put(person.getElement(), pers);
		SmtConstraint as = smtModel.createAssert(getCorrectedName(person.getName()), 4);
		as.addConstraint(
				new SmtConstraint("=").addConstraint(pers).addConstraint(new SmtConstraint("" + personMap.size())));
	}

	protected void visitContract(Element ele)
	{
		// closingDate = createDate(createNode(ele), dueMap, "closing");
		super.visitContract(ele);
	}

	public SmtModel generate(UmlModel2 model)
	{
		createDefault();
		visitModel(model);

		// create remaining claims that were not traversed
		while (!!!tmpClaimList.isEmpty())
			visitClaim(tmpClaimList.get(0));

		return smtModel;
	}
}
