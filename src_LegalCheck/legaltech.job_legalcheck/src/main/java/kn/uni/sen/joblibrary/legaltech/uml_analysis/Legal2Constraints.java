package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.HashMap;
import java.util.Map;

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

/**
 * Creates constraints for the legal elements.
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

	Map<Element, UmlAnnotation> map = new HashMap<>();
	SmtModel smtModel = new SmtModel();
	SmtElement closingDate;

	Map<Element, SmtDeclare> varMap = new HashMap<>();
	Map<Element, SmtDeclare> triggerMap = new HashMap<>();
	Map<Element, SmtDeclare> dueMap = new HashMap<>();
	Map<Element, SmtDeclare> claimDateMap = new HashMap<>();
	Map<Element, SmtDeclare> limitMap = new HashMap<>();
	Map<Element, SmtDeclare> personMap = new HashMap<>();
	Map<Element, SmtDeclare> thingMap = new HashMap<>();
	Map<Element, SmtDeclare> listDutyClaim = new HashMap<>();

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

	static boolean isClaimWarranty(UmlNode2 duty)
	{
		return duty.isOfClass(LegalUml.Warranty);
	}

	SmtDeclare createVariable(UmlNode2 cn, String nameD)
	{
		String type = cn.getNodeName();
		return createVariable(cn, type, varMap, nameD);
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
		SmtDeclare decl = map.get(cn.getElement());
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
		} else if (LegalUml.RealS.equals(type))
		{
			decl = new SmtDeclare("const", "Real_" + name, "Real");
			decl = smtModel.addDeclaration(decl);
		}
		if (decl == null)
		{
			context.reportWarning("Error SMT Encoding: Type " + type + " is unkown");
			return null;
		}
		map.put(cn.getElement(), decl);
		return decl;
	}

	protected void visitPrimaryClaim(Element ele)
	{
		super.visitPrimaryClaim(ele);
	}

	@Override
	protected void visitClaim(Element ele)
	{
		// 1. create claim date
		createClaimDate(createNode(ele));
		// 2. create children
		super.visitClaim(ele);
	}

	protected String getTrigger(UmlNode2 claim)
	{
		// todo: parse trigger formula
		return null;
	}

	protected SmtElement getTriggerDate(UmlNode2 claim)
	{
		String val = getTrigger(claim);
		if (val == null)
			return null;
		SmtConstraint conTrigger = new SmtConstraint(val);

		SmtElement triggerDate = createDate(claim, triggerMap, "trigger");
		String name1 = claim.getName();
		SmtConstraint ass = smtModel.createAssert("trigger_" + name1, 1);
		SmtConstraint con = new SmtConstraint("=");
		ass.addConstraint(con);
		con.addConstraint(triggerDate);
		con.addConstraint(conTrigger);
		return triggerDate;
	}

	protected String getDueDate(UmlNode2 duty)
	{
		if (duty == null)
			return null;
		String val = duty.getAttributeValue(LegalUml.DueDate);
		if (val != null)
		{
			if ((val.startsWith("+")) || (val.startsWith("(")))
			{
				context.reportWarning("todo: create due formula");
				return "todo: create due formula";
			}

			try
			{
				Float.parseFloat(val);
				return val;
			} catch (Exception e)
			{
				context.reportWarning("" + val + " is not a number!");
			}
		}
		return null;
	}

	protected SmtElement getClaimDueDate(UmlNode2 claim, SmtElement triggerDate)
	{
		SmtElement dueDate = createDate(claim, dueMap, "due");
		String dueVal = getDueDate(claim);
		SmtElement conDue = null;
		if (triggerDate == null)
		{
			// claim is a primary claim
			if ((dueVal != null) && !!!dueVal.isEmpty())
				conDue = new SmtConstraint(dueVal);
			conDue = new SmtConstraint("0");
		}

		if (isClaimWarranty(claim))
		{
			if (dueVal != null)
			{
				conDue = new SmtConstraint(dueVal);
			} else
				conDue = triggerDate;
		}
		String name1 = claim.getName();
		SmtConstraint ass = smtModel.createAssert("due_" + name1, 1);
		SmtConstraint con = new SmtConstraint("=");
		ass.addConstraint(con);
		con.addConstraint(dueDate);
		con.addConstraint(conDue);
		return dueDate;
	}

	public String getLimitation(UmlNode2 duty, SmtElement dueDate)
	{
		if (duty == null)
			return null;

		String val = duty.getAttributeValue(LegalUml.Limitation);
		if (val != null)
		{
			if ((val.startsWith("+")) || (val.startsWith("(")))
			{
				context.reportWarning("todo: create limitation formula");
				return "todo: create limitation formula";
			}

			try
			{
				Float.parseFloat(val);
				return val;
			} catch (Exception e)
			{
				context.reportWarning("" + val + " is not a number!");
			}
		}
		return null;
	}

	private SmtElement getClaimLimitation(UmlNode2 claim, SmtElement triggerDate, SmtElement dueDate)
	{
		if (claim.inheritatesFrom(LegalUml.PrimaryClaim))
		{
			String val = getLimitation(claim, dueDate);
			if ((val != null) && !!!val.isEmpty())
				return new SmtConstraint(val);
			return null;
		} else if (triggerDate == null)
		{
			// claim has no trigger
			String val = getLimitation(claim, null);
			if (val == null)
				return null;
			return new SmtConstraint(val);
		}

		String limit = getLimitation(claim, dueDate);
		if (limit == null)
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
		SmtConstraint ass = smtModel.createAssert("due_" + name1, 1);
		SmtConstraint con = new SmtConstraint("=");
		ass.addConstraint(con);
		con.addConstraint(limitDate);

		SmtConstraint limitCon = new SmtConstraint(limit);
		if (dutyCon != null)
		{
			SmtConstraint plus = new SmtConstraint("+");
			plus.addConstraint(limitCon);
			limitCon = plus;
		}
		con.addConstraint(limitCon);
		return limitDate;
	}

	private SmtElement createClaimDate(UmlNode2 claim)
	{
		// create claim date
		SmtElement claimDate = createDate(claim, claimDateMap, "event");
		if (claimDate == null)
			return null;
		SmtConstraint and = new SmtConstraint("and");
		// encode trigger if existing
		SmtElement triggerDate = getTriggerDate(claim);

		// encode due date
		SmtElement dueDate = getClaimDueDate(claim, triggerDate);
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
		if (limit != null)
			and.addConstraint(new SmtConstraint("<").addConstraint(claimDate).addConstraint(limit));

		// combine due date, claim date and limitation
		String name1 = claim.getName();
		SmtConstraint as2 = smtModel.createAssert(name1, 3);
		SmtConstraint or = new SmtConstraint("or");
		as2.addConstraint(or);
		or.addConstraint(new SmtConstraint("=").addConstraint(new SmtConstraint("-1")).addConstraint(claimDate));
		or.addConstraint(and);
		return claimDate;
	}

	@Override
	protected void visitObject(Element ele)
	{
		super.visitObject(ele);
	}

	@Override
	protected void visitPerson(Element ele)
	{
		addPersonConstraint(createNode(ele));
		super.visitPerson(ele);
	}

	private UmlNode2 createNode(Element ele)
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
		SmtConstraint as = smtModel.createAssert(getCorrectedName(person.getName()), 1);
		as.addConstraint(
				new SmtConstraint("=").addConstraint(pers).addConstraint(new SmtConstraint("" + personMap.size())));
	}

	protected void visitContract(Element ele)
	{
		closingDate = createDate(createNode(ele), dueMap, "closing");
		super.visitContract(ele);
	}

	public SmtModel generate(UmlModel2 model)
	{
		visitModel(model);
		return smtModel;
	}
}
