package kn.uni.sen.joblibrary.legaltech.parser.model;

/**
 * legal UML model and its key words in english
 * todo: use only the UML meta-model of a contract in legal.xsd
 * 
 * @author Martin Koelbl
 */
public class LegalUml
{
	static UmlModel model = null;

	public static final String StringS = "String";
	public static final String TextS = "Text";
	public static final String IntegerS = "Integer";
	public static final String FloatS = "Float";
	public static final String BooleanS = "Bool";
	public static final String DateS = "Date";
	public static final String Name = "Name";
	public static final String SPA = "SPA";
	public static final String Person = "Person";
	public static final String LegalPerson = "LegalPerson";
	public static final String NaturalPerson = "NaturalPerson";
	public static final String Corporation = "Corporation";
	public static final String Claim = "Claim";
	public static final String Latest = "Latest";
	public static final String Claim2 = "Claim2";
	public static final String Warranty = "WarrantyClaim";
	public static final String IndirectOwner = "IndirectOwner";
	public static final String Price = "Price";
	public static final String DueDate = "DueDate";
	public static final String Function = "Function";
	public static final String Head = "Head";
	public static final String Head2 = "Head2";
	public static final String Registration = "Registration";
	public static final String Property = "Property";
	public static final String PropertyTransfer = "PropertyTransfer";
	public static final String Owner = "Owner";
	public static final String Compensation = "CompensationClaim";
	public static final String Supplementary = "PerformanceClaim";
	public static final String PurchasePrice = "PurchasePrice";
	public static final String Object = "Object";
	public static final String Thing = "Thing";
	public static final String Limitation = "Limitation";
	public static final String Right = "Right";
	//public static final String Regelung = "Regelung";
	public static final String Share = "Share";
	public static final String PrimaryClaim = "PrimaryClaim";
	public static final String Debtor = "Debtor";
	public static final String Creditor = "Creditor";
	public static final String SecondaryClaim = "SecondaryClaim";
	public static final String Withdrawal = "RestitutionClaim";
	public static final String Content = "Content";
	public static final String Closing = "Closing";
	public static final String Signing = "Signing";
	public static final String PurchaseObject = "Object";
	public static final String PropertyRight = "PropertyRight";
	public static final String From = "From";
	public static final String To = "To";
	public static final String Min = "Min";
	public static final String Max = "Max";
	public static final String Damage = "Damage";
	public static final String ChangeMin = "ChangeMin";
	public static final String ChangeMax = "ChangeMax";
	public static final String Seller = "Seller";
	public static final String Amount = "Amount";
	public static final String Trigger = "Trigger";
	public static final String Purchaser = "Purchaser";
	public static final String Reference = "Reference";
	//public static final String Tatbestand = "Tatbestand";
	public static final String Performance = "Performance";
	public static final String FactTextG = "TextPerformed";
	public static final String FactTextB = "TextBreached";
	public static final String FactEval = "Eval";
	public static final String Item = "Item";
	public static final String Indemnity = "IndemnityClaim";
	public static final String Legal = "Legal";
	public static final String Consequence = "Trigger";
	public static final String Depend = "Depend";
	public static final String Integer = "Integer";
	public static final String EventDate = "Event";

	public static final String Clause = "Clause";
	public static final String Clause1 = "Clause1";
	public static final String Clause2 = "Clause2";
	public static final String Clause3 = "Clause3";

	public static final String Constraint = "Constraint";

	public static final String Type = "Type";

	public static void addClasses(UmlModel model)
	{
		//this is outdated since the model in the file legal.xsd is used
		if (model == null)
			return;
		int counter = 1;
		
		UmlNode legalObject = new UmlNode("class" + counter++, Legal);

		// basic types
		UmlNode stringN = new UmlNode("class" + counter++, StringS);
		model.addNode(stringN);

		UmlNode integerN = new UmlNode("class" + counter++, IntegerS);
		model.addNode(integerN);

		UmlNode boolN = new UmlNode("class" + counter++, BooleanS);
		model.addNode(boolN);

		UmlNode date = new UmlNode("class" + counter++, DateS);
		model.addNode(date);

		UmlNode function = new UmlNode("class" + counter++, Function);
		model.addNode(function);

		// contract structure in surface
		UmlNode head = new UmlNode("class" + counter++, Head);
		head.addInheritate(stringN);
		model.addNode(head);

		UmlNode head2 = new UmlNode("class" + counter++, Head2);
		head.addInheritate(stringN);
		model.addNode(head2);

		UmlNode clause = new UmlNode("class" + counter++, Clause);
		head.addInheritate(stringN);
		//clause.addAttribute(new UmlAttribute(Item, Item, stringN));
		//clause.addAttribute(new UmlAttribute(TextS, TextS, stringN));
		addAssociation(clause, Clause, clause);
		addAssociation(clause, Legal, legalObject);
		model.addNode(clause);

		UmlNode clause1 = new UmlNode("class" + counter++, Clause1);
		clause1.addInheritate(clause);
		model.addNode(clause1);
		
		UmlNode clause2 = new UmlNode("class" + counter++, Clause2);
		clause2.addInheritate(clause);
		model.addNode(clause2);

		UmlNode clause3 = new UmlNode("class" + counter++, Clause3);
		clause3.addInheritate(clause);
		model.addNode(clause3);

		// contract elements
		UmlNode person = new UmlNode("class" + counter++, Person);
		person.addInheritate(legalObject);
		person.addAttribute(new UmlAttribute(Name, Name, stringN));
		model.addNode(person);

		UmlNode personN = new UmlNode("class" + counter++, NaturalPerson);
		personN.addInheritate(legalObject);
		personN.addInheritate(person);
		personN.addAttribute(new UmlAttribute(Name, Name, stringN));
		model.addNode(personN);
		
		UmlNode eintrag = new UmlNode("class" + counter++, Registration);
		eintrag.addInheritate(legalObject);
		model.addNode(eintrag);

		UmlNode personJ = new UmlNode("class" + counter++, LegalPerson);
		personJ.addInheritate(legalObject);
		personJ.addInheritate(person);
		personJ.addAttribute(new UmlAttribute(Name, Name, stringN));
		addAssociation(personJ, Registration, eintrag);
		model.addNode(personJ);

		UmlNode gegenstand = new UmlNode("class" + counter++, Object);
		gegenstand.addInheritate(legalObject);
		gegenstand.addAttribute(new UmlAttribute(Name, Name, stringN));
		model.addNode(gegenstand);

		UmlNode sache = new UmlNode("class" + counter++, Thing);
		sache.addInheritate(gegenstand);
		model.addNode(sache);

		UmlNode uebergang = new UmlNode("class" + counter++, PropertyTransfer);
		uebergang.addInheritate(legalObject);
		model.addNode(uebergang);

		UmlNode recht = new UmlNode("class" + counter++, Right);
		recht.addInheritate(gegenstand);
		model.addNode(recht);

		UmlNode preis = new UmlNode("class" + counter++, PurchasePrice);
		preis.addInheritate(gegenstand);
		preis.addAttribute(new UmlAttribute(Amount, Amount, integerN));
		model.addNode(preis);

		UmlNode anteil = new UmlNode("class" + counter++, Share);
		anteil.addInheritate(recht);
		anteil.addAttribute(new UmlAttribute(Name, Name, stringN));
		anteil.addAttribute(new UmlAttribute(Price, Price, integerN));
		model.addNode(anteil);

		UmlNode unter = new UmlNode("class" + counter++, Corporation);
		unter.addInheritate(personJ);
		unter.addAttribute(new UmlAttribute(Name, Name, stringN));
		addAssociation(anteil, Share, person);
		model.addNode(unter);

		UmlNode regelung = new UmlNode("class" + counter++, Claim);
		regelung.addInheritate(recht);
		regelung.addAttribute(new UmlAttribute(Name, Name, stringN));
		regelung.addAttribute(new UmlAttribute(FactTextG, FactTextG, stringN));
		regelung.addAttribute(new UmlAttribute(FactTextB, FactTextB, stringN));
		addAssociation(regelung, Debtor, person);
		addAssociation(regelung, Depend, regelung);
		addAssociation(regelung, Creditor, person);
		addAssociation(regelung, Performance, function);
		model.addNode(regelung);

		UmlNode recht_eigen = new UmlNode("class" + counter++, PropertyRight);
		recht_eigen.addInheritate(recht);
		recht_eigen.addAttribute(new UmlAttribute(Owner, Owner, person));
		recht_eigen.addAttribute(new UmlAttribute(Property, Property, gegenstand));
		// addAssociation(recht_eigen, Eigentuemer, person);
		// addAssociation(recht_eigen, Eigentum, gegenstand);
		model.addNode(recht_eigen);

		UmlNode recht_mittel = new UmlNode("class" + counter++, IndirectOwner);
		recht_mittel.addInheritate(recht_eigen);
		model.addNode(recht_mittel);

		UmlNode folge = new UmlNode("class" + counter++, SecondaryClaim);
		folge.addInheritate(regelung);
		addAssociation(folge, Trigger, regelung);
		addAssociation(folge, Content, function);
		model.addNode(folge);
		
		UmlNode pflicht = new UmlNode("class" + counter++, PrimaryClaim);
		pflicht.addInheritate(regelung);
		pflicht.addAttribute(new UmlAttribute(DueDate, DueDate, date));
		addAssociation(pflicht, Debtor, person);
		addAssociation(pflicht, Creditor, person);
		addAssociation(pflicht, Trigger, folge);
		addAssociation(folge, Trigger, pflicht);
		// pflicht.addAttribute(new UmlAttribute(Glaeubiger, Glaeubiger,
		// person));
		model.addNode(pflicht);

		UmlNode verpflicht = new UmlNode("class" + counter++, Claim2);
		verpflicht.addInheritate(pflicht);
		model.addNode(verpflicht);

		
		UmlNode indemnity = new UmlNode("class" + counter++, Indemnity);
		indemnity.addInheritate(folge);
		indemnity.addAttribute(new UmlAttribute(Damage, Damage, stringN));
		indemnity.addAttribute(new UmlAttribute(Min, Min, integerN));
		indemnity.addAttribute(new UmlAttribute(Max, Max, integerN));
		model.addNode(indemnity);
		
		UmlNode garan = new UmlNode("class" + counter++, Warranty);
		garan.addInheritate(folge);
		model.addNode(garan);

		UmlNode nach = new UmlNode("class" + counter++, Supplementary);
		nach.addInheritate(garan);
		nach.addAttribute(new UmlAttribute(DueDate, DueDate, date));
		model.addNode(nach);

		UmlNode rueck = new UmlNode("class" + counter++, Withdrawal);
		rueck.addInheritate(garan);
		addAssociation(rueck, Debtor, person);
		model.addNode(rueck);

		UmlNode ersatz = new UmlNode("class" + counter++, Compensation);
		ersatz.addInheritate(garan);
		ersatz.addAttribute(new UmlAttribute(Damage, Damage, stringN));
		ersatz.addAttribute(new UmlAttribute(Min, Min, integerN));
		ersatz.addAttribute(new UmlAttribute(Max, Max, integerN));
		addAssociation(ersatz, Price, preis);
		model.addNode(ersatz);

		UmlNode vertrag = new UmlNode("class" + counter++, SPA);
		vertrag.addInheritate(folge);
		vertrag.addAttribute(new UmlAttribute(Closing, Closing, date));
		vertrag.addAttribute(new UmlAttribute(Signing, Signing, date));
		addAssociation(vertrag, Purchaser, person);
		addAssociation(vertrag, Seller, person);
		addAssociation(vertrag, PurchaseObject, gegenstand);
		addAssociation(vertrag, PurchasePrice, preis);
		model.addNode(vertrag);
	}

	private static void addAssociation(UmlNode node, String name, UmlNode child)
	{
		if (node == null)
			return;
		UmlAssociation ass = new UmlAssociation("");
		ass.setName(name);
		ass.addAssNode(name, child);
		node.addAssoziation(ass);
	}

	static void createModel()
	{
		if (model != null)
			return;
		model = new UmlModel();
		addClasses(model);
	}

	public static UmlNode getNodeByName(String name)
	{
		createModel();
		return model.getClassByName(name);
	}

	public static boolean isNodeClass(String name)
	{
		createModel();
		return model.getClassByName(name) != null;
	}
}
