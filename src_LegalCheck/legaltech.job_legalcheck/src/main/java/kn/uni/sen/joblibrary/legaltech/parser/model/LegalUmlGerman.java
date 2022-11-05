package kn.uni.sen.joblibrary.legaltech.parser.model;

import java.util.LinkedList;
import java.util.List;

/**
 * legal UML model with German legal keywords When a German contract is parsed,
 * convert the keywords from German into English and then do the analyses
 * 
 * @author Martin Koelbl
 */
public class LegalUmlGerman
{
	static List<String[]> german = new LinkedList<>();

	static void addLanguage()
	{
		german.add(new String[] { LegalUml.SPA, "Unternehmenskaufvertrag" });
		german.add(new String[] { LegalUml.LegalPerson, "JuristischePerson" });
		german.add(new String[] { "NaturalPerson", "NatuerlichePerson" });
		german.add(new String[] { "Corporation", "Gesellschaft" });
		german.add(new String[] { "Claim", "Verpflichtung" });
		german.add(new String[] { "WarrantyClaim", "Garantie" });
		german.add(new String[] { "IndirectOwner", "MittelbarerBesitz" });
		german.add(new String[] { "PurchasePrice", "Preis" });
		german.add(new String[] { "Performance", "Leistung" });
		german.add(new String[] { "PurchasePrice", "Kaufpreis" });
		german.add(new String[] { "Registration", "Eintragung" });
		german.add(new String[] { "Property", "Eigentum" });
		german.add(new String[] { "Owner", "Eigentuemer" });
		german.add(new String[] { "CompensationClaim", "Schadensersatz" });
		german.add(new String[] { "PerformanceClaim", "Nacherfuellung" });
		german.add(new String[] { "PurchasePrice", "Kaufpreis" });
		german.add(new String[] { "Object", "Gegenstand" });
		german.add(new String[] { "Thing", "Sache" });
		german.add(new String[] { "Right", "Recht" });
		german.add(new String[] { "Share", "Anteil" });
		german.add(new String[] { "Share", "Anteile" });
		german.add(new String[] { "DueDate", "Frist" });
		german.add(new String[] { "Limitation", "Verjaehrung" });
		german.add(new String[] { "PurchasePrice", "Kaufpreis" });
		german.add(new String[] { "PrimaryClaim", "Primaerpflicht" });
		german.add(new String[] { "Debtor", "Schuldner" });
		german.add(new String[] { "Creditor", "Glaeubiger" });
		german.add(new String[] { "SecondaryClaim", "Sekundaerpflicht" });
		german.add(new String[] { "IndemnityClaim", "Freistellung" });
		german.add(new String[] { "RestitutionClaim", "Ruecktritt" });
		german.add(new String[] { "Claim", "Regelung" });
		german.add(new String[] { "Content", "Voraussetzung" });
		german.add(new String[] { "Closing", "Closing" });
		german.add(new String[] { "PurchaseObject", "Kaufgegenstand" });
		german.add(new String[] { "PropertyRight", "EigentumsRecht" });
		german.add(new String[] { "From", "Von" });
		german.add(new String[] { "To", "An" });
		german.add(new String[] { "Damage", "Schaden" });
		german.add(new String[] { "Trigger", "Folge" });
		german.add(new String[] { "Purchaser", "Kaeufer" });
		german.add(new String[] { "Seller", "Verkaeufer" });
		german.add(new String[] { "LegalFact", "Tatsache" });
		german.add(new String[] { "FactTextG", "TextErfuellt" });
		german.add(new String[] { "FactTextB", "TextUnerfuellt" });
		german.add(new String[] { "Consequence", "Folge" });
		german.add(new String[] { "PropertyTransfer", "Eigentumsuebergang" });
	}

	public static String convertEnglish(String val)
	{
		if (val == null)
			return null;
		if (german.isEmpty())
			addLanguage();
		for (String[] s2 : german)
		{
			if (val.equals(s2[1]))
				return s2[0];
		}
		return val;
	}
}
