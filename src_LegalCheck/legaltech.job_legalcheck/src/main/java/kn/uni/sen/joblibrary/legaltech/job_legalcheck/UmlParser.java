package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpression;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import kn.uni.sen.joblibrary.legaltech.parser.model.UmlAssociation;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlAttribute;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlElement;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlModel;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlNode;
import kn.uni.sen.joblibrary.legaltech.parser.model.UmlOperation;
import kn.uni.sen.jobscheduler.common.model.Job;

public class UmlParser
{
	Job job;

	public UmlParser(Job j)
	{
		job = j;
	}

	private void parseNode(UmlModel m, UmlNode un, Node n)
	{
		NodeList cn = n.getChildNodes();
		// printNodeInfos("", n);
		for (int j = 0; j < cn.getLength(); j++)
		{
			Node c = cn.item(j);
			String nameA = c.getNodeName();
			if (nameA.equals("ownedAttribute"))
			{
				String atName = getNodeAttribute(c, "name");
				String atId = getNodeAttribute(c, "xmi:id");
				UmlNode atCl = null;
				UmlAttribute attr = new UmlAttribute(atId, atName, atCl);
				un.addAttribute(attr);
			} else if (nameA.equals("ownedOperation"))
			{
				String opName = getNodeAttribute(c, "name");
				String opId = getNodeAttribute(c, "xmi:id");
				UmlOperation op = new UmlOperation(opId, opName);
				un.addOperation(op);
			} else if (nameA.equals("interfaceRealization"))
			{
				// String id =getNodeAttribute(c, "general");
				// UmlNode other = m.getNodeByID(id);
				// System.out.println("interface");
			} else if (nameA.equals("generalization"))
			{
				String id = getNodeAttribute(c, "general");
				UmlNode other = m.getNodeByID(id);
				un.addInheritate(other);
			}
		}
	}

	private String replaceSigns(String text)
	{
		if (text == null)
			return text;
		return text.replaceAll("ä", "ae").replaceAll("ö", "oe").replaceAll("ü", "ue").replaceAll("ß", "s");
	}

	private UmlModel parseUML(Document doc)
	{
		UmlModel model = new UmlModel();

		// 1. parse every class and interface
		Map<UmlNode, Node> map = new HashMap<>();
		NodeList nodes = docRequest(doc, "//packagedElement[@type='uml:Class']");
		for (int i = 0; i < nodes.getLength(); i++)
		{
			Node n = nodes.item(i);
			String id = getNodeAttribute(n, "xmi:id");
			String name = getNodeAttribute(n, "name");
			UmlNode node = new UmlNode(id, replaceSigns(name));
			if (node != null)
				map.put(node, n);
			model.addNode(node);
		}
		nodes = docRequest(doc, "//packagedElement[@type='uml:Interface']");
		for (int i = 0; i < nodes.getLength(); i++)
		{
			Node n = nodes.item(i);
			String id = getNodeAttribute(n, "xmi:id");
			String name = getNodeAttribute(n, "name");
			UmlNode node = new UmlNode(id, replaceSigns(name));
			if (node != null)
				map.put(node, n);
			model.addNode(node);
		}
		// parse attributes of class nodes
		for (UmlNode un : map.keySet())
			parseNode(model, un, map.get(un));
		map.clear();

		// 2. parse associations
		nodes = docRequest(doc, "//packagedElement[@type='uml:Association']");
		for (int i = 0; i < nodes.getLength(); i++)
		{
			Node n = nodes.item(i);
			UmlAssociation ass = parseAssociation(model, n);
			model.addAssoziation(ass);
		}

		// 3. parse Instances
		nodes = docRequest(doc, "//packagedElement[@type='uml:InstanceSpecification']");
		for (int i = 0; i < nodes.getLength(); i++)
		{
			Node n = nodes.item(i);
			parseInstance(model, n);
		}

		return model;
	}

	private void parseInstance(UmlModel model, Node n)
	{
		String id = getNodeAttribute(n, "xmi:id");
		String cl = getNodeAttribute(n, "classifier");

		UmlElement ele = model.getByID(id);
		if (ele != null)
			// don't parse element twice
			return;

		UmlElement cla = model.getByID(cl);
		if (cla == null)
			return;

		if (cla instanceof UmlNode)
		{
			UmlNode node = parseInstanceNode(n, id, (UmlNode) cla);
			if (node != null)
				model.addNode(node);
		} else if (cla instanceof UmlAssociation)
		{
			UmlAssociation ass = parseInstanceAssociation(model, n, id, (UmlAssociation) cla);
			if (ass != null)
				model.addAssoziation(ass);
		}

	}

	private UmlNode parseInstanceNode(Node n, String id, UmlNode cla)
	{
		String name = getNodeAttribute(n, "name");
		UmlNode node = new UmlNode(id, replaceSigns(name));
		// System.out.println(name);

		node.setInstanceOf(cla);

		// parse attributes of instance
		NodeList atts = docRequest(n, "child::slot");
		for (int i = 0; i < atts.getLength(); i++)
		{
			Node c = atts.item(i);

			String featID = getNodeAttribute(c, "definingFeature");
			Node feat = docRequestFirst(n, "//*[@id='" + featID + "']");
			String atName = getNodeAttribute(feat, "name");
			String atId = getNodeAttribute(c, "xmi:id");

			//if (atId.equals("_lDMkl9qEEeuJ7vPsBYYixQ"))
			//{
			//	System.out.print("");
			//}

			// todo: parse type
			UmlNode atCl = null;

			// parse value
			Node val = docRequestFirst(c, "child::value");
			String atValue = getNodeAttribute(val, "value");
			if (atValue == null)
				atValue = getNodeAttribute(val, "symbol");

			UmlAttribute attr = new UmlAttribute(atId, atName, atCl);
			attr.setValue(atValue);
			node.addAttribute(attr);
		}

		return node;
	}

	private UmlAssociation parseInstanceAssociation(UmlModel model, Node n, String id, UmlAssociation cla)
	{
		UmlAssociation ass = new UmlAssociation(id);
		NodeList children = docRequest(n, "child::slot/value");
		// String assText = "Ass Instance: ";

		for (int i = 0; i < children.getLength(); i++)
		{
			Node c = children.item(i);
			String idC = getNodeAttribute(c, "instance");
			UmlNode nRef = model.getNodeByID(idC);
			if (nRef == null)
			{
				// referenced node is not yet parsed
				parseNodeByID(n, model, idC);
				nRef = model.getNodeByID(idC);
			}
			if (nRef == null)
			{
				job.logEventStatus("Warning", "Missing Associated Node: " + idC);
				return null;
			}

			Node parent = docRequestFirst(c, "parent::*");
			String val = getNodeAttribute(parent, "definingFeature");
			Node feat = docRequestFirst(n, "//*[@id='" + val + "']");
			String name = getNodeAttribute(feat, "name");

			ass.addAssNode(replaceSigns(name), nRef);
			nRef.addAssoziation(ass);
			// assText += name + " " + nRef.getName() + " ";
		}
		return ass;
	}

	private void parseNodeByID(Node n, UmlModel model, String idC)
	{
		NodeList nodeRef = docRequest(n, "//*[@id='" + idC + "']");
		for (int i = 0; i < nodeRef.getLength(); i++)
		{
			Node c = nodeRef.item(i);
			parseInstance(model, c);
		}
	}

	private UmlAssociation parseAssociation(UmlModel model, Node n)
	{
		String id = getNodeAttribute(n, "xmi:id");
		UmlAssociation ass = new UmlAssociation(id);
		String name = getNodeAttribute(n, "name");
		ass.setName(name);

		String members = getNodeAttribute(n, "memberEnd");
		for (String mem : members.split(" "))
		{
			Node fs = docRequestFirst(n, "//*[@id='" + mem + "']");
			if ("ownedEnd".equals(fs.getNodeName()))
			{
				String oid = getNodeAttribute(fs, "association");
				String nameEnd = getNodeAttribute(fs, "name");
				UmlNode other = model.getClass(oid);
				// seems not to exist
				ass.addAssNode(nameEnd, other);
				if (other != null)
					other.addAssoziation(ass);
			} else if ("ownedAttribute".equals(fs.getNodeName()))
			{
				Node parent = docRequestFirst(fs, "parent::*");
				String nameEnd = getNodeAttribute(parent, "name");
				String fID = getNodeAttribute(parent, "xmi:id");
				UmlNode other = model.getClass(fID);
				ass.addAssNode(nameEnd, other);
				// if (other == null)
				// System.out.println("Missing other in Association.");
				if (other != null)
					other.addAssoziation(ass);
			}
		}
		return ass;
	}

	private NodeList docRequest(Node doc, String request)
	{
		XPathFactory xPathfactory = XPathFactory.newInstance();
		XPath xpath = xPathfactory.newXPath();
		try
		{
			XPathExpression expr = xpath.compile(request);
			NodeList nodes = (NodeList) expr.evaluate(doc, XPathConstants.NODESET);
			return nodes;
		} catch (XPathExpressionException e)
		{
			e.printStackTrace();
		}
		return null;
	}

	private Node docRequestFirst(Node doc, String request)
	{
		NodeList list = docRequest(doc, request);
		if (list != null)
			for (int i = 0; i < list.getLength();)
			{
				return list.item(i);
			}
		return null;
	}

	private String getNodeAttribute(Node n, String attr)
	{
		if (n == null)
			return null;
		NamedNodeMap am = n.getAttributes();
		// printNodeInfos("", n);
		Node a = am.getNamedItem(attr);
		if (a == null)
			return null;
		return a.getNodeValue();
	}

	public UmlModel parseFile(InputStream xmiStream)
	{
		// 1.parse XMI:
		try
		{
			// ---- Parse XML file ----
			DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
			DocumentBuilder builder = factory.newDocumentBuilder();
			Document document = builder.parse(xmiStream);
			// ---- Get list of nodes to given element tag name ----
			// NodeList ndList =
			// document.getElementsByTagName("packagedElement");
			// printNodesFromList(ndList); // printNodesFromList see below
			return parseUML(document);
			// ---- Error handling ----
		} catch (SAXParseException spe)
		{
			job.logEventStatus("Error", "\n** Parsing error, line " + spe.getLineNumber() + ", uri " + spe.getSystemId()
					+ "   " + spe.getMessage());
			Exception e = (spe.getException() != null) ? spe.getException() : spe;
			e.printStackTrace();
		} catch (SAXException sxe)
		{
			Exception e = (sxe.getException() != null) ? sxe.getException() : sxe;
			e.printStackTrace();
		} catch (ParserConfigurationException pce)
		{
			pce.printStackTrace();
		} catch (IOException ioe)
		{
			ioe.printStackTrace();
		}
		// 2. generate Legal Model

		// 3. transform to SMT

		return null;
	}
}
