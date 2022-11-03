package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Scanner;
import java.util.Set;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import kn.uni.sen.jobscheduler.common.model.Job;
import kn.uni.sen.jobscheduler.common.model.JobEvent;
import kn.uni.sen.jobscheduler.common.resource.ResourceFile;

/** data structure to store a UML class diagram
 * 
 * @author Martin Koelbl
 */
public class UmlModel2
{
	String xsdFileUrl = null;
	Document doc = null;
	Element root = null;
	Element meta = null;
	Element model = null;
	int IDCounter = 0;

	Job job;

	public UmlModel2(Job j, ResourceFile xsd)
	{
		// parseContractSchema(xsd);
		job = j;
		createDocument();
		root = doc.createElement("root");
		root.setAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance");
		root.setAttribute("xmlns", "http://legaltech.sen.uni-konstanz.de");
		root.setAttribute("schemaLocation", "http://legaltech.sen.uni-konstanz.de");
		doc.appendChild(root);

		meta = addMetaSchema(doc);
		// doc.adoptNode(meta);
		// root.appendChild(meta);

		model = doc.createElement("model");
		root.appendChild(model);
	}

	private void createDocument()
	{
		doc = null;
		try
		{
			DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
			DocumentBuilder builder = factory.newDocumentBuilder();
			doc = builder.newDocument();
		} catch (ParserConfigurationException e)
		{
			e.printStackTrace();
		}
	}

	public InputStream getXSDFile()
	{
		ClassLoader classLoader = getClass().getClassLoader();
		URL res = classLoader.getResource("legal.xsd");
		try
		{
			return res.openStream();
		} catch (IOException e)
		{
			// e.printStackTrace();
		}
		return null;
	}

	public boolean validateFile(String xmlFile, ResourceFile xsdFile)
	{
		StreamSource inStream = null;
		if ((xsdFile != null) && xsdFile.exists())
		{
			inStream = new StreamSource(xsdFile.getData());
			// xsdFileUrl = xsdFile.getData();
		}
		if (inStream == null)
		{
			// load default csd file
			InputStream s = getXSDFile();
			inStream = new StreamSource(s);
		}
		try
		{
			SchemaFactory factory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
			Schema schema = factory.newSchema(inStream);
			Validator validator = schema.newValidator();
			validator.validate(new StreamSource(xmlFile));
		} catch (Exception ex)
		{
			job.logEventStatus(JobEvent.WARNING, ex.getMessage());
			return false;
		}
		return true;
	}

	public String parseFile(URL url)
	{
		StringBuilder build = new StringBuilder();
		try
		{
			Scanner s = new Scanner(url.openStream());
			while (s.hasNextLine())
				build.append(s.nextLine());
		} catch (IOException e)
		{
			return null;
		}
		return build.toString();
	}

	Document parseSchema()
	{
		// Setup classes to parse XSD file for complex types
		DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
		DocumentBuilder db;
		try
		{
			db = dbf.newDocumentBuilder();
			InputStream inStream = getXSDFile();

			// FileInputStream fis = new FileInputStream("legal.xsd");
			Document doc = db.parse(inStream);
			return doc;
		} catch (ParserConfigurationException e)
		{
			e.printStackTrace();
		} catch (Exception e)
		{
			e.printStackTrace();
		}
		return null;
	}

	private Element addMetaSchema(Document docNew)
	{
		Document docSchema = parseSchema();
		if (docSchema == null)
			return null;

		Element element = docSchema.getDocumentElement();
		Element eleNew = (Element) element.cloneNode(true);

		// get all child nodes
		NodeList nodes = eleNew.getChildNodes();

		// add each child to meta model
		for (int i = 0; i < nodes.getLength(); i++)
		{
			Node item = nodes.item(i);
			// NamedNodeMap attrs = item.getAttributes();
			// if (attrs != null)
			// System.out.println("" + attrs.getNamedItem("name"));

			// Node itemNew = item.cloneNode(false);
			// docNew.adoptNode(itemNew);
			if (item.getNodeType() == Node.ELEMENT_NODE)
				setUniqueID((Element) item);
		}
		return eleNew;
	}

	private Node xPathSearchAttribute(Element start, String query)
	{
		Document docSchema = parseSchema();
		if (docSchema == null)
			return null;
		// Given the id, go to correct place in XSD to get all the
		// parameters
		XPath xpath = XPathFactory.newInstance().newXPath();
		try
		{
			NodeList result = (NodeList) xpath.compile(query).evaluate(start, XPathConstants.NODESET);
			for (int i = 0; i < result.getLength();)
			{
				return result.item(i);
			}
		} catch (XPathExpressionException e1)
		{
			e1.printStackTrace();
		}
		return null;
	}

	private Element xPathSearchElement(Element start, String query)
	{
		// Document docSchema = parseSchema();
		// if (docSchema == null)
		// return null;
		// Given the id, go to correct place in XSD to get all the
		// parameters
		XPath xpath = XPathFactory.newInstance().newXPath();
		try
		{
			NodeList result = (NodeList) xpath.compile(query).evaluate(start, XPathConstants.NODESET);
			for (int i = 0; i < result.getLength();)
			{
				Element e = (Element) result.item(i);
				// System.out.println("" + e.getNodeName() + " = " +
				// e.getAttribute("name"));
				return e;
			}
		} catch (XPathExpressionException e1)
		{
			e1.printStackTrace();
		}
		return null;
	}

	private UmlNode2 xPathSearchNode(Element start, String query)
	{
		Element e = (Element) xPathSearchElement(start, query);
		if (e == null)
			return null;
		return new UmlNode2(this, e);
	}

	private List<UmlNode2> xPathSearchNodes(Element start, String query)
	{
		List<UmlNode2> list = new ArrayList<>();
		Document docSchema = parseSchema();
		if (docSchema == null)
			return list;
		// Given the id, go to correct place in XSD to get all the
		// parameters
		XPath xpath = XPathFactory.newInstance().newXPath();
		try
		{
			NodeList result = (NodeList) xpath.compile(query).evaluate(start, XPathConstants.NODESET);
			for (int i = 0; i < result.getLength(); i++)
			{
				Node n = result.item(i);
				if (n.getNodeType() != Node.ELEMENT_NODE)
					continue;
				list.add(new UmlNode2(this, (Element) n));
			}
		} catch (XPathExpressionException e1)
		{
			e1.printStackTrace();
		}
		return list;
	}

	private List<Element> xPathSearchElements(Element start, String query)
	{
		List<Element> list = new ArrayList<>();
		Document docSchema = parseSchema();
		if (docSchema == null)
			return list;
		// Given the id, go to correct place in XSD to get all the
		// parameters
		XPath xpath = XPathFactory.newInstance().newXPath();
		try
		{
			NodeList result = (NodeList) xpath.compile(query).evaluate(start, XPathConstants.NODESET);
			for (int i = 0; i < result.getLength(); i++)
			{
				Node n = result.item(i);
				if (n.getNodeType() != Node.ELEMENT_NODE)
					continue;
				list.add((Element) n);
			}
		} catch (XPathExpressionException e1)
		{
			e1.printStackTrace();
		}
		return list;
	}

	void writeFile(String filePath)
	{
		TransformerFactory transformerFactory = TransformerFactory.newInstance();
		Transformer transf;
		try
		{
			ResourceFile.createFile(filePath, false);

			transf = transformerFactory.newTransformer();
			transf.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
			transf.setOutputProperty(OutputKeys.INDENT, "yes");
			transf.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");

			DOMSource source = new DOMSource(doc);

			File myFile = new File(filePath);

			StreamResult file = new StreamResult(myFile);
			transf.transform(source, file);
		} catch (TransformerConfigurationException e)
		{
			e.printStackTrace();
		} catch (TransformerException e)
		{
			e.printStackTrace();
		}
	}

	private void setUniqueID(Element ele)
	{
		String id = ele.getAttribute("id");
		if (!!!id.isEmpty())
			return;
		id = "" + (++IDCounter);
		ele.setAttribute("id", id);
	}

	private String replaceSigns(String text)
	{
		if (text == null)
			return text;
		text = text.replaceAll("ä", "ae").replaceAll("ö", "oe").replaceAll("ü", "ue").replaceAll("ß", "s");
		return text.replace("(", "").replace(")", "").replace(" ", "");
	}

	public Element createElement(String type, String id)
	{
		return createElement(model, type, id);
	}

	public Element createElement(Element parent, String type, String id)
	{
		type = replaceSigns(type);
		UmlNode2 cl = getClass(type);
		if (cl == null)
			job.logEventStatus(JobEvent.WARNING, "Missing Class " + type);

		Element ele = doc.createElement(type);
		if (id != null)
			ele.setAttribute("name", id);
		setUniqueID(ele);
		if (parent == null)
			parent = model;
		parent.appendChild(ele);
		return ele;
	}

	Map<String, String> inheritMap = null;

	/**
	 * @return map with all inheritances between classe
	 */
	private Map<String, String> getInheritMap()
	{
		if (inheritMap != null)
			return inheritMap;

		inheritMap = new HashMap<>();
		List<UmlNode2> classes = xPathSearchNodes(meta, "complexType");
		for (UmlNode2 n : classes)
		{
			Element e = n.getElement();
			String name = e.getAttribute("name");
			Node attr = xPathSearchAttribute(e, "complexContent/extension/@base");
			if (attr == null)
				continue;
			String val = attr.getNodeValue();
			if ((val == null) || val.isEmpty())
				continue;
			inheritMap.put(name, val);
		}
		return inheritMap;
	}

	private Map<String, Set<String>> getInheritMapInverse()
	{
		Map<String, String> map = getInheritMap();
		Map<String, Set<String>> map2 = new HashMap<>();
		for (String k : map.keySet())
		{
			String val = map.get(k);

			Set<String> set = map2.get(val);
			if (set == null)
			{
				set = new HashSet<String>();
				map2.put(val, set);
			}
			set.add(k);
		}
		return map2;
	}

	public boolean inheritatesFrom(String node, String type)
	{
		Map<String, String> inheritMap = getInheritMap();

		String cl = node;
		while ((cl != null) && !!!cl.isEmpty())
		{
			if (cl.contentEquals(type))
				return true;
			cl = inheritMap.get(cl);
		}
		return false;
	}

	public boolean inheritatesFrom(Element node, String type)
	{
		if (isElementName(node, type))
			return true;

		Map<String, String> inheritMap = getInheritMap();

		String cl = node.getNodeName();
		while ((cl != null) && !!!cl.isEmpty())
		{
			if (cl.contentEquals(type))
				return true;
			cl = inheritMap.get(cl);
		}
		return false;
	}

	private boolean isElementName(Element node, String name)
	{
		if (node == null)
			return false;
		String name2 = node.getAttribute("name");
		if ((name2 == null) || name2.isEmpty())
			return false;
		if (name.equals(name2))
			return true;
		return false;
	}

	public void addAssociation2Node(Element par, String name, Element node)
	{
		name = replaceSigns(name);
		Element ass = doc.createElement(name);
		// ass.setAttribute("name", name);
		String id = node.getAttribute("id");
		if ((id == null) || id.isEmpty())
		{
			System.out.println("Element is missing ID " + node.getNodeName() + " " + node.getAttribute("name"));
			return;
		}
		ass.setAttribute("ref", id);
		par.appendChild(ass);
	}

	public boolean isRef(Element e)
	{
		if (e == null)
			return false;
		String ref = e.getAttribute("ref");
		if ((ref != null) && (!!!ref.isEmpty()))
			return true;
		return false;
	}

	public UmlNode2 checkRef(UmlNode2 n)
	{
		if (n == null)
			return null;
		if (!!!n.getElement().hasAttribute("ref"))
			return n;
		String ref = n.getElement().getAttribute("ref");
		if ((ref == null) || ref.isEmpty())
			return null;
		return getElementByID(ref);
	}

	public List<UmlNode2> getAssoziationsByName(Element node, String name)
	{
		List<UmlNode2> list = new ArrayList<>();
		NodeList children = node.getChildNodes();
		for (int i = 0; i < children.getLength(); i++)
		{
			Node ele = children.item(i);
			if (name.equals(ele.getNodeName()))
				if (ele.getNodeType() == Node.ELEMENT_NODE)
				{
					Element e = (Element) ele;
					UmlNode2 node2 = new UmlNode2(this, e);
					node2 = checkRef(node2);
					if (node2 != null)
						list.add(node2);
				}
		}
		return list;
	}

	public UmlNode2 getAssoziationByName(Element node, String name)
	{
		List<UmlNode2> list = getAssoziationsByName(node, name);
		if ((list == null) || list.isEmpty())
			return null;
		return list.get(0);
	}

	public void addAttribute(Element par, String name, String v)
	{
		name = replaceSigns(name);
		if (name == null)
		{
			System.out.println("Warning: Empty Attribute Name");
			return;
		}
		// remove old attributes
		removeAttribute(par, name);

		Element ass = doc.createElement(name);
		// ass.setAttribute("name", name);
		ass.setTextContent(v);
		// ass.setAttribute("value", v);
		par.appendChild(ass);
	}

	public void removeAttribute(Element par, String name)
	{
		UmlNode2 n = getNodeByName(name);
		while (n != null)
		{
			par.removeChild(n.getElement());
			n = getNodeByName(name);
		}
	}

	private UmlNode2 getElementByID(String id)
	{
		String query = "//*[@id='" + id + "']";
		return xPathSearchNode(root, query);
	}

	public UmlNode2 getClass(String type)
	{
		String query = "complexType[@name='" + type + "']";
		UmlNode2 node = xPathSearchNode(meta, query);
		if (node != null)
			return node;
		query = "simpleType[@name='" + type + "']";
		return xPathSearchNode(meta, query);
	}

	public Element getClassElement(String type)
	{
		UmlNode2 ele = getClass(type);
		if (ele == null)
			return null;
		return ele.getElement();
	}

	/**
	 * 
	 * @param type
	 * @return all instances that inherit class type
	 */
	public List<UmlNode2> getClassInstances(String type)
	{
		// if (!!!recursive)
		// return xPathSearchElements(model, "" + type);

		// get recursively all classes that inherit class type
		Map<String, Set<String>> map = getInheritMapInverse();
		Set<String> list = new HashSet<>();
		Queue<String> listNew = new LinkedList<>();
		listNew.add(type);
		while (!!!listNew.isEmpty())
		{
			String t = listNew.remove();
			list.add(t);
			Set<String> set = map.get(t);
			if (set == null)
				continue;
			listNew.addAll(set);
		}
		/*
		 * List<UmlNode2> listNew = new ArrayList<>(); // UmlNode2 cl =
		 * getClass(type); // UmlNode2 node = listNew.remove(0); String t =
		 * node.getName(); if ((t == null) || (t.isEmpty())) continue;
		 * list.add(t); List<UmlNode2> l = xPathSearchElements(meta,
		 * "//*[complexContent/extension[@base='" + t + "']]"); //
		 * "//*[contains(@base, '" + t + "')]/.."); if (l != null)
		 * listNew.addAll(l); }
		 */

		// get all instances
		Set<Element> nodes = new HashSet<>();
		for (String t : list)
		{
			List<Element> l = xPathSearchElements(model, "" + t);
			if (l != null)
				nodes.addAll(l);
		}
		return convertList2Node(nodes);
	}

	private List<UmlNode2> convertList2Node(Set<Element> nodes)
	{
		if (nodes == null)
			return null;
		List<UmlNode2> list = new ArrayList<>();
		for (Element e : nodes)
		{
			list.add(new UmlNode2(this, e));
		}
		return list;
	}

	public UmlNode2 getNodeByName(String name)
	{
		String query = "*[@name='" + name + "']";
		return xPathSearchNode(model, query);
	}

	public String getAttributeValue(Element ele, String name)
	{
		String query = "" + name;
		UmlNode2 n = xPathSearchNode(ele, query);
		if (n == null)
			return null;
		String val = null;
		if (n.getElement().hasAttribute(name))
			val = n.getElement().getAttribute("value");
		if (val == null)
		{
			val = n.getElement().getTextContent();
			if ((val == null) || (val.isEmpty()))
				return null;
		};
		return val;
	}

	public void setNodeAttribute(Element node, String v)
	{
		node.setNodeValue(v);
	}

	public UmlNode2 getNodeByID(String ref)
	{
		String query = "*[@id='" + ref + "']";
		return xPathSearchNode(model, query);
	}

	public List<UmlNode2> getAssoziationsByClass(Element ele, String type)
	{
		System.out.println("getAssoziationsByClass is not implemented");
		assert (false);
		return new ArrayList<>();
	}

	public List<UmlNode2> findNodesByExpression(String expr)
	{
		return xPathSearchNodes(model, expr);
	}

	public boolean isOfClass(Element ele, String type)
	{
		if (ele == null)
			return false;
		String cl = ele.getNodeName();
		if (cl.contentEquals(type))
			return true;
		return false;
	}
}
