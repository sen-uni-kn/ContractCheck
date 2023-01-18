package kn.uni.sen.joblibrary.legaltech.job_legalcheck;

import org.w3c.dom.Element;

public interface UmlVisitor
{
	void visit(UmlModel2 model);

	void visitElement(Element ele);

	void leaveElement(Element ele);

	void visitAttribute(Element ele, String name, String val);
}
