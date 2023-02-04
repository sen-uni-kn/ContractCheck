package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.List;

import kn.uni.sen.joblibrary.legaltech.smt_model.SmtConstraint;
import kn.uni.sen.joblibrary.legaltech.smt_model.SmtDeclare;

/**
 * Annotation of constraints of the element
 * 
 * @author Martin Koelbl (C) 2023
 */
public class UmlAnnotation
{
	//todo: by hash table -> boolean searched;
	String origin;
	List<SmtDeclare> variables; 
	List<SmtConstraint> constraints; 
}
