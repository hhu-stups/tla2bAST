package de.tla2b.types;

import java.util.ArrayList;
import java.util.LinkedHashSet;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;
import de.tla2bAst.BAstCreator;

public class EnumType extends AbstractHasFollowers {
	public LinkedHashSet<String> modelvalues;
	public int id;
	private boolean noVal = false;

	public EnumType(ArrayList<String> enums) {
		super(MODELVALUE);
		modelvalues = new LinkedHashSet<String>(enums);
	}

	public void setNoVal() {
		noVal = true;
	}

	public boolean hasNoVal() {
		return noVal;
	}

	public LinkedHashSet<String> getValues() {
		return modelvalues;
	}

	@Override
	public boolean isUntyped() {
		return false;
	}

	@Override
	public boolean compare(TLAType o) {
		return o.getKind() == UNTYPED || o.getKind() == MODELVALUE;
	}

	@Override
	public EnumType unify(TLAType o) throws UnificationException {
		if (o instanceof UntypedType) {
			((UntypedType) o).setFollowersTo(this);
			return this;
		}
		if (o instanceof EnumType) {
			EnumType e = (EnumType) o;
			e.setFollowersTo(this);
			this.modelvalues.addAll(((EnumType) o).modelvalues);
			return this;
		}
		throw new UnificationException();
	}

	@Override
	public EnumType cloneTLAType() {
		return this;
	}
	
	@Override
	public boolean contains(TLAType o) {
		//TODO is this really false
		return false;
	}

	@Override
	public String toString() {
		return "ENUM" + id;
	}
	
	@Override
	public PExpression getBNode() {
		return BAstCreator.createIdentifierNode("ENUM" + id);
	}

	public void apply(TypeVisitorInterface t) {
		t.caseEnumType(this);
	}


}
