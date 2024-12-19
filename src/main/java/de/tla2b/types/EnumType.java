package de.tla2b.types;

import de.be4.classicalb.core.parser.node.PExpression;
import de.tla2b.exceptions.UnificationException;
import de.tla2b.output.TypeVisitorInterface;
import de.tla2bAst.BAstCreator;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

public class EnumType extends AbstractHasFollowers {
	public final Set<String> modelvalues;
	public int id;
	private boolean noVal = false;

	public EnumType(List<String> enums) {
		super(MODELVALUE);
		modelvalues = new LinkedHashSet<>(enums);
	}

	public void setNoVal() {
		noVal = true;
	}

	public boolean hasNoVal() {
		return noVal;
	}

	public Set<String> getValues() {
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
