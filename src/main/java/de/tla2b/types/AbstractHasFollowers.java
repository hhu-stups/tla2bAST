package de.tla2b.types;

import java.util.ArrayList;
import java.util.List;

import de.tla2b.analysis.TypeChecker;

import tla2sany.semantic.SemanticNode;

public abstract class AbstractHasFollowers extends TLAType {

	private List<Object> followers = null;

	public AbstractHasFollowers(int t) {
		super(t);
	}

	public void addFollower(Object o) {
		if (followers == null) {
			followers = new ArrayList<>();
		}
		// only (partial) untyped types need follower
		if (!followers.contains(o)) {
			followers.add(o);
		}
	}

	public void deleteFollowers() {
		followers = null;
	}

	public void removeFollower(Object o) {
		if (this.hasFollowers()) {
			followers.remove(o);
		}
	}

	protected void setFollowersTo(TLAType newType) {
		if (!this.hasFollowers()) {
			return;
		}
		// avoid concurrent modification:
		new ArrayList<>(followers).forEach(follower -> {
			//this.removeFollower(follower);
			if (follower instanceof SemanticNode) {
				TypeChecker.updateTypeAndFollowers((SemanticNode) follower, this, newType);
			} else if (follower instanceof SetType) {
				((SetType) follower).update(this, newType);
			} else if (follower instanceof TupleType) {
				((TupleType) follower).update(this, newType);
			} else if (follower instanceof PairType) {
				((PairType) follower).update(this, newType);
			} else if (follower instanceof FunctionType) {
				((FunctionType) follower).update(this, newType);
			} else if (follower instanceof StructType) {
				((StructType) follower).setNewType(this, newType);
			} else if (follower instanceof StructOrFunctionType) {
				((StructOrFunctionType) follower).setNewType(this, newType);
			} else if (follower instanceof TupleOrFunction) {
				((TupleOrFunction) follower).setNewType(this, newType);
			} else {
				throw new RuntimeException("Unknown follower type: " + follower.getClass());
			}
		});
	}

	public boolean hasFollowers() {
		return followers != null && !followers.isEmpty();
	}
}
