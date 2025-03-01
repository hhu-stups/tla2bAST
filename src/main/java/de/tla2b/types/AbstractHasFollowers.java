package de.tla2b.types;

import de.tla2b.analysis.TypeChecker;
import tla2sany.semantic.SemanticNode;

import java.util.ArrayList;
import java.util.List;

public abstract class AbstractHasFollowers extends TLAType {

	private List<Object> followers = new ArrayList<>();

	public AbstractHasFollowers(int t) {
		super(t);
	}

	public List<Object> getFollowers() {
		return followers;
	}

	public void addFollower(Object o) {
		// only (partial) untyped types need follower
		if (followers != null && !followers.contains(o))
			followers.add(o);
	}

	public void deleteFollowers() {
		followers = null;
	}

	public void removeFollower(Object o) {
		followers.remove(o);
	}

	protected void setFollowersTo(TLAType newType) {
		if (this.followers == null)
			return;
		// avoid concurrent modification:
		new ArrayList<>(followers).forEach(follower -> {
			if (follower instanceof SemanticNode) {
				TypeChecker.setType((SemanticNode) follower, newType);
				if (newType instanceof AbstractHasFollowers) {
					((AbstractHasFollowers) newType).addFollower(follower);
				}
			} else if (follower instanceof SetType) {
				((SetType) follower).setSubType(newType);
			} else if (follower instanceof TupleType) {
				((TupleType) follower).update(this, newType);
			} else if (follower instanceof PairType) {
				PairType pair = ((PairType) follower);
				if (pair.getFirst() == this) {
					pair.setFirst(newType);
				}
				if (pair.getSecond() == this) {
					pair.setSecond(newType);
				}
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

	public boolean hasFollower() {
		return !followers.isEmpty();
	}
}
