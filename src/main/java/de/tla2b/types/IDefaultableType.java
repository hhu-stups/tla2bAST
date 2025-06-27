package de.tla2b.types;

import de.tla2b.exceptions.TLA2BException;

public interface IDefaultableType {

	TLAType setToDefault() throws TLA2BException;

}
