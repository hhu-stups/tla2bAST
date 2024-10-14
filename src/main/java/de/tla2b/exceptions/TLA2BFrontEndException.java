package de.tla2b.exceptions;

import tla2sany.modanalyzer.SpecObj;

public class TLA2BFrontEndException extends TLA2BException {

	public SpecObj spec;

	public TLA2BFrontEndException(String e) {
		super(e);
	}

	public TLA2BFrontEndException(String string, SpecObj spec) {
		super(string);
		this.spec = spec;
	}
}
