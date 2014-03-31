/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.exceptions;

@SuppressWarnings("serial")
public class SemanticErrorException extends TLA2BException {
	
	public SemanticErrorException(String e){
		super(e);
	}

}
