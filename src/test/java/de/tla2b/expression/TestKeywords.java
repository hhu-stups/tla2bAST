/**
 * @author Dominik Hansen <Dominik.Hansen at hhu.de>
 **/

package de.tla2b.expression;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compareExpr;

public class TestKeywords {

	@Test
	public void testTRUE() throws Exception {
		compareExpr("TRUE", "TRUE");
	}

	@Test
	public void testNat() throws Exception {
		compareExpr("NATURAL", "Nat");
	}

	@Test
	public void testExcept() throws Exception {
		compareExpr("bool(x = a <+ {1 |-> 1})", "x = [a EXCEPT ![1] = 1]");
	}

	@Test
	public void testCardinality() throws Exception {
		compareExpr("card({1, 2, 3})", "Cardinality({1,2,3})");
	}

	@Test
	public void testDom() throws Exception {
		compareExpr("bool(dom_1 = 1)", "dom = 1");
	}
}
