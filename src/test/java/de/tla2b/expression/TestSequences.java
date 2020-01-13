package de.tla2b.expression;

import static de.tla2b.util.TestUtil.compareExpr;

import org.junit.Test;

public class TestSequences {

	@Test
	public void testAppend() throws Exception {
		compareExpr("[1] <- 2", "Append(<<1>>, 2)");
	}

	@Test
	public void testHead() throws Exception {
		compareExpr("first([1, 2, 3])", "Head(<<1,2,3>>)");
	}

	@Test
	public void testTail() throws Exception {
		compareExpr("tail([1, 2, 3])", "Tail(<<1,2,3>>)");
	}

}
