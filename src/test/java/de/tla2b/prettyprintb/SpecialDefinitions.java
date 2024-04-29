package de.tla2b.prettyprintb;

import org.junit.Test;

import static de.tla2b.util.TestUtil.compare;

public class SpecialDefinitions {


	@Test
	public void testVisualisationDefinition() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
			+ "EXTENDS Naturals \n"
			+ "CUSTOM_GRAPH_NODES == { <<a,<<\"lightgray\",b>> >> : a\\in 1..2 , b \\in 1..2} \n"
			+ "CUSTOM_GRAPH_EDGES == 1..10 \n"
			+ "=================================";

		final String expected = "MACHINE Testing\n"
			+ "DEFINITIONS CUSTOM_GRAPH_NODES == UNION(a,b).(a : 1 .. 2 & b : 1 .. 2 | {(a|->(\"lightgray\"|->b))}); \n"
			+ "CUSTOM_GRAPH_EDGES == 1 .. 10;"
			+ "END";
		compare(expected, module);
	}
}
