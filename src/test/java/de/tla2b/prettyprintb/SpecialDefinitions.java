package de.tla2b.prettyprintb;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class SpecialDefinitions {

	
	@Test
	public void testVisualisationDefinition() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Naturals \n"
				+ "CUSTOM_GRAPH_NODES == 1..10 \n"
				+ "CUSTOM_GRAPH_EDGES == 1..10 \n"
				+ "=================================";
		
		final String expected = "MACHINE Testing\n"
				+ "DEFINITIONS CUSTOM_GRAPH_NODES == 1 .. 10; \n"
				+ "CUSTOM_GRAPH_EDGES == 1 .. 10;"
				+ "END";
		compare(expected, module);
	}
}
