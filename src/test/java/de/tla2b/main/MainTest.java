package de.tla2b.main;

import org.junit.Test;

import de.tla2b.TLA2B;

public class MainTest {

	@Test
	public void testClub() throws Exception {
		String file = "src/test/resources/regression/Club/Club.tla";
		TLA2B.main(new String[] { file });
	}
	
}
