package de.tla2b.main;

import org.junit.Test;

import de.tla2b.util.TestUtil;

public class RenamerTest {

	@Test
	public void testKeywords() throws Exception {
		String file = "src/test/resources/renamer/Keywords.tla";
		TestUtil.renamerTest(file);
	}
}
