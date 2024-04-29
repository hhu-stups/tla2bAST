package de.tla2b.main;

import de.tla2b.util.TestUtil;
import org.junit.Test;

public class RenamerTest {

	@Test
	public void testKeywords() throws Exception {
		String file = "src/test/resources/renamer/Keywords.tla";
		TestUtil.renamerTest(file);
	}
}
