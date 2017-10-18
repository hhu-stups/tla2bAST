package de.tla2b.main;

import java.io.File;

import org.junit.Test;

import de.tla2b.TLA2B;

public class MainTest {

	@Test
	public void testClub() throws Exception {
		String dir = "src/test/resources/regression/Club/";
		TLA2B.main(new String[] { dir + "Club.tla" });
		new File(dir + "Club_tla.txt").deleteOnExit();
	}

}
