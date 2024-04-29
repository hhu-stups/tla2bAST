package de.tla2b.main;

import de.tla2b.TLA2B;
import org.junit.Test;

import java.io.File;

public class MainTest {

	@Test
	public void testClub() throws Exception {
		String dir = "src/test/resources/regression/Club/";
		TLA2B.main(new String[]{dir + "Club.tla"});
		new File(dir + "Club_tla.txt").deleteOnExit();
	}

}
