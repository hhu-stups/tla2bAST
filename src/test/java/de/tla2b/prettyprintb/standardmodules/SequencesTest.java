package de.tla2b.prettyprintb.standardmodules;

import static de.tla2b.util.TestUtil.compare;

import org.junit.Test;

public class SequencesTest {

	@Test
	public void testSeq() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME <<1,2>> \\in Seq({1,2})\n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES [1,2] : seq({1,2}) \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testLen() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME Len(<<1,2>>) = 2\n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES size([1,2]) = 2 \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testConcatenation() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME <<1,2>> \\o <<3>> = <<1,2,3>>\n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES [1,2] ^ [3] = [1,2,3] \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testAppend() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME Append(<<1>>, 2) = <<1,2>> \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES [1] <- 2 = [1,2] \n"
				+ "END";
		compare(expected, module);
	}
	
	
	@Test
	public void testHead() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME Head(<<1,2>>) = 1 \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES first([1,2]) = 1 \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testTail() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME Tail(<<1,2,3>>) = <<2,3>> \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES tail([1,2,3]) = [2,3] \n"
				+ "END";
		compare(expected, module);
	}
	
	@Test
	public void testSubSeq() throws Exception {
		final String module = "-------------- MODULE Testing ----------------\n"
				+ "EXTENDS Sequences \n"
				+ "ASSUME SubSeq(<<1,2,3,4,5>>, 2, 3) = <<2,3>> \n"
				+ "=================================";
		final String expected = "MACHINE Testing\n"
				+ "PROPERTIES ([1,2,3,4,5] /|\\ 3) \\|/ 2 = [2,3] \n"
				+ "END";
		compare(expected, module);
	}
	
	
}
