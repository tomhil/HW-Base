package il.ac.bgu.cs.formalmethodsintro.base.ex3;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.and;
import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.next;
import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.not;
import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.true_;
import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.until;
import static org.junit.Assert.assertEquals;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.AP;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;

public class LTLTest2 {

	FvmFacade fvmFacadeImpl = FvmFacade.get();

	@Test
	public void test1() {
		AP<String> p = new AP<>("p");
		AP<String> q = new AP<>("q");
		AP<String> s = new AP<>("s");

		LTL<String> ltl = and(until(p, q), until(q, s));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

		assertEquals(aut, "(p U q) /\\ (q U s)");
	}

	@Test
	public void test2() {
		AP<String> p = new AP<>("p");
		AP<String> q = new AP<>("q");
		AP<String> s = new AP<>("s");

		LTL<String> ltl = and(not(until(p, q)), until(q, s));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

		assertEquals(aut, "~(p U q) /\\ (q U s)");
	}

	@Test
	public void test3() {
		AP<String> p = new AP<>("p");

		LTL<String> ltl = until(true_(), p);

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

		assertEquals(aut, "true U p");
	}

	@Test
	public void test4() {
		AP<String> p = new AP<>("p");
		AP<String> q = new AP<>("q");
		AP<String> s = new AP<>("s");

		LTL<String> ltl = until(not(p), and(p, and(next(s), next(next(q)))));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

		assertEquals(aut, "~p U (p /\\ ()s /\\ ()()q)");
	}

	@Test
	public void test5() {
		AP<String> p = new AP<>("p");
		AP<String> q = new AP<>("q");
		AP<String> s = new AP<>("s");

		LTL<String> ltl = until(p, until(q, s));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

		assertEquals(aut, "p U (q U s)");
	}

}
