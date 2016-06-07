package kodkod.test.pardinus.temporal;

import kodkod.ast.*;
import kodkod.engine.ltl2fol.NNFReplacer;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * Created by Eduardo Pessoa on 11/04/16.
 */
public class NNFTranslatorUnitTesting {

	private static VarRelation A = VarRelation.unary("A");
	private static VarRelation B = VarRelation.unary("B");
	private static VarRelation C = VarRelation.binary("C");
	private static VarRelation toSend = VarRelation.binary("toSend");
	private static Relation Process = Relation.unary("Process");

	NNFReplacer nnf = new NNFReplacer();

	@Test
	public final void test1() {
		Formula initial = A.lone().implies(B.some());
		String result = "(!lone A || some B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test2() {
		Formula initial = A.lone().implies(B.some()).not();
		String result = "(lone A && !some B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test3() {
		Formula initial = A.lone().iff(B.some());
		String result = "((lone A || !some B) && (!lone A || some B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test4() {
		Formula initial = A.lone().iff(B.some()).not();
		String result = "((!lone A && some B) || (lone A && !some B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test5() {
		Formula initial = A.some().and(B.lone()).not();
		String result = "(!some A || !lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test6() {
		Formula initial = A.some().or(B.lone()).not();
		String result = "(!some A && !lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test7() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().and(B.lone()).forAll(v.oneOf(A)).not();
		String result = "(some v: one A | (!some (C . v) || !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test8() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).forSome(v.oneOf(A)).not();
		String result = "(all v: one A | (!some (C . v) && !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test9() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).always().not();
		String result = "eventually((!some (C . v) && !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test10() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().and(B.lone()).eventually().not();
		String result = "always((!some (C . v) || !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test11() {
		Formula initial = A.some().and(A.some().implies(B.one())).not();
		String result = "(!some A || (some A && !one B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test12() {
		Formula initial = A.some().and(A.some().implies(B.one()).not()).not();
		String result = "(!some A || (!some A || one B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test13() {
		Formula initial = A.some().and(A.some().not().implies(B.one()).not()).not();
		String result = "(!some A || (some A || one B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test14() {
		Formula initial = A.some().or(A.some().not().implies(B.one()).not()).not();
		String result = "(!some A && (some A || one B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test15() {
		Formula initial = A.some().and(A.some().implies(B.one()).not());
		String result = "(some A && (some A && !one B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test16() {
		Formula initial = A.some().implies(B.one()).not().implies(A.some().implies(B.one()).not());
		String result = "((!some A || one B) || (some A && !one B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test17() {
		Formula initial = A.some().or(A.some().implies(B.one())).not();
		String result = "(!some A && (some A && !one B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test18() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().not().and(B.lone()).forSome(v.oneOf(A)).not();
		String result = "(all v: one A | (some (C . v) || !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test19() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().forSome(v.oneOf(A)).not().iff(C.join(v).lone());
		String result = "(((all v: one A | !some (C . v)) || !lone (C . v)) && ((some v: one A | some (C . v)) || lone (C . v)))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test20() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().forAll(v.oneOf(A)).always().not().iff(C.join(v).lone());
		String result = "((eventually((some v: one A | !some (C . v))) || !lone (C . v)) && (always((all v: one A | some (C . v))) || lone (C . v)))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test21() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().always().forAll(v.oneOf(A)).not();
		String result = "(some v: one A | eventually(!some (C . v)))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test22() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().and(B.lone()).once().not();
		String result = "historically((!some (C . v) || !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test23() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().forAll(v.oneOf(A)).historically().not().iff(C.join(v).lone());
		String result = "((once((some v: one A | !some (C . v))) || !lone (C . v)) && (historically((all v: one A | some (C . v))) || lone (C . v)))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test24() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().historically().forAll(v.oneOf(A)).not();
		String result = "(some v: one A | once(!some (C . v)))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test25() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).once().not();
		String result = "historically((!some (C . v) && !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test26() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).next().not();
		String result = "next((!some (C . v) && !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test27() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.and(
				new Formula[] { C.join(v).some().or(B.lone()).next(), A.lone().implies(B.some()), B.lone().not() })
				.not();
		String result = "(next((!some (C . v) && !lone B)) || (lone A && !some B) || lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test28() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.and(
				new Formula[] { C.join(v).some().or(B.lone()).next(), A.lone().implies(B.some()), B.lone() }).not();
		String result = "(next((!some (C . v) && !lone B)) || (lone A && !some B) || !lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test29() {
		Variable v = Variable.unary("v");
		Formula initial = Formula
				.and(new Formula[] { C.join(v).some().and(B.lone()).next().not(), A.lone().implies(B.some()),
						B.lone().not() }).not();
		String result = "(next((some (C . v) && lone B)) || (lone A && !some B) || lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test30() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.and(
				new Formula[] { C.join(v).some().and(B.lone()).next(), A.lone().implies(B.some()), B.lone() }).not();
		String result = "(next((!some (C . v) || !lone B)) || (lone A && !some B) || !lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test31() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.or(
				new Formula[] { C.join(v).some().and(B.lone()).always(), A.lone().not().implies(B.some()), B.lone() })
				.not();
		String result = "(eventually((!some (C . v) || !lone B)) && (!lone A && !some B) && !lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test32() {
		Variable v = Variable.unary("v");
		Formula initial = C.join(v).some().or(B.lone()).previous().not();
		String result = "previous((!some (C . v) && !lone B))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test33() {
		Variable v = Variable.unary("v");
		Formula initial = Formula.and(
				new Formula[] { C.join(v).some().or(B.lone()).previous(), A.lone().implies(B.some()), B.lone().not() })
				.not();
		String result = "(previous((!some (C . v) && !lone B)) || (lone A && !some B) || lone B)";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test34() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).not();
		String result = "(some p: one Process | (!((toSend . p) = (toSend . p)) until !lone (Process . toSend')))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test35() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).until(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).not();
		String result = "(some p: one Process | (!((toSend . p) = (toSend . p)) release !lone (Process . toSend')))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test36() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).and(Process.join(toSend.post()).one())
				.until(Process.join(toSend.post()).lone()).forAll(var3.oneOf(Process)).not();
		String result = "(some p: one Process | ((!((toSend . p) = (toSend . p)) || !one (Process . toSend')) release !lone (Process . toSend')))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	@Test
	public final void test37() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).and(Process.join(toSend.post()).one())
				.until(Process.join(toSend.post()).lone()).not();
		String result = "((!((toSend . p) = (toSend . p)) || !one (Process . toSend')) release !lone (Process . toSend'))";
		assertEquals(initial.accept(nnf).toString(), result);
	}

	public static void p(String s) {
		System.out.println(s);
	}

}
