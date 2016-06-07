package kodkod.test.pardinus.temporal;

import static org.junit.Assert.assertEquals;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.ast.Variable;
import kodkod.engine.ltl2fol.TemporalFormulaSlicer;
import kodkod.instance.Bounds;
import kodkod.instance.Universe;

import org.junit.Test;

public class TemporalSlicerUnitTesting {

	private static Relation Process = Relation.unary("Process");
	private static VarRelation toSend = VarRelation.binary("toSend");
	private static VarRelation elected = VarRelation.unary("elected");
	private static VarRelation naryRelation = VarRelation.nary("naryRelation", 4);

	private static Relation succ = Relation.binary("succ");

	private static Relation pfirst = Relation.unary("pfirst");
	private static Relation plast = Relation.unary("plast");
	private static VarRelation pord = VarRelation.binary("pord");
	private static VarRelation tord = VarRelation.binary("tord");

	private static Relation succ1 = Relation.binary("succ1");
	private static Relation succ2 = Relation.binary("succ2");

	TemporalFormulaSlicer slicingDynamicFormulas;

	@Test
	public final void test1() {
		Formula succFunction = tord.partialFunction(pfirst, plast);

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();

		Formula total = Formula.and(new Formula[] { localFormula2, succFunction, var4, var5, initial2 });

		String resultDynamic = "(TOTAL_ORDERING(pord, Process, pfirst, plast) && FUNCTION(tord, pfirst ->lone plast) && (elected in Process) && next((all p: one Process | (((toSend . p) = (toSend . p)) release lone (Process . toSend')))))";
		String resultStatic = "(succ in (Process -> Process))";

		Universe universe = new Universe();
		Bounds bounds = new Bounds(universe);

		slicingDynamicFormulas = new TemporalFormulaSlicer(total, bounds);
		Formula dynamicRel = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
		Formula staticRel = Formula.and(slicingDynamicFormulas.getStaticFormulas());
		assertEquals(dynamicRel.toString(), resultDynamic);
		assertEquals(staticRel.toString(), resultStatic);
		assertEquals(slicingDynamicFormulas.getDynamicFormulas().size(), 4);
		assertEquals(slicingDynamicFormulas.getStaticFormulas().size(), 1);

	}

	@Test
	public final void test2() {
		Formula succFunction = pord.partialFunction(pfirst, plast);

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Formula localFormula1 = localFormula2.and(var4.and(var5));

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();

		Formula total = Formula.and(new Formula[] { localFormula1, initial2 });

		String resultDynamic = "(TOTAL_ORDERING(pord, Process, pfirst, plast) && (elected in Process) && next((all p: one Process | (((toSend . p) = (toSend . p)) release lone (Process . toSend')))))";
		String resultStatic = "(succ in (Process -> Process))";

		total.accept(slicingDynamicFormulas);
		Formula dynamicRel = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
		Formula staticRel = Formula.and(slicingDynamicFormulas.getStaticFormulas());
		assertEquals(dynamicRel.toString(), resultDynamic);
		assertEquals(staticRel.toString(), resultStatic);
		assertEquals(slicingDynamicFormulas.getDynamicFormulas().size(), 3);
		assertEquals(slicingDynamicFormulas.getStaticFormulas().size(), 1);

	}

	@Test
	public final void test3() {
		Formula succFunction = pord.partialFunction(pfirst, plast);

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Formula localFormula1 = localFormula2.and(var4.and(var5.and(succFunction)));

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();

		Formula total = Formula.and(new Formula[] { localFormula1, initial2 });

		String resultDynamic = "(TOTAL_ORDERING(pord, Process, pfirst, plast) && (elected in Process) && FUNCTION(pord, pfirst ->lone plast) && next((all p: one Process | (((toSend . p) = (toSend . p)) release lone (Process . toSend')))))";
		String resultStatic = "(succ in (Process -> Process))";

		total.accept(slicingDynamicFormulas);
		Formula dynamicRel = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
		Formula staticRel = Formula.and(slicingDynamicFormulas.getStaticFormulas());
		assertEquals(dynamicRel.toString(), resultDynamic);
		assertEquals(staticRel.toString(), resultStatic);
		assertEquals(slicingDynamicFormulas.getDynamicFormulas().size(), 4);
		assertEquals(slicingDynamicFormulas.getStaticFormulas().size(), 1);
	}

	@Test
	public final void test4() {
		Formula succFunction = pord.partialFunction(pfirst, plast);

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Formula localFormula1 = Formula.and(localFormula2, var4, var5, succFunction);

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();

		Formula total = Formula.and(new Formula[] { localFormula1, initial2 });

		String resultDynamic = "(TOTAL_ORDERING(pord, Process, pfirst, plast) && (elected in Process) && FUNCTION(pord, pfirst ->lone plast) && next((all p: one Process | (((toSend . p) = (toSend . p)) release lone (Process . toSend')))))";
		String resultStatic = "(succ in (Process -> Process))";

		total.accept(slicingDynamicFormulas);
		Formula dynamicRel = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
		Formula staticRel = Formula.and(slicingDynamicFormulas.getStaticFormulas());
		assertEquals(dynamicRel.toString(), resultDynamic);
		assertEquals(staticRel.toString(), resultStatic);
		assertEquals(slicingDynamicFormulas.getDynamicFormulas().size(), 4);
		assertEquals(slicingDynamicFormulas.getStaticFormulas().size(), 1);
	}

	@Test
	public final void test5() {
		Formula var1 = succ1.in(Process.product(Process)).implies(
				succ2.in(Process.product(Process)).and(succ.in(Process.product(Process))));
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).until(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();
		Formula var12 = succ2.in(Process.product(Process));
		Formula third = Formula.and(var1, var12, initial);// second.and(var13);
		// -------------

		Formula var11 = succ2.in(Process.product(Process));
		Formula third1 = var11.and(third);// second.and(var13);

		// ----------------

		Formula succFunction = pord.partialFunction(pfirst, plast);
		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();

		Formula total = Formula.and(new Formula[] { third1, localFormula2, succFunction, var4, var5, initial2 });

		String resultDynamic = "(next((all p: one Process | (((toSend . p) = (toSend . p)) until lone (Process . toSend')))) && TOTAL_ORDERING(pord, Process, pfirst, plast) && FUNCTION(pord, pfirst ->lone plast) && (elected in Process) && next((all p: one Process | (((toSend . p) = (toSend . p)) release lone (Process . toSend')))))";
		String resultStatic = "((succ2 in (Process -> Process)) && ((succ1 in (Process -> Process)) => ((succ2 in (Process -> Process)) && (succ in (Process -> Process)))) && (succ2 in (Process -> Process)) && (succ in (Process -> Process)))";

		total.accept(slicingDynamicFormulas);
		Formula dynamicRel = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
		Formula staticRel = Formula.and(slicingDynamicFormulas.getStaticFormulas());
		assertEquals(dynamicRel.toString(), resultDynamic);
		assertEquals(staticRel.toString(), resultStatic);
		assertEquals(slicingDynamicFormulas.getDynamicFormulas().size(), 5);
		assertEquals(slicingDynamicFormulas.getStaticFormulas().size(), 4);
	}

	@Test
	public final void test6() {
		Formula var1 = succ1.in(Process.product(Process)).implies(
				succ2.in(Process.product(Process)).and(succ.in(Process.product(Process))));
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).until(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();
		Formula var12 = succ2.in(Process.product(Process));
		Formula third = Formula.and(var1, var12, initial);// second.and(var13);
		// -------------

		Formula var11 = succ2.in(Process.product(Process));
		Formula third1 = var11.and(third);// second.and(var13);

		// ----------------

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);
		Formula var6 = var5.and(var4.and(localFormula2));

		// ----------------
		Formula succFunction = pord.partialFunction(pfirst, plast);
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();

		Formula total = Formula.and(new Formula[] { third1, var6, succFunction, initial2 });

		String resultDynamic = "(next((all p: one Process | (((toSend . p) = (toSend . p)) until lone (Process . toSend')))) && (elected in Process) && TOTAL_ORDERING(pord, Process, pfirst, plast) && FUNCTION(pord, pfirst ->lone plast) && next((all p: one Process | (((toSend . p) = (toSend . p)) release lone (Process . toSend')))))";
		String resultStatic = "((succ2 in (Process -> Process)) && ((succ1 in (Process -> Process)) => ((succ2 in (Process -> Process)) && (succ in (Process -> Process)))) && (succ2 in (Process -> Process)) && (succ in (Process -> Process)))";

		total.accept(slicingDynamicFormulas);
		Formula dynamicRel = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
		Formula staticRel = Formula.and(slicingDynamicFormulas.getStaticFormulas());
		assertEquals(dynamicRel.toString(), resultDynamic);
		assertEquals(staticRel.toString(), resultStatic);
		assertEquals(slicingDynamicFormulas.getDynamicFormulas().size(), 5);
		assertEquals(slicingDynamicFormulas.getStaticFormulas().size(), 4);
	}

	@Test
	public final void test7() {
		Formula var1 = succ1.in(Process.product(Process));
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).until(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();
		Formula first = initial.and(var1);

		Formula var12 = succ2.in(Process.product(Process));

		// -------------
		Formula var13 = succ2.in(Process.product(Process));
		Formula third = Formula.and(new Formula[] { var13, var12, first });
		// -------------

		Formula var11 = succ2.in(Process.product(Process));
		Formula third1 = var11.and(third);

		// ----------------

		Formula succFunction = pord.partialFunction(pfirst, plast);
		Formula var5 = elected.in(Process);

		Formula two = Formula.and(new Formula[] { succFunction, var5, third1 });

		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.post()).lone())
				.forAll(var3.oneOf(Process)).next();

		Formula total = initial2.and(localFormula2.and(var4)).and(two);

		String resultDynamic = "(next((all p: one Process | (((toSend . p) = (toSend . p)) release lone (Process . toSend')))) && TOTAL_ORDERING(pord, Process, pfirst, plast) && FUNCTION(pord, pfirst ->lone plast) && (elected in Process) && next((all p: one Process | (((toSend . p) = (toSend . p)) until lone (Process . toSend')))))";
		String resultStatic = "((succ in (Process -> Process)) && (succ2 in (Process -> Process)) && (succ2 in (Process -> Process)) && (succ2 in (Process -> Process)) && (succ1 in (Process -> Process)))";

		total.accept(slicingDynamicFormulas);
		Formula dynamicRel = Formula.and(slicingDynamicFormulas.getDynamicFormulas());
		Formula staticRel = Formula.and(slicingDynamicFormulas.getStaticFormulas());
		assertEquals(dynamicRel.toString(), resultDynamic);
		assertEquals(staticRel.toString(), resultStatic);
		assertEquals(slicingDynamicFormulas.getDynamicFormulas().size(), 5);
		assertEquals(slicingDynamicFormulas.getStaticFormulas().size(), 5);
	}

	public static void p(String s) {
		System.out.println(s);
	}
}
