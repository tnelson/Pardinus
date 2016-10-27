package kodkod.test.pardinus.temporal;

import java.util.HashMap;
import java.util.Map;

import kodkod.ast.*;
import kodkod.engine.ltl2fol.LTL2FOLTranslator;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

public class TemporalTranslatorUnitTesting {

	private static Relation Process = Relation.unary("Process");
	private static VarRelation toSend = VarRelation.binary("toSend");
	private static VarRelation elected = VarRelation.unary("elected");
	private static VarRelation naryRelation = VarRelation.nary("naryRelation", 4);

	private static Relation succ = Relation.binary("succ");

	private static Relation pfirst = Relation.unary("pfirst");
	private static Relation plast = Relation.unary("plast");
	private static VarRelation pord = VarRelation.binary("pord");

	public TemporalTranslatorUnitTesting() {
		Map<String, Relation> rels = new HashMap<String, Relation>();
		rels.put(toSend.name(), Relation.nary(toSend.name(), toSend.arity() + 1));
		rels.put(elected.name(), Relation.nary(elected.name(), elected.arity() + 1));
		rels.put(naryRelation.name(), Relation.nary(naryRelation.name(), naryRelation.arity() + 1));
		rels.put(pord.name(), Relation.nary(pord.name(), pord.arity() + 1));
	}

	/*
	 * 
	 * /*Declarations
	 */
	@Test
	public final void declaration_one() {
		Formula initial = elected.in(Process);
		String result = "((elected . init) in Process)";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void declaration_two() {
		Formula initial = toSend.in(Process.product(Process));
		String result = "((toSend . init) in (Process -> Process))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void declaration_three() {
		Formula initial = naryRelation.in(Process.product(Process).product(Process).product(Process));
		String result = "((naryRelation . init) in (((Process -> Process) -> Process) -> Process))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void declaration_totalFunction() {
		Formula initial = pord.function(pfirst, plast);
		String result = "((pord in ((pfirst -> plast) -> Time)) && (all [t: one Time, d: one pfirst] | one (d . (pord . t))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void declaration_partialFunction() {
		Formula initial = pord.partialFunction(pfirst, plast);
		String result = "((pord in ((pfirst -> plast) -> Time)) && (all [t: one Time, d: one pfirst] | lone (d . (pord . t))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void declaration_normal_partialFunction() {
		Formula initial = succ.partialFunction(pfirst, plast);
		String result = "FUNCTION(succ, pfirst ->lone plast)";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void declaration_normal_function() {
		Formula initial = succ.partialFunction(pfirst, plast);
		String result = "FUNCTION(succ, pfirst ->lone plast)";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	/* Temporal */

	@Test
	public final void simple_post_init() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.prime().join(var3)).and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process));
		String result = "(some (init . nextt) && (all p: one Process | ((p in ((toSend . (init . nextt)) . p)) && (p in ((toSend . init) . p)))))";

		Formula f = LTL2FOLTranslator.translate(initial);
		assertEquals(f.toString(), result);
	}

	@Test
	public final void simple_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process))
				.always();
		String result = "(one loop && (all t0: one (init . *nextt) | (all p: one Process | ((p in ((toSend . t0) . p)) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_next() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process)).next();
		String result = "(some (init . nextt) && (all p: one Process | ((p in ((toSend . (init . nextt)) . p)) && (p in ((toSend . (init . nextt)) . p)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_eventually() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process))
				.eventually();
		String result = "(some t0: one (init . *nextt) | (all p: one Process | ((p in ((toSend . t0) . p)) && (p in ((toSend . t0) . p)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_historically() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process))
				.historically();
		String result = "(all t0: one (init . *~nextt) | (all p: one Process | ((p in ((toSend . t0) . p)) && (p in ((toSend . t0) . p)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_once() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process)).once();
		String result = "(some t0: one (init . *~nextt) | (all p: one Process | ((p in ((toSend . t0) . p)) && (p in ((toSend . t0) . p)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_post_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.join(toSend.prime()).eq(var3.join(toSend)).always();
		String result = "(one loop && (all t0: one (init . *nextt) | (some (t0 . nextt) && ((p . (toSend . (t0 . nextt))) = (p . (toSend . t0))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_post_next_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.join(toSend.prime()).eq(var3.join(toSend)).next().always();
		String result = "(one loop && (all t0: one (init . *nextt) | (some ((t0 . nextt) . nextt) && (some (t0 . nextt) && ((p . (toSend . ((t0 . nextt) . nextt))) = (p . (toSend . (t0 . nextt))))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_post_eventually() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.join(toSend.prime()).eq(var3.join(toSend)).eventually();
		String result = "(some t0: one (init . *nextt) | (some (t0 . nextt) && ((p . (toSend . (t0 . nextt))) = (p . (toSend . t0)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_until() {
		Formula initial = Process.join(toSend).some().until(Process.join(toSend).lone());
		String result = "(some t0: one (init . *nextt) | (lone (Process . (toSend . t0)) && (all t1: one ((init . *nextt) & (^nextt . t0)) | some (Process . (toSend . t1)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_release() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend).lone())
				.forAll(var3.oneOf(Process));
		String result = "(all p: one Process | ((one loop && (all t0: one (init . *nextt) | lone (Process . (toSend . t0)))) || (some t1: one (init . *nextt) | ((((toSend . t1) . p) = ((toSend . t1) . p)) && (all t2: one ((init . *nextt) & (*nextt . t1)) | lone (Process . (toSend . t2)))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_release_post() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process));
		String result = "(all p: one Process | ((one loop && (all t0: one (init . *nextt) | (some (t0 . nextt) && lone (Process . (toSend . (t0 . nextt)))))) || (some t1: one (init . *nextt) | ((((toSend . t1) . p) = ((toSend . t1) . p)) && (all t2: one ((init . *nextt) & (*nextt . t1)) | (some (t2 . nextt) && lone (Process . (toSend . (t2 . nextt)))))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	/* Out of the root */

	@Test
	public final void simple_always_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).always().and(var3.in(toSend.join(var3)))
				.forAll(var3.oneOf(Process)).always();
		String result = "(one loop && (all t0: one (init . *nextt) | (all p: one Process | ((one loop && (all t1: one (t0 . *nextt) | (p in ((toSend . t1) . p)))) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_always_eventually() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).always().and(var3.in(toSend.join(var3)))
				.forAll(var3.oneOf(Process)).eventually();
		String result = "(some t0: one (init . *nextt) | (all p: one Process | ((one loop && (all t1: one (t0 . *nextt) | (p in ((toSend . t1) . p)))) && (p in ((toSend . t0) . p)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_once_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).once().and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process))
				.always();
		String result = "(one loop && (all t0: one (init . *nextt) | (all p: one Process | ((some t1: one (t0 . *~nextt) | (p in ((toSend . t1) . p))) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_historically_eventually() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).historically().and(var3.in(toSend.join(var3)))
				.forAll(var3.oneOf(Process)).eventually();
		String result = "(some t0: one (init . *nextt) | (all p: one Process | ((all t1: one (t0 . *~nextt) | (p in ((toSend . t1) . p))) && (p in ((toSend . t0) . p)))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_next_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).next().and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process))
				.always();
		String result = "(one loop && (all t0: one (init . *nextt) | (all p: one Process | ((some (t0 . nextt) && (p in ((toSend . (t0 . nextt)) . p))) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_previous_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).previous().and(var3.in(toSend.join(var3)))
				.forAll(var3.oneOf(Process)).always();
		String result = "(one loop && (all t0: one (init . *nextt) | (all p: one Process | ((some (t0 . ~nextt) && (p in ((toSend . (t0 . ~nextt)) . p))) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_previous_always_eventually() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).previous()
				.and(var3.in(toSend.join(var3)).always().and(var3.in(toSend.join(var3)))).forAll(var3.oneOf(Process))
				.eventually();
		String result = "(some t0: one (init . *nextt) | (all p: one Process | ((some (t0 . ~nextt) && (p in ((toSend . (t0 . ~nextt)) . p))) && ((one loop && (all t1: one (t0 . *nextt) | (p in ((toSend . t1) . p)))) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_next_eventually_eventually() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).next()
				.and(var3.in(toSend.join(var3)).eventually().and(var3.in(toSend.join(var3))))
				.forAll(var3.oneOf(Process)).eventually();
		String result = "(some t0: one (init . *nextt) | (all p: one Process | ((some (t0 . nextt) && (p in ((toSend . (t0 . nextt)) . p))) && ((some t1: one (t0 . *nextt) | (p in ((toSend . t1) . p))) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_until_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = Process.join(toSend).some().until(var3.in(toSend.join(var3))).and(var3.in(toSend.join(var3)))
				.forAll(var3.oneOf(Process)).always();
		String result = "(one loop && (all t0: one (init . *nextt) | (all p: one Process | ((some t1: one (t0 . *nextt) | ((p in ((toSend . t1) . p)) && (all t2: one ((t0 . *nextt) & (^nextt . t1)) | some (Process . (toSend . t2))))) && (p in ((toSend . t0) . p))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_always_until_eventually() {
		Variable var3 = Variable.unary("p");
		Formula initial = var3.in(toSend.join(var3)).always()
				.and(Process.join(toSend).some().until(var3.in(toSend.join(var3)))).forAll(var3.oneOf(Process))
				.eventually();
		String result = "(some t0: one (init . *nextt) | (all p: one Process | ((one loop && (all t1: one (t0 . *nextt) | (p in ((toSend . t1) . p)))) && (some t2: one (t0 . *nextt) | ((p in ((toSend . t2) . p)) && (all t3: one ((t0 . *nextt) & (^nextt . t2)) | some (Process . (toSend . t3))))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);

	}

	@Test
	public final void simple_release_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).release(Process.join(toSend).lone())
				.forAll(var3.oneOf(Process)).always();
		String result = "(one loop && (all t0: one (init . *nextt) | (all p: one Process | ((one loop && (all t1: one (t0 . *nextt) | lone (Process . (toSend . t1)))) || (some t2: one (t0 . *nextt) | ((((toSend . t2) . p) = ((toSend . t2) . p)) && (all t3: one ((t0 . *nextt) & (*nextt . t2)) | lone (Process . (toSend . t3)))))))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void simple_until1_always() {
		Variable var3 = Variable.unary("p");
		Formula initial = Process.join(toSend).some().until(var3.in(toSend.prime().join(var3)).always())
				.and(var3.in(toSend.join(var3))).forAll(var3.oneOf(Process));
		String result = "(all p: one Process | ((some t0: one (init . *nextt) | ((one loop && (all t1: one (t0 . *nextt) | (some (t1 . nextt) && (p in ((toSend . (t1 . nextt)) . p))))) && (all t2: one ((init . *nextt) & (^nextt . t0)) | some (Process . (toSend . t2))))) && (p in ((toSend . init) . p))))";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void nested_quantifiers() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).eventually();
		String result = "";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void nested_quantifiers2() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).and(toSend.prime().prime().prime().in(toSend))
				.eventually();
		String result = "";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	@Test
	public final void nested_quantifiers3() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).and(toSend.prime().prime().prime().in(toSend));
		String result = "";
		assertEquals(LTL2FOLTranslator.translate(initial).toString(), result);
	}

	public static void p(String s) {
		System.out.println(s);
	}
}
