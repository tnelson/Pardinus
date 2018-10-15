package kodkod.test.pardinus.temporal;

import java.util.HashMap;
import java.util.Map;

import kodkod.ast.*;
import kodkod.engine.ltl2fol.LTL2FOLTranslator;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

import static kodkod.engine.ltl2fol.TemporalTranslator.FIRST;
import static kodkod.engine.ltl2fol.TemporalTranslator.TRACE;
import static kodkod.engine.ltl2fol.TemporalTranslator.PREFIX;

public class TemporalTranslatorTests {

	private static Relation Process = Relation.unary("Process");
	private static VarRelation toSend = VarRelation.binary("toSend");
	private static VarRelation elected = VarRelation.unary("elected");
	private static VarRelation naryRelation = VarRelation.nary("naryRelation", 4);

	private static Relation succ = Relation.binary("succ");

	private static Relation pfirst = Relation.unary("pfirst");
	private static Relation plast = Relation.unary("plast");
	private static VarRelation pord = VarRelation.binary("pord");

	public TemporalTranslatorTests() {
		Map<String, Relation> rels = new HashMap<String, Relation>();
		rels.put(toSend.name(), Relation.nary(toSend.name(), toSend.arity() + 1));
		rels.put(elected.name(), Relation.nary(elected.name(), elected.arity() + 1));
		rels.put(naryRelation.name(), Relation.nary(naryRelation.name(), naryRelation.arity() + 1));
		rels.put(pord.name(), Relation.nary(pord.name(), pord.arity() + 1));
	}
	
	/* Declarations */
	@Test
	public final void test() {
		Formula initial = (elected.eq(elected.prime()).not()).next();
		Formula result = elected.expanded.join(FIRST).in(Process);
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	/* Declarations */
	@Test
	public final void declaration_one() {
		Formula initial = elected.in(Process);
		Formula result = elected.expanded.join(FIRST).in(Process);
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void declaration_two() {
		Formula initial = toSend.in(Process.product(Process));
		Formula result = toSend.expanded.join(FIRST).in(Process.product(Process));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void declaration_three() {
		Formula initial = naryRelation.in(Process.product(Process).product(Process).product(Process));
		Formula result = naryRelation.expanded.join(FIRST).in(Process.product(Process).product(Process).product(Process));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void declaration_totalFunction() {
		Formula initial = pord.function(pfirst, plast);
		Variable d = Variable.unary("v"+pord);
		Variable t = Variable.unary("t0");
		Formula result = ((pord.expanded.join(t).in(pfirst.product(plast)))
				.and((d.join(pord.expanded.join(t)).one()).forAll(d.oneOf(pfirst))).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void declaration_partialFunction() {
		Formula initial = pord.partialFunction(pfirst, plast);
		Variable d = Variable.unary("v"+pord);
		Variable t = Variable.unary("t0");
		Formula result = ((pord.expanded.join(t).in(pfirst.product(plast)))
				.and((d.join(pord.expanded.join(t)).lone()).forAll(d.oneOf(pfirst))).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void declaration_normal_partialFunction() {
		Formula initial = succ.partialFunction(pfirst, plast);
		Formula result = succ.partialFunction(pfirst, plast);
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void declaration_normal_function() {
		Formula initial = succ.partialFunction(pfirst, plast);
		Formula result = succ.partialFunction(pfirst, plast);
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	/* Temporal */
	@Test
	public final void simple_post_init() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.prime().join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process));
		Formula result = FIRST.join(TRACE).some().and(v.in(toSend.expanded.join(FIRST.join(TRACE)).join(v)).and(v.in(toSend.expanded.join(FIRST).join(v))).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_always() {
		Variable v = Variable.unary("p");
		Variable t = Variable.unary("t0");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Formula result = (v.in(toSend.expanded.join(t).join(v)).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_next() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).next();
		Formula result = FIRST.join(TRACE).some().and(v.in(toSend.expanded.join(FIRST.join(TRACE)).join(v)).and(v.in(toSend.expanded.join(FIRST.join(TRACE)).join(v))).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void simple_prime() {
		Variable v = Variable.unary("p");
		Formula initial = (toSend.join(v).prime()).eq(toSend.join(v)).forAll(v.oneOf(Process));
		Formula result = FIRST.join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE)).join(v).eq(toSend.expanded.join(FIRST).join(v)).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void simple_double_prime() {
		Variable v = Variable.unary("p");
		Formula initial = (toSend.join(v).prime()).eq(toSend.prime().join(v).prime()).forAll(v.oneOf(Process));
		Formula result = FIRST.join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE)).join(v).eq(toSend.expanded.join(FIRST.join(TRACE).join(TRACE)).join(v)).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = v.in(toSend.expanded.join(t).join(v)).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_historically() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process))
				.historically();
		Variable t = Variable.unary("t0");
		Formula result = v.in(toSend.expanded.join(t).join(v)).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.transpose().reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_once() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).once();
		Variable t = Variable.unary("t0");
		Formula result = v.in(toSend.expanded.join(t).join(v)).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(TRACE.transpose().reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void simple_previous() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).previous();
		Formula result = FIRST.join(TRACE.transpose()).some().and(v.in(toSend.expanded.join(FIRST.join(TRACE.transpose())).join(v)).and(v.in(toSend.expanded.join(FIRST.join(TRACE.transpose())).join(v))).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_prime_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend)).always();
		Variable t = Variable.unary("t0");
		Formula result = (((v.join(toSend.expanded.join(t.join(TRACE))).eq(v.join(toSend.expanded.join(t))))).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());

	}

	@Test
	public final void simple_post_next_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend)).next().always();
		Variable t = Variable.unary("t0");
		Formula result = ((t.join(TRACE).join(TRACE).some().and((v.join(toSend.expanded.join(t.join(TRACE).join(TRACE))).eq(v.join(toSend.expanded.join(t.join(TRACE))))))).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());

	}

	@Test
	public final void simple_post_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = t.join(TRACE).some().and(v.join(toSend.expanded.join(t.join(TRACE))).eq(v.join(toSend.expanded.join(t)))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void simple_post_next_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend).prime().prime()).next().eventually();
		Variable t = Variable.unary("t0");
		Formula result = (t.join(TRACE).join(TRACE).join(TRACE).some().and(v.join(toSend.expanded.join(t.join(TRACE).join(TRACE))).eq(v.join(toSend.expanded.join(t.join(TRACE).join(TRACE).join(TRACE)))))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void simple_post_next() {
		Formula initial = toSend.prime().eq(toSend).next();
		Formula result = FIRST.join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE).join(TRACE)).eq(toSend.expanded.join(FIRST.join(TRACE))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_until() {
		Formula initial = Process.join(toSend).some().until(Process.join(toSend).lone());
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f2 = Process.join(toSend.expanded.join(t1)).some().forAll(t1.oneOf(upTo(FIRST,t,true,false)));
		Formula f1 = Process.join(toSend.expanded.join(t)).lone().and(f2).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula result = f1;
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_since() {
		Formula initial = Process.join(toSend).some().since(Process.join(toSend).lone());
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f2 = Process.join(toSend.expanded.join(t1)).some().forAll(t1.oneOf(upTo(t,FIRST,false,true)));
		Formula f1 = Process.join(toSend.expanded.join(t)).lone().and(f2).forSome(t.oneOf(FIRST.join(TRACE.transpose().reflexiveClosure())));
		Formula result = f1;
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	private Expression upTo(Expression t1, Expression t2, boolean inc1, boolean inc2) {
		Formula c = t2.in(t1.join(PREFIX.reflexiveClosure()));
		Expression exp1 = inc1?PREFIX.reflexiveClosure():PREFIX.closure();
		Expression exp2 = inc2?PREFIX.reflexiveClosure():PREFIX.closure();
		Expression exp11 = inc1?TRACE.reflexiveClosure():TRACE.closure();
		Expression exp12 = inc2?TRACE.reflexiveClosure():TRACE.closure();
		Expression e1 = (t1.join(exp1)).intersection(t2.join(exp2.transpose()));
		Expression e21 = (t1.join(exp11)).intersection(t2.join(exp12.transpose()));
		Expression e22 = (t2.join(exp1)).intersection(t1.join(exp2.transpose()));
		Expression e2 = e21.difference(e22);
		return c.thenElse(e1, e2);
	}

	@Test
	public final void simple_release() {
		Formula initial = Process.join(toSend).some().release(Process.join(toSend).lone());
		Variable t = Variable.unary("t1");
		Variable t1 = Variable.unary("t2");
		Variable t2 = Variable.unary("t0");
		Formula f2 = Process.join(toSend.expanded.join(t1)).lone().forAll(t1.oneOf(upTo(FIRST,t,true,true)));
		Formula f1 = Process.join(toSend.expanded.join(t)).some().and(f2).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula f3 = Process.join(toSend.expanded.join(t2)).lone().forAll(t2.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula result = ((f3)).or(f1);
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_release_post() {
		Variable v = Variable.unary("p");
		Formula initial = toSend.join(v).eq(toSend.join(v)).release(Process.join(toSend.prime()).lone()).forAll(v.oneOf(Process));
		Variable t = Variable.unary("t1");
		Variable t1 = Variable.unary("t2");
		Variable t2 = Variable.unary("t0");
		Formula f2 = t1.join(TRACE).some().and(Process.join(toSend.expanded.join(t1.join(TRACE))).lone()).forAll(t1.oneOf(upTo(FIRST,t,true,true)));
		Formula f1 = toSend.expanded.join(t).join(v).eq(toSend.expanded.join(t).join(v)).and(f2).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula f3 = Process.join(toSend.expanded.join(t2.join(TRACE))).lone().forAll(t2.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula result = ((f3)).or(f1).forAll(v.oneOf(Process));

		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	/* Out of the root */
	@Test
	public final void simple_always_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).always().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = (((v.in(toSend.expanded.join(t1).join(v))).forAll(t1.oneOf(t.join(TRACE.reflexiveClosure())))).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_always_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).always().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = ((v.in(toSend.expanded.join(t1).join(v))).forAll(t1.oneOf(t.join(TRACE.reflexiveClosure())))).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_once_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).once().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = ((v.in(toSend.expanded.join(t1).join(v))).forSome(t1.oneOf(t.join(TRACE.transpose().reflexiveClosure()))).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_historically_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).historically().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = (v.in(toSend.expanded.join(t1).join(v))).forAll(t1.oneOf(t.join(TRACE.transpose().reflexiveClosure()))).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_next_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).next().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Formula result = ((t.join(TRACE).some().and(v.in(toSend.expanded.join(t.join(TRACE)).join(v)))).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_previous_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).previous().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Formula result = ((t.join(TRACE.transpose()).some().and(v.in(toSend.expanded.join(t.join(TRACE.transpose())).join(v)))).and(v.in(toSend.expanded.join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_previous_always_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).previous().and(v.in(toSend.join(v)).always().and(v.in(toSend.join(v)))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f1 = t.join(TRACE.transpose()).some().and(v.in(toSend.expanded.join(t.join(TRACE.transpose())).join(v)));
		Formula f2 = ((v.in(toSend.expanded.join(t1).join(v))).forAll(t1.oneOf(t.join(TRACE.reflexiveClosure()))));
		Formula result = ((f1.and(f2.and(v.in(toSend.expanded.join(t).join(v))))).forAll(v.oneOf(Process))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_next_eventually_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).next().and(v.in(toSend.join(v)).eventually().and(v.in(toSend.join(v)))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f1 = t.join(TRACE).some().and(v.in(toSend.expanded.join(t.join(TRACE)).join(v)));
		Formula f2 = (v.in(toSend.expanded.join(t1).join(v))).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = ((f1.and(f2.and(v.in(toSend.expanded.join(t).join(v))))).forAll(v.oneOf(Process))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	
	@Test
	public final void simple_until_always() {
		Formula initial = Process.join(toSend).some().until(Process.join(toSend).lone()).always();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Variable t2 = Variable.unary("t2");
		Formula f2 = Process.join(toSend.expanded.join(t2)).some().forAll(t2.oneOf(upTo(t,t1,true,false)));
		Formula f1 = Process.join(toSend.expanded.join(t1)).lone().and(f2).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = (f1.forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_always_until_eventually() {
		Formula initial = Process.join(toSend).some().always().until(Process.join(toSend).lone()).eventually();

		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Variable t2 = Variable.unary("t2");
		Variable t3 = Variable.unary("t3");
		Formula f2 = ((Process.join(toSend.expanded.join(t3)).some().forAll(t3.oneOf(t2.join(TRACE.reflexiveClosure()))))).forAll(t2.oneOf(upTo(t,t1,true,false)));
		Formula f1 = Process.join(toSend.expanded.join(t1)).lone().and(f2).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = f1.forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void simple_release_always() {
		Formula initial = Process.join(toSend).some().release(Process.join(toSend).lone()).always();
		Variable t = Variable.unary("t2");
		Variable t1 = Variable.unary("t3");
		Variable t2 = Variable.unary("t1");
		Variable t3 = Variable.unary("t0");
		Formula f2 = Process.join(toSend.expanded.join(t1)).lone().forAll(t1.oneOf(upTo(t3,t,true,true)));
		Formula f1 = Process.join(toSend.expanded.join(t)).some().and(f2).forSome(t.oneOf(t3.join(TRACE.reflexiveClosure())));
		Formula f3 = Process.join(toSend.expanded.join(t2)).lone().forAll(t2.oneOf(t3.join(TRACE.reflexiveClosure())));
		Formula result = (((f3)).or(f1).forAll(t3.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());	}

	@Test
	public final void simple_until1_always() {
		Formula initial = Process.join(toSend).some().until(Process.join(toSend).prime().lone()).always().and(toSend.one());
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Variable t2 = Variable.unary("t2");
		Formula f2 = Process.join(toSend.expanded.join(t2)).some().forAll(t2.oneOf(upTo(t,t1,true,false)));
		Formula f1 = (t1.join(TRACE).some().and(Process.join(toSend.expanded.join(t1.join(TRACE))).lone()).and(f2)).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = (f1.forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure())))).and(toSend.expanded.join(FIRST).one());
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());	
	}

	/* Prime, next and previous */
	@Test
	public final void nested_primes() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = t.join(TRACE).join(TRACE).some().and(((toSend.expanded.join(t.join(TRACE)).join(toSend.expanded.join(t.join(TRACE).join(TRACE)))).in(toSend.expanded.join(t)))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void nested_primes2() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).and(toSend.prime().prime().prime().in(toSend)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = t.join(TRACE).join(TRACE).join(TRACE).some().and((toSend.expanded.join(t.join(TRACE)).join(toSend.expanded.join(t.join(TRACE).join(TRACE))).in(toSend.expanded.join(t))).and(toSend.expanded.join(t.join(TRACE).join(TRACE).join(TRACE)).in(toSend.expanded.join(t)))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}

	@Test
	public final void nested_primes3() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).and(toSend.prime().prime().prime().in(toSend));
		Formula result = FIRST.join(TRACE).join(TRACE).join(TRACE).some().and((toSend.expanded.join(FIRST.join(TRACE)).join(toSend.expanded.join(FIRST.join(TRACE).join(TRACE))).in(toSend.expanded.join(FIRST))).and(toSend.expanded.join(FIRST.join(TRACE).join(TRACE).join(TRACE)).in(toSend.expanded.join(FIRST))));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void nested_next() {
		Formula initial = (toSend.in(toSend).next().next()).and(toSend.in(toSend).next()).next();
		Formula f1 = FIRST.join(TRACE).join(TRACE).some().and(FIRST.join(TRACE).join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE).join(TRACE).join(TRACE)).in(toSend.expanded.join(FIRST.join(TRACE).join(TRACE).join(TRACE)))));
		Formula f2 = FIRST.join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE).join(TRACE)).in(toSend.expanded.join(FIRST.join(TRACE).join(TRACE))));
		Formula result = FIRST.join(TRACE).some().and(f1.and(f2));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void nested_next_prime() {
		Formula initial = (toSend.in(toSend).next().next()).and(toSend.in(toSend.prime()).next()).next();
		Formula f1 = FIRST.join(TRACE).join(TRACE).some().and(FIRST.join(TRACE).join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE).join(TRACE).join(TRACE)).in(toSend.expanded.join(FIRST.join(TRACE).join(TRACE).join(TRACE)))));
		Formula f2 = FIRST.join(TRACE).join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE).join(TRACE)).in(toSend.expanded.join(FIRST.join(TRACE).join(TRACE).join(TRACE))));
		Formula result = FIRST.join(TRACE).some().and(f1.and(f2));
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void nested_previous() {
		Formula initial = (toSend.in(toSend).previous().previous()).and(toSend.in(toSend).previous()).previous();
		Formula f1 = FIRST.join(TRACE.transpose()).join(TRACE.transpose()).some().and(FIRST.join(TRACE.transpose()).join(TRACE.transpose()).join(TRACE.transpose()).some().and(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE.transpose()).join(TRACE.transpose())).in(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE.transpose()).join(TRACE.transpose())))));
		Formula f2 = FIRST.join(TRACE.transpose()).join(TRACE.transpose()).some().and(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE.transpose())).in(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE.transpose()))));
		Formula result = FIRST.join(TRACE.transpose()).some().and(f1.and(f2));		
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void nested_previous_next() {
		Formula initial = (toSend.in(toSend)).next().previous();
		Formula f1 = FIRST.join(TRACE.transpose()).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE)).in(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE))));
		Formula result = FIRST.join(TRACE.transpose()).some().and(f1);		
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void nested_previous_prime() {
		Formula initial = (toSend.in(toSend.prime())).previous();
		Formula f1 = FIRST.join(TRACE.transpose()).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE.transpose())).in(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE))));
		Formula result = FIRST.join(TRACE.transpose()).some().and(f1);		
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
	
	@Test
	public final void nested_previous_next_prime() {
		Formula initial = ((toSend.prime().prime().in(toSend.prime()).next()).and((toSend.prime().prime().in(toSend.prime()).previous()))).previous();
		Formula f1 = FIRST.join(TRACE.transpose()).join(TRACE).join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE).join(TRACE).join(TRACE)).in(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE).join(TRACE))));
		Formula f2 = FIRST.join(TRACE.transpose()).join(TRACE.transpose()).some().and(FIRST.join(TRACE.transpose()).join(TRACE.transpose()).join(TRACE).join(TRACE).some().and(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE.transpose()).join(TRACE).join(TRACE)).in(toSend.expanded.join(FIRST.join(TRACE.transpose()).join(TRACE.transpose()).join(TRACE)))));
		Formula result = FIRST.join(TRACE.transpose()).some().and(f1.and(f2));		
		assertEquals(result.toString(), ((NaryFormula)LTL2FOLTranslator.translate(initial,false)).child(0).toString());
	}
}
