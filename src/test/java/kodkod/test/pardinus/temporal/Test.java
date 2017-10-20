package kodkod.test.pardinus.temporal;

import kodkod.ast.*;
import kodkod.engine.TemporalPardinusSolver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by macbookpro on 19/04/16.
 */
public class Test {
	private Relation Process = Relation.unary("Process");

	private Relation succ = Relation.binary("succ");
	private Relation pfirst = Relation.unary("pfirst");
	private Relation plast = Relation.unary("plast");
	private Relation pord = Relation.binary("pord");

	private VarRelation toSend = VarRelation.binary("toSend");
	private VarRelation elected = VarRelation.unary("elected");

	public static void main(String[] args) {
		new Test();
	}

	public Test() {
		Formula formula = finalFormula();
		PardinusBounds bounds = bounds(3);
		ExtendedOptions options = new ExtendedOptions();
		options.setMaxTraceLength(5);
		TemporalPardinusSolver solver = new TemporalPardinusSolver(options);
		solver.solve(formula, bounds);
	}

	public Formula declarations() {
		final Formula ordProcess = pord.totalOrder(Process, pfirst, plast);
		final Formula succFunction = succ.function(Process, Process);

		final Formula electedDomRange = elected.in(Process);
		final Formula sendDomRange = toSend.in(Process.product(Process));

		return Formula.and(ordProcess, succFunction, electedDomRange, sendDomRange);
	}

	// fact Ring {all p: Process | Process in p.^succ}
	public Formula factRing() {
		final Variable p = Variable.unary("p");
		return Process.in(p.join(succ.closure())).forAll(p.oneOf(Process));
	}

	// ---------------
	public Formula init() {
		final Variable p = Variable.unary("p");
		return p.join(toSend).eq(p).forAll(p.oneOf(Process));
	}

	public Formula skip(Expression p) {
		return p.join(toSend.prime()).eq(p.join(toSend));
	}

	public Formula step(Expression p) {
		final Expression from = p.join(toSend);
		final Expression to = p.join(succ).join(toSend);

		final Variable id = Variable.unary("id");
		final Expression prevs = (p.join(succ)).join((pord.transpose()).closure());
		final Formula f1 = p.join(toSend.prime()).eq(from.difference(id));
		final Formula f2 = p.join(succ).join(toSend.prime()).eq(to.union(id.difference(prevs)));
		return f1.and(f2).forSome(id.oneOf(from));
	}

	public Formula traces() {
		final Variable p = Variable.unary("p");
		final Formula f = step(p).or(step(succ.join(p))).or(skip(p));
		final Formula fAll = f.forAll(p.oneOf(Process)).always();
		return init().and(fAll);
	}

	// ---------------------------

	public Formula invariants() {
		return declarations().and(factRing()).and(traces());
	}

	public Formula GoodSafety() {
		Variable x = Variable.unary("x");
		Variable y = Variable.unary("y");
		return x.eq(y).forAll(y.oneOf(elected)).always().forAll(x.oneOf(elected)).always();
	}

	public Formula finalFormula() {
		return Formula.and(invariants(), GoodSafety());
	}

	public PardinusBounds bounds(int processes) {
		final List<String> atoms = new ArrayList<String>(processes);
		for (int i = 0; i < processes; i++) {
			atoms.add("Process" + i);
		}

		final Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);

		final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process" + (processes - 1)));

		b.bound(Process, pb);
		b.bound(succ, pb.product(pb));
		b.bound(toSend, pb.product(pb));
		b.bound(elected, pb);
		b.bound(pord, pb.product(pb));
		b.bound(pfirst, pb);
		b.bound(plast, pb);

		return b;
	}

	public static void p(String name) {
		System.out.println(name);
	}

}
