/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2014-present, Nuno Macedo
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.examples.pardinus.temporal;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.decomp.DModel;
import kodkod.engine.ltl2fol.TemporalFormulaSlicer;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Eduardo Pessoa, nmm (pt.uminho.haslab)
 */
public class HotelP implements DModel {

	private int n;
	final private Variant variant;

	private final Relation key, key_first, key_last, key_next;
	private final Relation room, guest, rkeys;
	private final VarRelation current, lastkey, occupant, gkeys;

	public enum Variant {
		INTERVENES, NOINTERVENES;
	}

	private TemporalFormulaSlicer slicer;

	public HotelP(String[] args) {
		this.n = Integer.valueOf(args[0]);
		this.variant = Variant.valueOf(args[1]);

		key = Relation.unary("Key");
		guest = Relation.unary("Guest");
		room = Relation.unary("Room");
		rkeys = Relation.nary("Room.keys", 2);
		key_first = Relation.unary("ordering/Ord.First");
		key_last = Relation.unary("ordering/Ord.Last");
		key_next = Relation.nary("ordering/Ord.Next", 2);

		current = VarRelation.nary("Room.currentKey", 2);
		lastkey = VarRelation.nary("FrontDesk.lastKey", 2);
		occupant = VarRelation.nary("FrontDesk.occupant", 2);
		gkeys = VarRelation.nary("Guest.gkeys", 2);

		slicer = new TemporalFormulaSlicer(finalFormula(), bounds());
	}

	public Formula finalFormula() {
		Formula f2 = Formula.compose(FormulaOperator.AND, declsAndFacts(), init(), next(), noBadEntries().not());
		if (variant == Variant.NOINTERVENES)
			f2 = f2.and(noIntervenes());
		return f2;
	}

	private Formula init() {
		Variable r = Variable.unary("r");
		Formula x158 = r.join(lastkey).eq(r.join(current));
		Formula x111 = x158.forAll(r.oneOf(room)); // all r : Room |
													// r.lastkey.init =
													// r.current.init

		Formula x149 = (guest.join(gkeys)).no(); // no Guest.gkeys.init
		Formula x152 = (occupant).no(); // no occupant.init

		return x111.and(x149).and(x152);
	}

	public Formula staticDecls() {
		Formula x13 = rkeys.in(room.product(key)); // rkeys in Room -> Key
		Formula x28 = key_next.totalOrder(key, key_first, key_last);
		return Formula.compose(FormulaOperator.AND, x13, x28);
	}

	public Formula staticFact() {
		Variable v2 = Variable.unary("v5");
		Formula x41 = ((rkeys.join(v2)).one()).forAll(v2.oneOf(key)); // all k :
																		// Key |
																		// one
																		// rkeys.k
		Variable v3 = Variable.unary("v5");
		Formula x42 = ((v3.join(rkeys)).some()).forAll(v3.oneOf(room)); // all r
																		// :
																		// Room
																		// |
																		// some
																		// r.rkeys
		Formula x99 = guest.eq(guest);
		return Formula.compose(FormulaOperator.AND, x41, x99, x42);
	}

	public Formula tempDecls() {
		Formula x22 = lastkey.in(room.product(key)).always();/* TEMPORAL OP */// lastkey
																				// in
																				// Room
																				// ->
																				// Key
																				// ->
																				// Time
		Formula x27 = occupant.in(room.product(guest)).always();/* TEMPORAL OP */// occupant
																					// in
																					// Room
																					// ->
																					// Guest
																					// ->
																					// Time
		Formula x60 = gkeys.in(guest.product(key)).always();/* TEMPORAL OP */// gkeys
																				// in
																				// Guest
																				// ->
																				// Key
																				// ->
																				// Time
		Formula x86 = current.in(room.product(key)).always();/* TEMPORAL OP */// current
																				// in
																				// Room
																				// ->
																				// Key
																				// ->
																				// Time
		return Formula.compose(FormulaOperator.AND, x22, x27, x60, x86);
	}

	public Formula tempFacts() {
		Variable r = Variable.unary("r");
		Formula rt1 = (r.join(lastkey)).lone(); // all t : Time, r : Room | lone
												// r.lastkey.t
		Formula rt2 = (r.join(current)).one(); // all t : Time, r : Room | one
												// r.current.t
		Formula rt3 = (r.join(current)).in(r.join(rkeys)); // all t : Time, r :
															// Room |
															// r.current.t in
															// r.keys
		return (rt1.and(rt2).and(rt3)).forAll(r.oneOf(room)).always();/*
																	 * TEMPORAL
																	 * OP
																	 */
	}

	public Formula declsAndFacts() {
		return Formula.compose(FormulaOperator.AND, staticDecls(), staticFact(), tempDecls(), tempFacts());
	}

	private Formula next() {
		Variable g = Variable.unary("g");
		Variable r = Variable.unary("r");
		Variable k = Variable.unary("k");

		Formula x189 = entry(r, k, g).or(checkout(g)).or(checkin(r, k, g));
		Formula x181 = x189.forSome((g.oneOf(guest)).and(r.oneOf(room)).and(k.oneOf(key)));
		return x181.always();
	}

	private Formula noIntervenes() {
		Variable g = Variable.unary("g");
		Variable r = Variable.unary("r");
		Variable k = Variable.unary("k");

		Formula checkin = checkin(r, k, g);
		Formula entry = entry(r, k, g);

		Formula x394 = checkin.implies(entry.next());/* TEMPORAL OP */

		return x394.forAll(g.oneOf(guest).and(r.oneOf(room)).and(k.oneOf(key))).always();/*
																						 * TEMPORAL
																						 * OP
																						 */
	}

	private Formula noBadEntries() {
		Variable r = Variable.unary("r");
		Variable g = Variable.unary("g");
		Variable k = Variable.unary("k");

		Formula entry = entry(r, k, g);
		Formula x653 = r.join(occupant).some(); // some r.occupant.t
		Formula x624 = (g.in(r.join(occupant))); // g in r.occupant.t
		Formula x574 = (entry.and(x653)).implies(x624);
		Formula x566 = x574.forAll((r.oneOf(room)).and(g.oneOf(guest)).and(k.oneOf(key))).always();/*
																									 * TEMPORAL
																									 * OP
																									 */

		return x566;
	}

	private Formula entry(Variable r, Variable k, Variable g) {
		Formula x583 = k.eq(r.join(current)); // k = r.current.t

		Expression x595 = ((r.join(current)).join(key_next.closure())).intersection(r.join(rkeys)); // (r.current.t).next+
																									// &
																									// r.keys
		Formula x593 = k.eq(x595.difference(x595.join(key_next.closure()))); // k
																				// =
																				// (r.current.t).next+
																				// &
																				// r.keys
																				// -
																				// ((r.current.t).next+
																				// &
																				// r.keys).next+
		Formula x581 = x583.or(x593);

		Formula x576 = k.in(g.join(gkeys)); // k in g.keys.t
		Formula x609 = (r.join(current.post())).eq(k);/* TEMPORAL OP */// r.current.t'
																		// = k

		Variable r1 = Variable.unary("r'");
		Formula x641 = (r1.join(current)).eq(r1.join(current.post()));/*
																	 * TEMPORAL
																	 * OP
																	 */
		Formula x637 = x641.forAll(r1.oneOf(room.difference(r))); // all x :
																	// Room - r
																	// |
																	// x.current.t
																	// =
																	// x.current.t'

		Formula x614 = gkeys.eq(gkeys.post());/* TEMPORAL OP */// gkeys.t =
																// gkeys.t'
		Formula x629 = (lastkey).eq(lastkey.post());/* TEMPORAL OP */// lastley.t
																		// =
																		// lastkey.t'
		Formula x647 = (occupant).eq(occupant.post()); /* TEMPORAL OP */// occupant.t
																			// =
																			// occupant.t'
		Formula entry = Formula.compose(FormulaOperator.AND, x576, x581, x614, x629, x637, x647, x609);
		return entry;
	}

	private Formula checkin(Variable r, Variable k, Variable g) {
		Formula x398 = g.join(gkeys.post()).eq((g.join(gkeys)).union(k)); // g.keys.t'
																			// =
																			// g.keys.t
																			// +
																			// k
		Formula x407 = (r.join(occupant)).no(); // no r.occupant.t
		Formula x411 = (lastkey.post()).eq((lastkey).override(r.product(k))); // lastkey.t'
																				// =
																				// lastkey.t
																				// ++
																				// r
																				// ->
																				// k
		Expression x428 = (((r.join(lastkey)).join(key_next.closure())).intersection(r.join(rkeys))).join(key_next
				.closure());
		Expression x420 = (((r.join(lastkey)).join(key_next.closure())).intersection(r.join(rkeys))).difference(x428);
		Formula x419 = k.eq(x420); // k = (r.lastkey.t.next+ & r.keys) -
									// (r.lastkey.t.next+ & r.keys).next+
		Formula x439 = (occupant.post()).eq((occupant).union(r.product(g))); // occupant.t'
																				// =
																				// occupant.t
																				// +
																				// r
																				// ->
																				// g
		Formula x447 = (current).eq(current.post()); // current.t = current.t'
		Variable g1 = Variable.unary("g1");
		Formula x461 = (g1.join(gkeys)).eq(g1.join(gkeys.post()));
		Formula x457 = x461.forAll(g1.oneOf(guest.difference(g))); // all g1 :
																	// Guest - g
																	// |
																	// g.keys.t
																	// =
																	// g.keys.t'
		Formula checkin = Formula.compose(FormulaOperator.AND, x398, x407, x411, x419, x439, x447, x457);
		return checkin;
	}

	private Formula checkout(Variable g) {
		Formula x337 = ((occupant).join(g)).some(); // some (occupant.t).g
		Formula x343 = occupant.post().eq((occupant).difference(room.product(g))); // occupant.t'
																					// =
																					// occupant.t
																					// -
																					// room
																					// ->
																					// g
		Formula x351 = (current).eq(current.post()); // current.t = current.t'
		Formula x352 = (gkeys).eq(gkeys.post()); // lastkey.t = lastkey.t'
		Formula x353 = (lastkey).eq(lastkey.post()); // gkeys.t = gkeys.t'
		Formula checkout = x337.and(x343.and(x351)).and(x352).and(x353);
		return checkout;
	}

	public Bounds bounds() {
		final List<String> atoms = new ArrayList<String>(3 * n);
		for (int i = 0; i < n; i++) {
			atoms.add("Key" + i);
		}
		for (int i = 0; i < n; i++) {
			atoms.add("Room" + i);
		}
		for (int i = 0; i < n; i++) {
			atoms.add("Guest" + i);
		}

		Universe u = new Universe(atoms);

		final TupleFactory f = u.factory();
		final Bounds b = new Bounds(u);

		final TupleSet kb = f.range(f.tuple("Key0"), f.tuple("Key" + (n - 1)));
		final TupleSet gb = f.range(f.tuple("Guest0"), f.tuple("Guest" + (n - 1)));
		final TupleSet rb = f.range(f.tuple("Room0"), f.tuple("Room" + (n - 1)));

		b.boundExactly(key, kb);
		b.bound(key_first, kb);
		b.bound(key_last, kb);
		b.bound(key_next, kb.product(kb));
		b.bound(guest, gb);
		b.bound(room, rb);
		b.bound(rkeys, rb.product(kb));

		b.bound(lastkey, rb.product(kb));
		b.bound(occupant, rb.product(gb));
		b.bound(current, rb.product(kb));
		b.bound(gkeys, gb.product(kb));
		return b;
	}

	@Override
	public Bounds bounds1() {
		return slicer.getStaticBounds();
	}

	@Override
	public Bounds bounds2() {
		return slicer.getDynamicBounds();
	}

	@Override
	public Formula partition1() {
		return Formula.and(slicer.getStaticFormulas());
	}

	@Override
	public Formula partition2() {
		return Formula.and(slicer.getDynamicFormulas());
	}

	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getBitwidth() {
		return 1;
	}

	public static void main(String[] args) {
		HotelP model = new HotelP(new String[] { "3", "NOINTERVENES" });

		ExtendedOptions opt = new ExtendedOptions();
		opt.setSolver(SATFactory.Glucose);
		opt.setMaxTraceLength(10);
		Solver solver = new Solver(opt);

		Solution sol = solver.solve(model.finalFormula(), model.bounds());

		System.out.println(sol);
		return;
	}
}
