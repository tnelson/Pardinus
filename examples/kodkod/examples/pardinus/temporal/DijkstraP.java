package kodkod.examples.pardinus.temporal;


import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.ast.Variable;
import kodkod.engine.decomp.DModel;
import kodkod.engine.ltl2fol.TemporalFormulaExtension;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

import java.util.ArrayList;
import java.util.List;


public class DijkstraP implements DModel {
    private final Relation Process, Mutex;
    private final Relation  mfirst, mlast, mord;

    private final VarRelation holds, waits;


    private int processes, mutexes;
    private Variant var;

    public enum Variant {
        SAT,
        UNSAT;
    }

    private  TemporalFormulaExtension temporalFormula;

    /**
     * Creates an instance of Dijkstra example.
     */
    public DijkstraP(String[] args) {
        Process = Relation.unary("Process");
        Mutex = Relation.unary("Mutex");
        mfirst = Relation.unary("mfirst");
        mlast = Relation.unary("mlast");
        mord = Relation.binary("mord");

        holds = VarRelation.binary("holds");
        waits = VarRelation.binary("waits");

        this.processes = Integer.valueOf(args[0]);
        this.mutexes = Integer.valueOf(args[1]);
        int times  = Integer.valueOf(args[2]);
        this.var = Variant.valueOf(args[3]);



        Formula formula = finalFormula();
        Bounds var6 = bounds();
        temporalFormula = new TemporalFormulaExtension(formula, var6,times);

    }

    public Bounds bounds1(){
        return this.temporalFormula.getStaticBounds();
    }

    public Bounds bounds2(){
        return this.temporalFormula.getDynamicBounds();
    }

    public Formula partition1() {
        return this.temporalFormula.getStaticFormula();
    }

    public Formula partition2(){
        return this.temporalFormula.getDynamicFormula();

    }

    public int getBitwidth() {
        return 1;
    }





    /**
     * Returns the declaration constraints.
     * @return
     * <pre>
     * sig Process {}
     * sig Mutex {}
     * sig State { holds, waits: Process -> Mutex }
     * </pre>
     */
    public Formula declarations() {
        final Formula f3 = holds.in(Process.product(Mutex)).always();/*TEMPORAL OP*/
        final Formula f4 = waits.in(Process.product(Mutex)).always();/*TEMPORAL OP*/

        final Formula f5 = mord.totalOrder(Mutex, mfirst, mlast);
        final Formula f6 = Process.eq(Process);

        return Formula.and(f3, f4,f5,f6);
    }



    /**
     * Returns the initial predicate for state s.
     * @return
     * <pre>
     * pred State.Initial () { no this.holds + this.waits }
     * </pre>
     */
    public Formula initial() {
        return holds.union(waits).no();
    }

    /**
     * Returns the free predicate for state s and mutex m.
     * @return
     * <pre>
     * pred State.IsFree (m: Mutex) {
     * // no process holds this mutex
     * no m.~(this.holds)
     * }
     * </pre>
     */
    public Formula isFree(Expression m) {
        return m.join(holds).no();
    }



    /**
     * Returns the isStalled predicate for state s and process p.
     * @return
     * <pre>
     * pred State.IsStalled (p: Process) { some p.(this.waits) }
     * </pre>
     */
    public Formula isStalled(Expression p) {
        return p.join(waits).some();
    }



    /**
     * Returns the GrabMutex predicate for states s1, s2, process p and mutex m.
     * @return
     * <pre>
     * pred State.GrabMutex (p: Process, m: Mutex, s': State) {
     *  // a process can only act if it is not
     *  // waiting for a mutex
     * !this::IsStalled(p)
     * // can only grab a mutex we do not yet hold
     * 	m !in p.(this.holds)
     * this::IsFree (m) => {
     *    // if the mutex is free, we now hold it,
     *    // and do not become stalled
     *    p.(s'.holds) = p.(this.holds) + m
     *    no p.(s'.waits)
     *  } else {
     *   // if the mutex was not free,
     *   // we still hold the same mutexes we held,
     *   // and are now waiting on the mutex
     *   // that we tried to grab.
     *   p.(s'.holds) = p.(this.holds)
     *   p.(s'.waits) = m
     * }
     * all otherProc: Process - p | {
     *    otherProc.(s'.holds) = otherProc.(this.holds)
     *    otherProc.(s'.waits) = otherProc.(this.waits)
     * }
     * }
     * </pre>
     */
    public Formula grabMutex(/*Expression s1, Expression s2,*/ Expression p, Expression m) {
        final Formula f1 = isStalled(p).not().and(m.in(p.join(holds)).not());
        final Formula isFree = isFree(m);
        final Formula f2 = p.join(holds.post()).eq(p.join(holds).union(m));/*TEMPORAL OP*/
        final Formula f3 = p.join(waits.post()).no();/*TEMPORAL OP*/
        final Formula f4 = isFree.implies(f2.and(f3));
        final Formula f5 = p.join(holds.post()).eq(p.join(holds));/*TEMPORAL OP*/
        final Formula f6 = p.join(waits.post()).eq(m);/*TEMPORAL OP*/
        final Formula f7 = isFree.not().implies(f5.and(f6));
        final Variable otherProc = Variable.unary("otherProc");
        final Formula f8 = otherProc.join(holds.post()).eq(otherProc.join(holds));/*TEMPORAL OP*/
        final Formula f9 = otherProc.join(waits.post()).eq(otherProc.join(waits));/*TEMPORAL OP*/
        final Formula f10 = f8.and(f9).forAll(otherProc.oneOf(Process.difference(p)));
        return Formula.and(f1, f4, f7, f10);
    }



    /**
     * Returns the GrabMutex predicate for states s1, s2, process p and mutex m.
     * @return
     * <pre>
     * pred State.ReleaseMutex (p: Process, m: Mutex, s': State) {
     *   !this::IsStalled(p)
     *   m in p.(this.holds)
     *   p.(s'.holds) = p.(this.holds) - m
     *   no p.(s'.waits)
     *   no m.~(this.waits) => {
     *       no m.~(s'.holds)
     *       no m.~(s'.waits)
     *    } else {
     *       some lucky: m.~(this.waits) | {
     *       m.~(s'.waits) = m.~(this.waits) - lucky
     *     m.~(s'.holds) = lucky
     *    }
     *   }
     *   all mu: Mutex - m {
     *     mu.~(s'.waits) = mu.~(this.waits)
     *     mu.~(s'.holds)= mu.~(this.holds)
     *   }
     * }
     * </pre>
     */
    public Formula releaseMutex(Expression p, Expression m) {
        final Formula f1 = isStalled(p).not().and(m.in(p.join(holds)));
        final Formula f2 = p.join(holds.post()).eq(p.join(holds).difference(m));/*TEMPORAL OP*/
        final Formula f3 = p.join(waits.post()).no();/*TEMPORAL OP*/
        final Expression cexpr = m.join((waits).transpose());
        final Formula f4 = m.join(holds.post().transpose()).no();/*TEMPORAL OP*/
        final Formula f5 = m.join(waits.post().transpose()).no();/*TEMPORAL OP*/
        final Formula f6 = cexpr.no().implies(f4.and(f5));
        final Variable lucky = Variable.unary("lucky");
        final Formula f7 = m.join(waits.post().transpose()).eq(m.join(waits.transpose()).difference(lucky));/*TEMPORAL OP*/
        final Formula f8 = m.join(holds.post().transpose()).eq(lucky);/*TEMPORAL OP*/
        final Formula f9 = f7.and(f8).forSome(lucky.oneOf(m.join(waits.transpose())));
        final Formula f10 = cexpr.some().implies(f9);
        final Variable mu = Variable.unary("mu");
        final Formula f11 = mu.join(waits.post().transpose()).eq(mu.join(waits.transpose()));/*TEMPORAL OP*/
        final Formula f12 = mu.join(holds.post().transpose()).eq(mu.join(holds.transpose()));/*TEMPORAL OP*/
        final Formula f13 = f11.and(f12).forAll(mu.oneOf(Mutex.difference(m)));
        return Formula.and(f1, f2, f3, f6, f10, f13);
    }



    /**
     * Returns the GrabOrRelease predicate.
     * @return
     * <pre>
     * pred GrabOrRelease () {
     *    Initial(so/first()) &&
     *    (
     *    all pre: State - so/last () | let post = so/next (pre) |
     *       (post.holds = pre.holds && post.waits = pre.waits)
     *        ||
     *       (some p: Process, m: Mutex | pre::GrabMutex (p, m, post))
     *        ||
     *       (some p: Process, m: Mutex | pre::ReleaseMutex (p, m, post))
     *
     *    )
     * }
     * </pre>
     */
    public Formula grabOrRelease() {
        final Variable pre = Variable.unary("pre");
        final Formula f1 = holds.post().eq(holds);/*TEMPORAL OP*/
        final Formula f2 = waits.post().eq(waits);/*TEMPORAL OP*/
        final Variable p = Variable.unary("p");
        final Variable m = Variable.unary("m");
        final Decls d = p.oneOf(Process).and(m.oneOf(Mutex));
        final Formula f3 = grabMutex(p, m).forSome(d);
        final Formula f4 = releaseMutex(p, m).forSome(d);
        return initial().and(((f1.and(f2)).or(f3).or(f4)).always());/*TEMPORAL OP*/
    }


    /**
     * Returns the Deadlock predicate.
     * @return
     * <pre>
     * pred Deadlock () {
     *  some s: State | all p: Process | some p.(s.waits)
     * }
     * </pre>
     */
    public Formula deadlock() {
        final Variable p = Variable.unary("p");
        return p.join(waits).some().forAll(p.oneOf(Process)).eventually();/*TEMPORAL OP*/
    }


    /**
     * Returns the GrabbedInOrder predicate.
     * @return
     * <pre>
     * pred GrabbedInOrder ( ) {
     * all pre: State - so/last() |
     *  let post = so/next(pre) |
     *     let had = Process.(pre.holds), have = Process.(post.holds) |
     *     let grabbed = have - had |
     *        some grabbed => grabbed in mo/nexts(had)
     * }
     * </pre>
     */
    public Formula grabbedInOrder() {
        final Expression had = Process.join(holds);
        final Expression have = Process.join(holds.post());/*TEMPORAL OP*/
        final Expression grabbed = have.difference(had);
        return grabbed.some().implies(grabbed.in(had.join(mord.closure()))).always();/*TEMPORAL OP*/
    }


    /**
     * Returns the DijkstraPreventsDeadlocks assertion.
     * @return
     * <pre>
     * assert DijkstraPreventsDeadlocks {
     *  some Process && GrabOrRelease() && GrabbedInOrder() => ! Deadlock()
     * }
     * </pre>
     */
    public Formula checkDijkstraPreventsDeadlocks() {
        return Formula.and(declarations(), Process.some(), grabOrRelease(), grabbedInOrder(), deadlock());
    }



    /**
     * Returns the showDijkstra predicate.
     * @return he showDijkstra predicate
     */
    public Formula showDijkstra() {
        return declarations().and(grabOrRelease()).and(deadlock()).and(waits.some());
    }



    public Bounds bounds() {

        final List<String> atoms = new ArrayList<String>(processes + mutexes);
        for(int i = 0; i < processes; i++) {
            atoms.add("Process"+i);
        }
        for(int i = 0; i < mutexes; i++) {
            atoms.add("Mutex"+i);
        }


        Universe u = new Universe(atoms);
        final TupleFactory f = u.factory();
        final Bounds b = new Bounds(u);

        final TupleSet pb = f.range(f.tuple("Process0"), f.tuple("Process" + (processes - 1)));
        final TupleSet mb = f.range(f.tuple("Mutex0"), f.tuple("Mutex"+(mutexes-1)));

        b.bound(Process, pb);

        b.bound(holds, pb.product(mb));
        b.bound(waits, pb.product(mb));

        b.bound(Mutex, mb);
        b.bound(mfirst, mb);
        b.bound(mlast, mb);
        b.bound(mord, mb.product(mb));

        return b;
    }




    public Formula finalFormula() {
        if (var == Variant.SAT) return showDijkstra();
        else return checkDijkstraPreventsDeadlocks();
    }

	@Override
	public String shortName() {
		// TODO Auto-generated method stub
		return null;
	}



}
