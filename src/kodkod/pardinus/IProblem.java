package kodkod.pardinus;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;

public class IProblem extends DSolution {

	final public List<Solution> config;

	public IProblem(List<Solution> cfg, DProblemManager manager) {
		super(manager, manager.formula2(), configBounds(manager, cfg));
		this.config = cfg;
	}
	
	/**
	 * Sets a configuration solution as exact bounds for the problem.
	 * @param b1
	 * @param b2
	 * @param s
	 * @return
	 */
	private static List<Bounds> configBounds(DProblemManager manager, List<Solution> ss) {
		List<Bounds> res = new ArrayList<Bounds>();
		
		for (Solution s : ss) {
		Bounds b3 = manager.bounds2().clone();

		for (Relation e : manager.bounds1().upperBounds().keySet()) {
			if (getTupleConfiguration(e.name(), s.instance()) != null) {
				b3.boundExactly(e, getTupleConfiguration(e.name(), s.instance()));
			}
		}

		for (Integer i : s.instance().ints().toArray())
			b3.boundExactly(i, b3.universe().factory().setOf(i));

		res.add(b3);
		}
		return res;
	}

	private static TupleSet getTupleConfiguration(String name, Instance s) {
		for (Relation r : s.relationTuples().keySet()) {
			if (r.name().equals(name)) {
				return s.relationTuples().get(r);
			}
		}
		return null;
	}
	
	/**
	 * Calculates the size of the configuration (number of tuples in the relations).
	 * @return
	 */
	private int configSize() {
		int c = 0;
		for (Solution s : config)
			for (TupleSet x : s.instance().relationTuples().values())
				c = c + x.size();
		return c;
	}
	
	public String toString() {
		if (config==null) return "M: POISON";
		if (getSolution()==null) return "M: UNSOLVED";
		return "M: "+ configSize() +  "\t" + getSolution().outcome() + "\t" + getSolveTime();
	}
	
}