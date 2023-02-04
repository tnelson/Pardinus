/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
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
package kodkod.cli;

import java.text.NumberFormat;
import java.time.temporal.Temporal;
import java.util.*;
import java.util.logging.Logger;

import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.Statistics;
import kodkod.engine.ucore.HybridStrategy;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.Instance;
import kodkod.instance.TemporalInstance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleSet;

/**
 * An implementation of the  {@link KodkodOutput} interface that writes solutions provided to it
 * to standard output, in the form of s-expressions.  Given a satisfiable
 * solution {@code s}, an instance of this class  will produce output of the form {@code (sat :model ([ri {(int+)*}]*))},
 * where each {@code ri} is a relation in {@code s.instance}, and {@code {(int+)*}} is an
 * s-expression representation of the tupleset {@code s.instance.tuples(ri)}.
 * Each tupleset is represented as a list of tuples, and each tuple is represented
 * as a (space-separated) list of atom indices comprising that tuple.
 *
 * <p>
 * Given an unsatisfiable solution {@code s} to a problem {@code p}, this implementation will produce output of the
 * form {@code (unsat :core (fi+))}, if a core is available, or of the form {@code (unsat)}, otherwise.
 * Each {@code fi} is a formula identifier in {@code p.env.defs['f']} such that the formula
 * {@code p.env.defs['f'][fi]} is in {@code s.proof.highLevelCore().values()}.  If there are some formulas
 * that are in the core but are not defined in {@code p.env.defs['f']}, a warning message will be printed to
 * a specified {@link Logger logger}.
 * </p>
 *
 * <p>
 * For both sat and unsat solutions, a {@link StandardKodkodOutput} instance
 * prints all statistics as info messages to its {@link Logger logger}.
 * The format of the info messages is unspecified.
 * </p>
 *
 * @specfield logger: {@link Logger}
 */
public final class StandardKodkodOutput implements KodkodOutput {
	private final Logger logger;

	/**
	 * Creates an instance of {@link StandardKodkodOutput}.
	 * @ensures this.logger' = logger
	 */
	StandardKodkodOutput(Logger logger) {  this.logger = logger; }

	/**
	 * Creates an instance of {@link StandardKodkodOutput} that will use the
	 * {@link Logger#getGlobal() global logger}.
	 * @ensures this.logger' = Logger.getGlobal()
	 */
	public StandardKodkodOutput() {  this(Logger.getGlobal()); }

    public void writeUnsat(Solution sol, KodkodProblem problem) {
		if(sol.proof() != null) {
			if("rce".equalsIgnoreCase(problem.coreMinimization))
				sol.proof().minimize(new RCEStrategy(sol.proof().log()));
			else if("hybrid".equalsIgnoreCase(problem.coreMinimization))
				sol.proof().minimize(new HybridStrategy(sol.proof().log()));
		}

        writeCore(sol, problem, (StringDefs<Formula>) problem.env().defs('f'));
    }

	/**
	 * {@inheritDoc}
	 * @see kodkod.cli.KodkodOutput#writeSolution(kodkod.engine.Solution, kodkod.cli.KodkodProblem)
	 */
	@SuppressWarnings("unchecked")
	public void writeSolution(Solution sol, KodkodProblem problem) {
		if (sol.sat()) 	{
			// var relations (x) and normal relations (r) are stored separately
			StringDefs<Relation> rdefns = (StringDefs<Relation>) problem.env().defs('r');
			StringDefs<Relation> xdefns = (StringDefs<Relation>) problem.env().defs('x');
			Set<String> origAtoms = problem.env().defs('a').keys();
			final StringBuilder str = new StringBuilder();
			str.append("(sat :model (");

			// Temporal problem will have a TemporalInstance to break down
			// But isTemporal stops being trustworthy
			//if(problem.isTemporal()) {
			if(sol.instance() instanceof TemporalInstance) {
				TemporalInstance tinst = (TemporalInstance) sol.instance();
				int prefixLength = tinst.prefixLength();
				int loopTo = tinst.loop;
				for(int i=0;i<prefixLength;i++) {
					Instance iinst = tinst.state(i);
					writeInstance(str, problem, iinst, rdefns, xdefns, origAtoms);
				}

			} else {
				writeInstance(str, problem, sol.instance(), rdefns, xdefns, origAtoms);
			}
			str.append(")"); // end of instance list
			writeStats(problem, sol, str);
			str.append(":metadata (");
			if(sol.instance() instanceof TemporalInstance) {
				str.append("(prefixLength " +
						((TemporalInstance)sol.instance()).prefixLength() +
						") (loop " +
						((TemporalInstance)sol.instance()).loop + ")");
			}
			str.append(")"); // end of metadata
			str.append(")"); // end of sat
			System.out.println(str);
		}
		else			System.out.println("(no-more-instances)");
	}



	/**
	 * Writes the instance s-expression to standard out.
	 * @requires all r: defs.def[int] | inst.tuples(r) != null
	 **/
	public void writeInstance(StringBuilder str, KodkodProblem problem, Instance inst, StringDefs<Relation> rdefs, StringDefs<Relation> xdefs, Set<String> origAtoms) {
		Set<Relation> written = new HashSet<>();
		str.append("("); // start model expression
		for (String name : rdefs.keys()) {
			final Relation r = rdefs.use(name);
			if (r==null) continue;
			final TupleSet ts = inst.tuples(r);
			assert ts != null;
			appendRelation(r, ts, str, origAtoms);
			written.add(r);
		}

		for (String name : xdefs.keys()) {
			final Relation r = xdefs.use(name);
			if (r==null) continue;
			// Don't index by relation here, because the relation r
			// is the pre-state-addition relation; use the name instead.
			final TupleSet ts = inst.tuples(r.name());
			assert ts != null;
			appendRelation(r, ts, str, origAtoms);
			written.add(r);
		}
		// Write out Skolem relations as well. Client will need to be ready for non-numeric label.
		for(Relation r : inst.relations()) {
			if(!written.contains(r) && r.name().startsWith("$")) {
				final TupleSet ts = inst.tuples(r);
				assert ts != null;
				appendRelation(r, ts, str, origAtoms);
				written.add(r);
			}
			// Also provide the state indices
			//   ^ Not anymore, now we're passing a sequence of instances back
			/*if(r.name().equals("Time")) {
				final TupleSet ts = inst.tuples(r);
				assert ts != null;
				appendRelation(r, ts, str, origAtoms);
				written.add(r);
			}*/
		}

		str.append(")"); // end of model
	}

	private void appendRelation(Relation r, TupleSet ts, StringBuilder str, Set<String> origAtoms) {
		str.append("[").append(r).append(" {");
		final int arity = ts.arity();
		// This code previously used t.atomIndex, rather than t.atom
		// Pardinus (temporal) will create new atoms at 0-based indexes
		//   which meant the previous approach was unsafe. Now send back
		//   new atom names instead of forcing caller to increment everything
		// If needed, origAtoms parameter can be used to identify new atoms
		for(Tuple t : ts) {
			str.append("(");
			str.append(t.atom(0));
			for(int idx = 1; idx < arity; idx++) {
				str.append(" ").append(t.atom(idx));
			}
			str.append(")");
		}
		str.append("}]");
	}

	/**
	 * Writes the core s-expression to standard out.
	 * @requires proof.highLevelCore().values() in defs.def[int]
	 **/
	public void writeCore(Solution sol,  KodkodProblem problem, StringDefs<Formula> defs) {
		final StringBuilder str = new StringBuilder();
		final Proof proof = sol.proof();
		str.append("(unsat");

        if (proof != null){
            str.append(" :core ( ");
            for (Node form : proof.highLevelCore().values()) {
                str.append("\"");
                if(form instanceof Formula && defs.canReverse((Formula)form)) {
					str.append("f:"+defs.reverse((Formula) form));
				} else {
                	// If core granularity is high, Kodkod may produce
					//  formulas that don't correspond to top-level constraints
					str.append(form);
				}
                str.append("\" ");
            }
            str.append(")");
        }

		writeStats(problem, sol, str);

		str.append(")");
        System.out.println(str.toString());
    }
    // ...
// }
		// final Set<Node> core;
		// if (proof == null) {
		// 	core = Collections.emptySet();
		// } else {
        //     core =
		// 	core = new LinkedHashSet<Node>(proof.highLevelCore().values());
		// 	str.append(" :core (");
		// 	for (int i = 0, max = defs.maxIndex(); i <= max; i++) {
		// 		if (core.remove(defs.use(i)))
		// 			str.append('f').append(i).append(" ");
		// 	}
		// 	if (str.charAt(str.length()-1)==' ')
		// 		str.deleteCharAt(str.length()-1);
		// 	str.append(")");
		// }
		// str.append(")");
		// System.out.println(str.toString());
		// if (!core.isEmpty()) {
		// 	Logger.getGlobal().warning(	"Returned minimal core is missing " + core.size() +
		// 								" formulas for which no definitions of the form (fi ...) were provided.\n");
        //     for (Iterator i = core.iterator(); i.hasNext(); ){
        //         Logger.getGlobal().warning("Core contains: " + i.next().toString() + "\n");
        //     }
		// }
	// }

	/**
	 * Logs the given solution and problem statistics to {@code this.logger} as info messages.
	 */
	void writeStats(KodkodProblem problem, Solution sol, StringBuilder str) {
		final Statistics stats = sol.stats();
		if (stats != null) {
			str.append(" :stats (");
			writeStat("size-variables", stats.variables(), str);
			writeStat("size-clauses", stats.clauses(), str);
			writeStat("size-primary", stats.primaryVariables(), str);

			final long pt = problem.buildTimeMillis(), ct = problem.coreTimeMillis(),
					tt = stats.translationTime(), st = stats.solvingTime();

			writeStat("time-translation", Long.max(tt, 0), str);
			writeStat("time-solving", Long.max(st, 0), str);
			writeStat("time-building", Long.max(pt, 0), str);
			if (sol.unsat()) writeStat("time-core", Long.max(ct, 0), str);

			str.append(")");
		}
	}

	/**
	 * Logs the given statistic and its value to {@code this.logger} as an info message.
	 */
	void writeStat(String stat, Object value, StringBuilder str) {
		str.append(String.format(" (%s %s)", stat, value));
	}

	/**
	 * Writes an info s-expression to the out stream. This meant to be
	 * ignored by the caller, except for info/debugging purposes.
	 */
	public void writeInfo(String info) {
		System.out.println(
						"(info \""+
							info.replaceAll("[()]", "")
									.replaceAll("\"", "'")+
						"\")");
	}

	/**
	 * Report memory usage info to caller as an (info ...) message.
	 */
	void printMemInfo() {
    	Runtime runtime = Runtime.getRuntime();
        NumberFormat format = NumberFormat.getInstance();
        StringBuilder sb = new StringBuilder();
        long maxMemory = runtime.maxMemory();
        long allocatedMemory = runtime.totalMemory();
        long freeMemory = runtime.freeMemory();
        final long mb = 1048576;
        sb.append("free memory MB: ");
        sb.append(format.format(freeMemory / mb));
        sb.append("\n");
        sb.append("allocated memory MB: ");
        sb.append(format.format(allocatedMemory / mb));
        sb.append("\n");
        sb.append("max memory MB: ");
        sb.append(format.format(maxMemory / mb));
        sb.append("\n");
        sb.append("total free memory MB: ");
        sb.append(format.format((freeMemory + (maxMemory - allocatedMemory)) / mb));
        sb.append("\n");
        writeInfo(sb.toString());
    }
}
