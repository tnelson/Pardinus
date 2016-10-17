/*
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.engine.config;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.List;
import java.util.Set;

import kodkod.ast.Decl;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.bool.BooleanFormula;
import kodkod.instance.Bounds;
import kodkod.util.ints.IntSet;

/**
 * An implementation of the reporter interface that prints messages
 * to the standard output stream.
 * @author Emina Torlak
 * @modified Nuno Macedo // [HASLab] decomposed model finding
 */
public final class FileReporter implements Reporter {
	
	PrintWriter writer;
	
	/**
	 * Constructs a new instance of the ConsoleReporter.
	 */
	public FileReporter() {
		try {
			writer = new PrintWriter(new File("log.txt"));
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	/**
	 * @see kodkod.engine.config.Reporter#generatingSBP()
	 */
	public void generatingSBP() {
		writer.println("generating lex-leader symmetry breaking predicate...");
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#skolemizing(kodkod.ast.Decl, kodkod.ast.Relation, java.util.List)
	 */
	public void skolemizing(Decl decl, Relation skolem, List<Decl> context) {}

	/**
	 * @see kodkod.engine.config.Reporter#solvingCNF(int, int, int)
	 */
	public void solvingCNF(int primaryVars, int vars, int clauses) {
		writer.println("solving p cnf " + vars + " " + clauses);
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#detectingSymmetries(kodkod.instance.Bounds)
	 */
	public void detectingSymmetries(Bounds bounds){}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.config.Reporter#detectedSymmetries(java.util.Set)
	 */
	public void detectedSymmetries(Set<IntSet> parts) {}
	
	/**
	 * @see kodkod.engine.config.Reporter#optimizingBoundsAndFormula()
	 */
	public void optimizingBoundsAndFormula() {}
	
	/**
	 * @see kodkod.engine.config.Reporter#translatingToBoolean(kodkod.ast.Formula, kodkod.instance.Bounds)
	 */
	public void translatingToBoolean(Formula formula, Bounds bounds) {
		writer.println("translating to boolean... ");
	}

	/**
	 * @see kodkod.engine.config.Reporter#translatingToCNF(kodkod.engine.bool.BooleanFormula)
	 */
	public void translatingToCNF(BooleanFormula circuit) {}
	
	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "FileReporter";
	}

	// [HASLab]
	public void solvingConfig(Solution solution) {
		writer.println("new configuration...");
	}

	@Override
	public void configOutcome(Solution solution) {
		writer.println("new config solved: "+solution.outcome());
	}

	@Override
	public void amalgOutcome(Solution solution) {
		writer.println("amalg solved: "+solution.outcome());
	}
	

}
