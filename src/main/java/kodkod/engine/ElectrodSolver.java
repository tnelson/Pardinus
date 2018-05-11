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
package kodkod.engine;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.engine.unbounded.ElectrodPrinter;
import kodkod.engine.unbounded.ElectrodReader;
import kodkod.engine.unbounded.InvalidUnboundedProblem;
import kodkod.engine.unbounded.InvalidUnboundedSolution;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;

/**
 * A computational engine for solving unbounded temporal relational
 * satisfiability problems. Such a problem is described by a
 * {@link kodkod.ast.Formula formula} in first order temporal relational logic;
 * finite unbounded temporal {@link PardinusBounds bounds} on the value of each
 * {@link Relation relation} constrained by the respective formula; and a set of
 * {@link ExtendedOptions options}, although there are currently no particular
 * options for unbounded temporal solving.
 * 
 * <p>
 * An {@link ElectrodSolver} takes as input a relational problem and produces a
 * satisfying model or a {@link TemporalInstance temporal instance} of it, if
 * one exists.
 * </p>
 * 
 * <p>
 * Although Electrod does not support solution iteration, it is implemented as
 * an {@link IterableSolver} in order to be used by the Alloy Analyzer. This
 * iterator contains one single satisfiable solution.
 * </p>
 * 
 * @author Nuno Macedo // [HASLab] unbounded temporal model finding
 */
public class ElectrodSolver implements UnboundedSolver<ExtendedOptions>,
		TemporalSolver<ExtendedOptions>,
		IterableSolver<PardinusBounds, ExtendedOptions> {

	private final ExtendedOptions options;

	/**
	 * Constructs a new Electrod solver with the given options.
	 * 
	 * @param options the solver options.
	 * @throws NullPointerException
	 *             options = null
	 */
	public ElectrodSolver(ExtendedOptions options) {
		if (options == null)
			throw new NullPointerException();
		this.options = options;
	}

	/**
	 * {@inheritDoc}
	 */
	public ExtendedOptions options() {
		return options;
	}

	/**
	 * {@inheritDoc}
	 */
	public Solution solve(Formula formula, PardinusBounds bounds)
			throws InvalidUnboundedProblem, InvalidUnboundedSolution {
		Reporter rep = options.reporter();

		// create a directory with the specified unique name
		String temp=System.getProperty("java.io.tmpdir");
		File dir = new File(temp+File.separatorChar+options.uniqueName());
		if (!dir.exists()) dir.mkdir();
		
		String file = dir.toString()+File.separatorChar+String.format("%05d", bounds.integration);
		PrintWriter writer;
		try {
			if (!Options.isDebug())
				new File(file+".elo").deleteOnExit();
			writer = new PrintWriter(file+".elo");
			String electrod = ElectrodPrinter.print(formula, bounds, rep);
			writer.println(electrod);
			writer.close();
			rep.debug("New Electrod problem at "+dir+".");
		} catch (FileNotFoundException e) {
			throw new AbortedException("Electrod problem generation failed.", e);
		}
		ProcessBuilder builder;
		if (options.solver().toString().equals("electrodX")) {
			builder = new ProcessBuilder("electrod",Options.isDebug()?"-v":"--",file+".elo");
		} else {
			builder = new ProcessBuilder("electrod","-t","NuSMV",Options.isDebug()?"-v":"--",file+".elo");
		}
		builder.environment().put("PATH", builder.environment().get("PATH")+":/usr/local/bin:.");
		builder.redirectErrorStream(true);
		int ret;
		try {
			Process p = builder.start();
			
			BufferedReader output = new BufferedReader(new InputStreamReader(
					p.getInputStream()));

			String oline = "";
			while ((oline = output.readLine()) != null)
				rep.debug(oline);

			ret = p.waitFor();
		} catch (InterruptedException e) {
			throw new AbortedException("Electrod problem interrupted.", e);
		} catch (IOException e) {
			throw new AbortedException("Electrod process failed.", e);
		}

		if (ret != 0) {
			rep.warning("Electrod exit code: "+ret);
			throw new AbortedException("Electrod exit code: "+ret);
		}
		else
			rep.debug("Electrod ran successfully.");
		
		File xml = new File(file+".xml");
		
		if (!Options.isDebug())
			xml.deleteOnExit();

		if (!xml.exists())
			throw new AbortedException("XML solution file not found: "+file+".xml.");
		else {
			rep.debug(file);

			ElectrodReader rd = new ElectrodReader(bounds);
			TemporalInstance res = rd.read(xml);
			
			Statistics st = new Statistics(rd.nbvars, 0,0, rd.ctime, rd.atime);

			Solution sol;
			// ElectrodReader#read returns null if unsat
			if (res == null)
				sol = Solution.unsatisfiable(st, null);
			else
				sol = Solution.satisfiable(st, res);
			
			return sol;
		}
	}

	/**
	 * {@inheritDoc}
	 */
	public void free() {}

	/**
	 * {@inheritDoc}
	 * 
	 * Electrod problems return a single solution, thus this iterator has
	 * exactly one satisfiable element and one unsatisfiable.
	 */
	public Iterator<Solution> solveAll(Formula formula, PardinusBounds bounds) {
		Solution s = solve(formula,bounds);

		Solution[] ss;
		if (s.sat())
			// TODO: get the stats from the header of the electrod solution
			ss = new Solution[]{s,Solution.unsatisfiable(new Statistics(0, 0, 0, 0, 0), null)};
		else
			ss = new Solution[]{s};
		
		return Arrays.asList(ss).iterator();
	}

}
