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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
package kodkod.engine.satlab;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.Closeable;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * An implementation of a wrapper for an external SAT solver, 
 * executed in a separate process.
 * @author Emina Torlak
 */
// [HASLab] public
final public class ExternalSolver implements SATSolver {
	private final boolean deleteTemp;
	private final String inTemp;
	public final String executable; // [HASLab]
	public final String[] options; // [HASLab]
	private final BitSet solution;
	private volatile Boolean sat;
	private volatile int vars, clauses;

    // How much of a solver's stderr to keep for error messages.
	private static final int STDERR_TAIL_CHARS = 2000;
	// The solver runs in this directory. 
	private final File workDir;
	// Temporary file to use. 
	private final File inTempFile;
	// DIMACS representation of all clauses added so far (used to re-write the CNF file for solvers)
	private final StringBuilder buffer;


	/**
	 * Constructs an ExternalSolver that will execute the specified binary
	 * with the given options on the {@code inTemp} file.  The {@code inTemp} file 
	 * will be initialized to contain all clauses added to this solver via the 
	 * {@link #addClause(int[])} method.  The solver is assumed to write its output 
	 * to standard out.  The {@code deleteTemp} flag indicates whether the temporary 
	 * files should be deleted when they are no longer needed by this solver.
	 * 
	 * If {@code deleteTemp} is true, the file is deleted when solve() returns or throws.
	 */
	ExternalSolver(String executable, String inTemp, boolean deleteTemp, String... options) {
		// To make sure relative paths in solver scripts work, the solver runs in its own directory.
		this.workDir = new File(executable).getAbsoluteFile().getParentFile();
		// The temporary file location is relative to the solver location.
		final File tempFile = new File(inTemp);
		this.inTempFile = tempFile.isAbsolute() ? tempFile : new File(workDir, inTemp);

		this.deleteTemp = deleteTemp;
		this.buffer = new StringBuilder();
		this.sat = null;
		this.solution = new BitSet();
		this.vars = 0;
		this.clauses = 0;
		this.executable = executable;
		this.inTemp = inTemp;
		// remove empty strings from the options array
		final List<String> nonEmpty = new ArrayList<String>(options.length);
		for(String opt : options) { 
			if (!opt.isEmpty())
				nonEmpty.add(opt);
		}
		this.options = nonEmpty.toArray(new String[nonEmpty.size()]);
	}

	/**
	 * Silently closes the given resource if it is non-null.
	 */
	private static void close(Closeable closeable) {
		try {
			if (closeable!=null)
				closeable.close();
		} catch (IOException e) { } // ignore
	}

	/**
	 * Writes DIMACS problem to file, replacing any contents that are already there.
	 */
	private final void writeCnf() throws SATAbortedException {
		try (Writer w = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(inTempFile), StandardCharsets.ISO_8859_1))) {
			w.write("p cnf " + vars + " " + clauses + "\n");
			w.append(buffer);
		} catch (IOException e) {
			throw new SATAbortedException("Could not write to custom solver's input file: " + e.getMessage(), e);
		}
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#addClause(int[])
	 */
	public boolean addClause(int[] lits) {
		clauses++;		
		// For now, adding a new clause will throw away the previous SAT result, forcing 
		// a re-run (although not a re-translation).
		if (sat == Boolean.TRUE) sat = null;
		for(int lit: lits) {
			buffer.append(lit);
			buffer.append(" ");
		}
		buffer.append("0\n");
		return true;
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#addVariables(int)
	 */
	public void addVariables(int numVars) {
		if (numVars < 0)
			throw new IllegalArgumentException("vars < 0: " + numVars);
		vars += numVars;
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#free()
	 */
	public synchronized void free() {
		// Assuming solve() is finished, there is no file to delete here.
		buffer.setLength(0);
		buffer.trimToSize();
	}


	/**
	 * Releases the resources used by this external solver.
	 */
	protected final void finalize() throws Throwable {
		super.finalize();
		free();
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
	 */
	public int numberOfClauses() {
		return clauses;
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
	 */
	public int numberOfVariables() {
		return vars;
	}

	/**
	 * @ensures |lit| <= this.vars && lit != 0 => this.solution'.set(|lit|, lit>0)
	 * @throws SATAbortedException  lit=0 || |lit|>this.vars
	 */
	private final void updateSolution(int lit) {
		int abs = StrictMath.abs(lit);
		if (abs<=vars && abs>0)
			solution.set(abs-1, lit>0);
		else
			throw new SATAbortedException("Invalid variable value: |" + lit + "| !in [1.."+vars+"]");
	}
	
	

	/**
	 * @see kodkod.engine.satlab.SATSolver#solve()
	 */
	public boolean solve() throws SATAbortedException {
		if (sat==null) {
			Process p = null;
			Thread errThread = null;
			final StringBuilder errTail = new StringBuilder();
			try {
				writeCnf();
				solution.clear();
				p = startSolver();
				errThread = new Thread(drain(p.getErrorStream(), errTail));
				// Don't let a solver that hangs after answering keep this thread occupied.
				errThread.setDaemon(true);
				errThread.start();
				readResult(p, errThread, errTail);
			} catch (IOException e) {
				if (p == null) {
					throw new SATAbortedException("The solver couldn't be run: " + executable + ": " + e.getMessage(), e);
				}
				throw new SATAbortedException(e.toString() + details(p, errThread, errTail), e);
			} catch (NumberFormatException e) {
				throw new SATAbortedException("Invalid "+ executable +" output: encountered a non-integer variable token."
						+ details(p, errThread, errTail), e);
			} finally {
				stopSolver(p);
				deleteCnf();
			}
		}
		return sat;
	}

	/**
	 * Start the custom solver. 
	 */
	private Process startSolver() throws IOException {
		final String[] command = new String[options.length+2];
		// The solver runs in workDir. (Avoid double-applying relative path.)
		command[0] = new File(executable).getAbsolutePath();
		System.arraycopy(options, 0, command, 1, options.length);
		command[command.length-1] = inTemp;
		return Runtime.getRuntime().exec(command, null, workDir);
	}

	/**
	 * Read the solver's output into this.sat and this.solution.
	 */
	private void readResult(Process p, Thread errThread, StringBuilder errTail) throws IOException {
		try (BufferedReader out = outputReader(p)) {
			String line = null;
			while((line = out.readLine()) != null) {
				String[] tokens = line.split("\\s");
				int tlength = tokens.length;
				if (tlength>0) {
					if (tokens[0].compareToIgnoreCase("s")==0) {
						if (tlength==2) {
							if (tokens[1].compareToIgnoreCase("SATISFIABLE")==0) {
								sat = Boolean.TRUE;
								continue;
							} else if (tokens[1].compareToIgnoreCase("UNSATISFIABLE")==0) {
								sat = Boolean.FALSE;
								// Stop here; no need to wait for the solver to stop.
								break;
							}
						}
						throw new SATAbortedException("Invalid " + executable + " output. Line: " + line + "."
								+ details(p, errThread, errTail));
					} else if (tokens[0].compareToIgnoreCase("v")==0) {
						int last = tlength-1;
						for(int i = 1; i < last; i++) {
							updateSolution(Integer.parseInt(tokens[i]));
						}
						int lit = Integer.parseInt(tokens[last]);
						if (lit!=0) updateSolution(lit);
						else if (sat!=null) break;
					} // not a solution line or a variable line, so ignore it.
				}
			}
			if (sat==null) {
				throw new SATAbortedException("Invalid " + executable + " output: no line specifying the outcome."
						+ details(p, errThread, errTail));
			}
		}
	}

	/**
	 * Best effort: give the solver some time to exit, then force it to stop.
	 */
	private static void stopSolver(Process p) {
		// Note TODO: only the process that _Java_ creates is stopped. Engines that that 
		// process calls may persist.
		if (p != null) {
			try {
				if (!p.waitFor(2, TimeUnit.SECONDS)) {
					p.destroyForcibly();
					p.waitFor(1, TimeUnit.SECONDS);
				}
			} catch (InterruptedException e) {
				p.destroyForcibly();
				Thread.currentThread().interrupt();
			}
		}
	}

	/**
	 * Deletes the custom-solvers temporary input file, if any.
	 */
	private void deleteCnf() {
		// Warning (usually for Windows) if deleting the file fails.
		if (deleteTemp && !inTempFile.delete() && inTempFile.exists()) {
			writeWarning("Could not delete custom-solver input file " + inTempFile.getAbsolutePath());
		}
	}
	
	/**
	 * Report a recoverable problem to the client. 
	 */
	private static void writeWarning(String msg) {
		System.out.println("(warning \"" + msg.replaceAll("[()]", "").replace("\\", "\\\\").replace("\"", "\\\"") + "\")");
	}

	/**
	 * Returns a runnable that drains the specified input stream.
	 * @return a runnable that drains the specified input stream.
	 */
	private static Runnable drain(final InputStream input, final StringBuilder tail) {
		return new Runnable() {
			public void run() {
				try {
					final byte[] buffer=new byte[8192];
					while(true) {
						int n=input.read(buffer);
						if (n<0) break;
						// Keep the tail of the solver's error, if any, for error messages.
						synchronized (tail) {
							tail.append(new String(buffer, 0, n));
							if (tail.length() > STDERR_TAIL_CHARS) {
								tail.delete(0, tail.length() - STDERR_TAIL_CHARS);
							}
						}
					}
				} catch (IOException ex) {
				} finally {
					close(input);
				}
			}
		};
	}

	// Obtain the exit code and (tail of) stderr of the solver, for error messages. 
	private static String details(Process p, Thread errThread, StringBuilder errTail) {
		final StringBuilder s = new StringBuilder();
		try {
			if (p.waitFor(2, TimeUnit.SECONDS)) {
				s.append(" Exit code ").append(p.exitValue()).append('.');
			}
			if (errThread != null) {
				errThread.join(2000);
			}
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
		}
		final String err;
		synchronized (errTail) {
			err = errTail.toString().trim();
		}
		s.append(err.isEmpty() ? " No error output." : " Solver error output:\n" + err);
		return s.toString();
	}

	/**
	 * Returns a reader for reading the output of the given process.
	 * @return a reader for reading the output of the given process.
	 */
	private BufferedReader outputReader(Process p) {
		return new BufferedReader(new InputStreamReader(p.getInputStream(), StandardCharsets.ISO_8859_1));
	}

	/**
	 * @see kodkod.engine.satlab.SATSolver#valueOf(int)
	 */
	public boolean valueOf(int variable) {
		if (!Boolean.TRUE.equals(sat))
			throw new IllegalStateException();
		if (variable < 1 || variable > vars)
			throw new IllegalArgumentException(variable + " !in [1.." + vars+"]");
		return solution.get(variable-1);
	}

	/**
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return executable + " " + options;
	}
}
