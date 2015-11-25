package kkpartition.examples;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.text.Format;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import kkpartition.MProblem;
import kkpartition.PProblem;
import kkpartition.ParallelSolver;
import kkpartition.ParallelSolver.Modes;
import kkpartition.ParallelSolver.Solvers;
import kkpartition.PartitionModel;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.IncrementalSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;

public final class RunTests {

	final static Solver solver = new Solver();
	final static ParallelSolver psolver = new ParallelSolver(solver);

	final static Map<Integer,List<PProblem>> stats = new HashMap<Integer,List<PProblem>> ();

	static PProblem psolution = null;
	static Solution solution = null;

	static boolean glucose, minisat, plingling, syrup;
	static boolean batch, sequential, parallel, hybrid, incremental;
	static int tries, threads = 4;

	static private StringBuilder log = new StringBuilder();
	static private StringBuilder header = new StringBuilder();

	static private PrintWriter writer;
	private static boolean ring, hotel, file, handshake;

	/**
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	public static void main(String[] args) throws IOException, InterruptedException {
		List<String> opts = Arrays.asList(args);

		writer = new PrintWriter(new FileWriter("pkklog.txt", true));

		tries = Integer.valueOf(args[0]);

		glucose = opts.contains("-gl");
		minisat = opts.contains("-ms");
		plingling = opts.contains("-pl");
		syrup = opts.contains("-sy");

		batch = opts.contains("-b");
		sequential = opts.contains("-s");
		parallel = opts.contains("-p");
		hybrid = opts.contains("-h");
		incremental = opts.contains("-i");

		ring = opts.contains("--ring");
		handshake = opts.contains("--handshake");
		hotel = opts.contains("--hotel");
		file = opts.contains("--file");

		printHeader();
		flush();

		if (ring) runRing();
		if (handshake) runHandshake();
		if (hotel) runHotel();
		if (file) runFileSystem();

	}

	private static void printHeader() {
		Format formatter = new SimpleDateFormat("YYYY-MM-dd_HH-mm-ss");
		log.append("\n------\n");
		log.append(formatter.format(new Date()));
		log.append("\n");
		log.append("Examples: ");
		if (hotel) log.append("Hotel ");
		if (ring) log.append("RingLeader ");
		if (handshake) log.append("Handshake ");
		if (file) log.append("FileSystem ");
		log.append("\n");

		log.append("Solvers: ");
		if (minisat) log.append("Minisat ");
		if (glucose) log.append("Glucose ");
		if (syrup) log.append("Syrup ");
		if (plingling) log.append("Plingeling ");
		log.append("\n");

		log.append("Modes: ");
		if (batch) log.append("Batch ");
		if (sequential) log.append("Sequential ");
		if (parallel) log.append("Parallel ");
		if (hybrid) log.append("Hybrid ");
		if (incremental) log.append("Incremental ");
		log.append("\n");

		log.append("Tries: ");
		log.append(tries);
		log.append("\n");
		log.append("Threads: ");
		log.append(threads);
		log.append("\n");

		header.append("n\t");
		for (int i = 0; i < tries; i++)
			if (minisat && batch) header.append("M.B\tSat\t");
		for (int i = 0; i < tries; i++)
			if (minisat && sequential) header.append("M.S\tSat\tC.#\tC.t\t");
		for (int i = 0; i < tries; i++)
			if (minisat && parallel) header.append("M.P\tSat\tC.#\tC.t\t");
		for (int i = 0; i < tries; i++)
			if (minisat && hybrid) header.append("M.H\tSat\tC.#\tC.t\t");
		for (int i = 0; i < tries; i++)
			if (minisat && incremental) header.append("M.I\tSat\t");

		for (int i = 0; i < tries; i++)
			if (glucose && batch) header.append("G.B\tSat\t");
		for (int i = 0; i < tries; i++)
			if (glucose && sequential) header.append("G.S\tSat\tC.#\tC.t\t");
		for (int i = 0; i < tries; i++)
			if (glucose && parallel) header.append("G.P\tSat\tC.#\tC.t\t");
		for (int i = 0; i < tries; i++)
			if (glucose && hybrid) header.append("G.H\tSat\tC.#\tC.t\t");
		for (int i = 0; i < tries; i++)
			if (glucose && incremental) header.append("G.I\tSat\t");

		for (int i = 0; i < tries; i++)
			if (syrup && batch) header.append("S.B\tSat\t");
		for (int i = 0; i < tries; i++)
			if (plingling && batch) header.append("P.B\tSat\t");

		header.append("\n");
	}

	/**
	 * Given a partitioned model, runs the model under all considered parameters.
	 * @param model
	 * @param sym
	 */
	private static void run_tests(PartitionModel model, int sym) {
		final Bounds b1 = model.bounds1();
		final Bounds b2 = model.bounds2();
		final Formula f1 = model.partition1();
		final Formula f2 = model.partition2();

		solver.options().setBitwidth(model.getBitwidth());
		solver.options().setSymmetryBreaking(sym);

		int cn = 0;
		int ch = 0;

		// warm up
		//		for (int i = 0; i<30; i++)
		//			solver.solve(f1, b1);

		// run under MiniSat in batch, sequential and parallel mode
		if (minisat) {
			solver.options().setSolver(SATFactory.MiniSat);
			if (batch)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					solution = go_batch(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			if (sequential)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(1);
					psolver.options().setHybrid(false);
					psolution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					cn = getConfigNum(psolver);
					log.append((t2-t1));
					log.append("\t");
				}
			if (parallel)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(threads);
					psolver.options().setHybrid(false);
					psolution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					cn = getConfigNum(psolver);
					log.append((t2-t1));
					log.append("\t");
				}	
			if (hybrid)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(threads);
					psolver.options().setHybrid(true);
					psolution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					ch = getConfigNum(psolver);
					log.append((t2-t1));
					log.append("\t");
				}	
		}

		// run under Glucose in batch, sequential and parallel mode
		if (glucose) {
			solver.options().setSolver(SATFactory.Glucose);
			if (incremental)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					solution = go_incremental(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			if (batch)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					solution = go_batch(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
			flush();
			if (sequential)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(1);
					psolver.options().setHybrid(false);
					psolution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					cn = getConfigNum(psolver);
					log.append((t2-t1));
					log.append("\t");
				}
			flush();
			if (parallel)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(threads);
					psolver.options().setHybrid(false);
					psolution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					cn = getConfigNum(psolver);
					log.append((t2-t1));
					log.append("\t");
					flush();
				}	
			flush();
			if (hybrid)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					psolver.options().setThreads(threads);
					psolver.options().setHybrid(true);
					psolution = psolver.solve(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					ch = getConfigNum(psolver);
					log.append((t2-t1));
					log.append("\t");
				}	
			flush();
		}

		// run under plingeling in batch
		if (syrup) {
			solver.options().setSolver(SATFactory.syrup());
			if (batch)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					solution = go_batch(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
		}

		// run under plingeling in batch
		if (plingling) {
			solver.options().setSolver(SATFactory.plingeling());
			if (batch)
				for (int i = 0; i < tries; i++) {
					long t1 = System.currentTimeMillis();
					solution = go_batch(b1, b2, f1, f2);
					long t2 = System.currentTimeMillis();
					log.append((t2-t1));
					log.append("\t");
				}
		}

		if (sequential || parallel || hybrid) {
			log.append(psolution.sat()?"S":"U");
			log.append("\t");
			if (sequential || parallel) {
				log.append(cn);
				log.append("\t");
			}
			if (hybrid) {
				log.append(ch);
				log.append("\t");
			}
			log.append(getGenTime(psolver));
		} else {
			log.append(solution.sat()?"S":"U");
		}

		flush();
	}

	private static void flush() {
		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}

	private static long getGenTime(ParallelSolver psolver2) {
		long counter = 0;
		for (PProblem p : psolver2.manager().solutions())
			if (p instanceof MProblem) counter = counter + ((MProblem) p).getConfigTime();
		return counter;
	}

	private static int getConfigNum(ParallelSolver psolver2) {
		int counter = psolver2.manager().solutions().size();
		if (!(psolver2.manager().solutions().get(psolver2.manager().solutions().size()-1) instanceof MProblem))
			counter = -counter;
		return counter;
	}

	/**
	 * Solves the problem under standard Kodkod (i.e., batch mode).
	 * @param b1
	 * @param b2
	 * @param f1
	 * @param f2
	 * @return 
	 */
	private static Solution go_batch(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		return solver.solve(f1.and(f2), b3);
	}

	private static Solution go_incremental(Bounds b1, Bounds b2, Formula f1, Formula f2) {
		IncrementalSolver isolver = IncrementalSolver.solver(solver.options());

		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		isolver.solve(f1,b3);
		b3.relations().clear();
		return isolver.solve(f2,b3);

		//		isolver.solve(f1,b1);
		//		return isolver.solve(f2,b2);
	}

	private static void printConfigs() {
		for (Integer i : stats.keySet()) {
			for (PProblem p : stats.get(i))
				System.out.println(p.toString());
			System.out.println();
		}		
	}

	/**
	 * Runs a model instance instance for the specified number of times.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runModelInstance(String model, String[] model_args) throws IOException, InterruptedException {
		String javaHome = System.getProperty("java.home");
		String javaBin = javaHome + File.separator + "bin" + File.separator + "java";
		String classpath = System.getProperty("java.class.path");
		String className = RunTestModel.class.getCanonicalName();
		String librarypath = System.getProperty("java.library.path");

		String[] cmd_args = new String[]{javaBin, "-Djava.library.path="+librarypath, "-cp", classpath, className, model};

		String[] args = Arrays.copyOf(cmd_args, cmd_args.length + model_args.length);
		System.arraycopy(model_args, 0, args, cmd_args.length, model_args.length);

		for (int k = 0; k < tries; k++) {
			Process p = Runtime.getRuntime().exec(args);

			InputStream stderr = p.getErrorStream();
			InputStreamReader isr = new InputStreamReader(stderr);
			BufferedReader br = new BufferedReader(isr);
			String line = null;
			while ( (line = br.readLine()) != null)
				System.out.println(line);
			int exitVal = p.waitFor();
		}
	}

	/**
	 * Runs a model variant for the specified modes and solvers.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runModes(String model, String[] model_args) throws IOException, InterruptedException {
		String[] args = new String[model_args.length+2];
		System.arraycopy(model_args, 0, args, 2, model_args.length);

		if (minisat) {
			args[1] = Solvers.MINISAT.name();
			for (Modes m : getModes()) {
				args[0] = m.name();
				runModelInstance(model,args);
			}
		}

		if (glucose) {
			args[1] = Solvers.GLUCOSE.name();
			for (Modes m : getModes()) {
				args[0] = m.name();
				runModelInstance(model,args);
			}
		}

		if (syrup) {
			if (getModes().contains(Modes.BATCH)) {
				args[0] = Modes.BATCH.name();
				args[1] = Solvers.SYRUP.name();
				runModelInstance(model,args);
			}
		}

		if (plingling) {
			if (getModes().contains(Modes.BATCH)) {
				args[0] = Modes.BATCH.name();
				args[1] = Solvers.PLINGELING.name();
				runModelInstance(model,args);
			}
		}

	}

	private static List<Modes> getModes() {
		List<Modes> modes = new ArrayList<Modes>();
		if (batch) modes.add(Modes.BATCH);
		if (sequential) modes.add(Modes.SEQUENTIAL);
		if (parallel) modes.add(Modes.PARALLEL);
		if (hybrid) modes.add(Modes.HYBRID);
		if (incremental) modes.add(Modes.INCREMENTAL);
		return modes;
	}

	private static List<Solvers> getSolvers() {
		List<Solvers> solvers = new ArrayList<Solvers>();
		if (minisat) solvers.add(Solvers.MINISAT);
		if (glucose) solvers.add(Solvers.GLUCOSE);
		if (syrup) solvers.add(Solvers.SYRUP);
		if (plingling) solvers.add(Solvers.PLINGELING);
		return solvers;
	}

	/**
	 * Tests the performance of all variants of the Ring example.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runRing() throws IOException, InterruptedException {
		String model = RingP.class.getCanonicalName();

		int t = 10;

		for (RingP.Variant2 s : RingP.Variant2.values())
			for (RingP.Variant1 v : RingP.Variant1.values()) {
				log.append(v.name()+" "+s.name()+" "+t+"\n"); 
				log.append(header);
				flush();
				for (int i = 1; i <= 6; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", t+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
			}

		t = 20;

		for (RingP.Variant2 s : RingP.Variant2.values())
			for (RingP.Variant1 v : RingP.Variant1.values()) {
				log.append(v.name()+" "+s.name()+" "+t+"\n"); 
				log.append(header);
				flush();
				for (int i = 1; i <= 6; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", t+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
			}

	}

	/**
	 * Tests the performance of all variants of the Handshake example.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runHandshake() throws IOException, InterruptedException {

		String model = HandshakeP.class.getCanonicalName();

		for (HandshakeP.Variant2 s : HandshakeP.Variant2.values())
			for (HandshakeP.Variant1 v : HandshakeP.Variant1.values()) {
				log.append(v.name()+" "+s.name()+"\n"); 
				log.append(header);
				flush();
				for (int i = 3; i <= 16; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
			}
	}

	/**
	 * Tests the performance of all variants of the Hotel example.
	 */
	private static void runHotel() throws IOException, InterruptedException {
		String model = HotelP.class.getCanonicalName();

		int t = 10;

		for (HotelP.Variant v : HotelP.Variant.values()) {
			log.append(v.name()+" "+t+"\n"); 
			log.append(header);
			flush();
			for (int i = 1; i <= 6; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}

		t = 20;

		for (HotelP.Variant v : HotelP.Variant.values()) {
			log.append(v.name()+" "+t+"\n"); 
			log.append(header);
			flush();
			for (int i = 1; i <= 6; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	}


	private static void runFileSystem() throws IOException, InterruptedException {
		String model = FilesystemP.class.getCanonicalName();

		for (FilesystemP.Variant v : FilesystemP.Variant.values()) {
			log.append(v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 3; i <= 16; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	}

}