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

import kkpartition.PProblem;
import kkpartition.ParallelOptions.Modes;
import kkpartition.ParallelOptions.Solvers;
import kkpartition.ParallelSolver;
import kodkod.engine.Solution;
import kodkod.engine.Solver;

public final class RunTests {

	final static Solver solver = new Solver();
	final static ParallelSolver psolver = new ParallelSolver(solver);

	final static Map<Integer,List<PProblem>> stats = new HashMap<Integer,List<PProblem>> ();

	static PProblem psolution = null;
	static Solution solution = null;

	static int tries, threads = 4;

	static private StringBuilder log = new StringBuilder();
	static private StringBuilder header = new StringBuilder();

	static private PrintWriter writer;
	private static boolean ring, hotel, file, handshake, span, dijkstra, diffeg, netconfig, redblack;

	private static List<Modes> modes = new ArrayList<Modes>();
	private static List<Solvers> solvers = new ArrayList<Solvers>();

	/**
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	public static void main(String[] args) throws IOException, InterruptedException {
		List<String> opts = Arrays.asList(args);

		writer = new PrintWriter(new FileWriter("pkklog.txt", true));

		tries = Integer.valueOf(args[0]);

		if(opts.contains("-ms")) solvers.add(Solvers.MINISAT);
		if(opts.contains("-gl")) solvers.add(Solvers.GLUCOSE);
		if(opts.contains("-sy")) solvers.add(Solvers.SYRUP);
		if(opts.contains("-pl")) solvers.add(Solvers.PLINGELING);

		if(opts.contains("-b")) modes.add(Modes.BATCH);
		if(opts.contains("-s")) modes.add(Modes.SEQUENTIAL);
		if(opts.contains("-p")) modes.add(Modes.PARALLEL);
		if(opts.contains("-h")) modes.add(Modes.HYBRID);
		if(opts.contains("-i")) modes.add(Modes.INCREMENTAL);

		ring = opts.contains("--ring");
		handshake = opts.contains("--handshake");
		hotel = opts.contains("--hotel");
		file = opts.contains("--file");
		span = opts.contains("--span");
		dijkstra = opts.contains("--dijkstra");
		diffeg = opts.contains("--diffeg");
		netconfig = opts.contains("--netconfig");
		redblack = opts.contains("--redblack");

		printHeader();
		flush();

		if (handshake) runHandshake();
		if (hotel) runHotel();
		if (ring) runRing();
		if (file) runFileSystem();
		if (span) runSpanTree();
		if (dijkstra) runDijkstra();
		if (diffeg) runDiffEg();
		if (netconfig) runNetconfig();
		if (redblack) runRedBlack();

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
		log.append(solvers);
		log.append("\n");

		log.append("Modes: ");
		log.append(modes);
		log.append("\n");

		log.append("Tries: ");
		log.append(tries);
		log.append("\n");

		log.append("Threads: ");
		log.append(threads);
		log.append("\n");

		header.append("n\t");
		if (solvers.contains(Solvers.MINISAT)) {
			if (modes.contains(Modes.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("M.B\tSat\t");
			if (modes.contains(Modes.SEQUENTIAL))
				for (int i = 0; i < tries; i++)
					header.append("M.S\tSat\tC.#\tC.t\t");
			if (modes.contains(Modes.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("M.P\tSat\tC.#\tC.t\t");
			if (modes.contains(Modes.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("M.H\tSat\tC.#\tC.t\t");
			if (modes.contains(Modes.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("M.I\tSat\t");
		}

		if (solvers.contains(Solvers.GLUCOSE)) {
			if (modes.contains(Modes.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("G.B\tSat\t");
			if (modes.contains(Modes.SEQUENTIAL))
				for (int i = 0; i < tries; i++)
					header.append("G.S\tSat\tC.#\tC.t\t");
			if (modes.contains(Modes.PARALLEL))
				for (int i = 0; i < tries; i++)
					header.append("G.P\tSat\tC.#\tC.t\t");
			if (modes.contains(Modes.HYBRID))
				for (int i = 0; i < tries; i++)
					header.append("G.H\tSat\tC.#\tC.t\t");
			if (modes.contains(Modes.INCREMENTAL))
				for (int i = 0; i < tries; i++)
					header.append("G.I\tSat\t");
		}

		if (solvers.contains(Solvers.SYRUP)) {
			if (modes.contains(Modes.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("S.B\tSat\t");
		}

		if (solvers.contains(Solvers.PLINGELING)) {
			if (modes.contains(Modes.BATCH))
				for (int i = 0; i < tries; i++)
					header.append("P.B\tSat\t");
		}

		header.append("\n");
	}

	private static void flush() {
		System.out.print(log.toString());
		writer.print(log.toString());
		writer.flush();
		log = new StringBuilder();
	}

	/**
	 * Runs a model instance instance for the specified number of times.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static int runModelInstance(String model, String[] model_args) throws IOException, InterruptedException {
		String javaHome = System.getProperty("java.home");
		String javaBin = javaHome + File.separator + "bin" + File.separator + "java";
		String classpath = System.getProperty("java.class.path");
		String className = RunTestModel.class.getCanonicalName();
		String librarypath = System.getProperty("java.library.path");

		String[] cmd_args = new String[]{javaBin, "-Djava.library.path="+librarypath, "-cp", classpath, className, model};

		String[] args = Arrays.copyOf(cmd_args, cmd_args.length + model_args.length);
		System.arraycopy(model_args, 0, args, cmd_args.length, model_args.length);

		int exitVal = -1;

		for (int k = 0; k < tries; k++) {
			Process p = Runtime.getRuntime().exec(args);

			InputStream stderr = p.getErrorStream();
			InputStreamReader isr = new InputStreamReader(stderr);
			BufferedReader br = new BufferedReader(isr);
			String line = null;
			while ( (line = br.readLine()) != null)
				System.out.println(line);
			exitVal = p.waitFor();
			System.out.print("OK\t\t");
		}

		return exitVal;
	}

	/**
	 * Runs a model variant for the specified modes and solvers.
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	private static void runModes(String model, String[] model_args) throws IOException, InterruptedException {
		String[] args = new String[model_args.length+2];
		System.arraycopy(model_args, 0, args, 2, model_args.length);

		if (solvers.contains(Solvers.MINISAT)) {
			args[1] = Solvers.MINISAT.name();
			for (Modes m : modes) {
				args[0] = m.name();
				runModelInstance(model,args);
			}
		}

		if (solvers.contains(Solvers.GLUCOSE)) {
			args[1] = Solvers.GLUCOSE.name();
			for (Modes m : modes) {
				args[0] = m.name();
				runModelInstance(model,args);
			}
		}

		if (solvers.contains(Solvers.SYRUP)) {
			if (modes.contains(Modes.BATCH)) {
				args[0] = Modes.BATCH.name();
				args[1] = Solvers.SYRUP.name();
				runModelInstance(model,args);
			}
		}

		if (solvers.contains(Solvers.PLINGELING)) {
			if (modes.contains(Modes.BATCH)) {
				args[0] = Modes.BATCH.name();
				args[1] = Solvers.PLINGELING.name();
				runModelInstance(model,args);
			}
		}

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
				for (int i = 1; i <= 8; i ++)  {
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
				for (int i = 1; i <= 7; i ++)  {
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
				for (int i = 3; i <= 14; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
			}
	}

	private static void runRedBlack() throws IOException, InterruptedException {

		String model = RedBlackTreeP.class.getCanonicalName();

		for (RedBlackTreeP.Variant1 v : RedBlackTreeP.Variant1.values()) 
			for (RedBlackTreeP.Variant2 s : RedBlackTreeP.Variant2.values()) {
				log.append("Red Black Tree "+v.name()+" "+s.name()+"\n"); 
				log.append(header);
				flush();
				for (int i = 2; i <= 11; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
			}
	}

	private static void runSpanTree() throws IOException, InterruptedException {

		String model = SpanP.class.getCanonicalName();
		int t = 8;
		log.append("Span"+t+"\n"); 
		log.append(header);
		flush();
		for (int i = 10; i <= 14; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"", t+""});
			log.append("\n"); flush();
		}
		log.append("\n");

		t = 12;
		log.append("Span"+t+"\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 14; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"", t+""});
			log.append("\n"); flush();
		}
		log.append("\n");
}

	private static void runDijkstra() throws IOException, InterruptedException {

		String model = DijkstraP.class.getCanonicalName();
		int t = 20;
		log.append("Dijkstra"+t+"\n"); 
		log.append(header);
		flush();
		for (int i = 5; i <= 20; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"", i+"", t+""});
			log.append("\n"); flush();
		}
		log.append("\n");
	}

	private static void runDiffEg() throws IOException, InterruptedException {

		String model = DiffEgP.class.getCanonicalName();
		log.append("DiffEg"+"\n"); 
		log.append(header);
		flush();
		for (int i = 30; i <= 40; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+""});
			log.append("\n"); flush();
		}
		log.append("\n");
	}

	private static void runNetconfig() throws IOException, InterruptedException {

		String model = NetconfigP.class.getCanonicalName();
		log.append("Netconfig"+"\n"); 
		log.append(header);
		flush();
		for (int i = 3; i <= 20; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"",1+"",i+"",20+""});
			log.append("\n"); flush();
		}
		log.append("\n");
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
			for (int i = 1; i <= 5; i ++)  {
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
			for (int i = 3; i <= 14; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	}

}