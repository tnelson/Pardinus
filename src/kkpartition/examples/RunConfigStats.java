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

public final class RunConfigStats {

	final static Solver solver = new Solver();
	final static ParallelSolver psolver = new ParallelSolver(solver);

	final static Map<Integer,List<PProblem>> stats = new HashMap<Integer,List<PProblem>> ();

	static PProblem psolution = null;
	static Solution solution = null;

	static int threads = 4;

	static private StringBuilder log = new StringBuilder();
	static private StringBuilder header = new StringBuilder();

	static private PrintWriter writer;
	private static boolean ring, hotel, file, handshake, span, dijkstra, diffeg, netconfig, redblack, dining, peaceable, jobs, lift;
	
	/**
	 * @throws IOException 
	 * @throws InterruptedException 
	 */
	public static void main(String[] args) throws IOException, InterruptedException {
		List<String> opts = Arrays.asList(args);

		writer = new PrintWriter(new FileWriter("pkklog.txt", true));

		if (opts.contains("--all")) {
			diffeg = true;
			dijkstra = true;
			dining = true;
			file = true;
			handshake = true;
			hotel = true;
			jobs = true;
			lift = true;
			peaceable = true;
			redblack = true;
			netconfig = true;
			ring = true;
			span = true;
		} else {
			diffeg = opts.contains("--diffeg");
			dijkstra = opts.contains("--dijkstra");
			dining = opts.contains("--dining");
			file = opts.contains("--file");
			handshake = opts.contains("--handshake");
			hotel = opts.contains("--hotel");
			jobs = opts.contains("--jobs");
			lift = opts.contains("--lift");
			peaceable = opts.contains("--peaceable");
			redblack = opts.contains("--redblack");
			netconfig = opts.contains("--netconfig");
			ring = opts.contains("--ring");
			span = opts.contains("--span");
		}
		
		printHeader();
		flush();

		if (diffeg) runDiffEg();
		if (dijkstra) runDijkstra();
		if (dining) runDining();
		if (file) runFileSystem();
		if (handshake) runHandshake();
		if (hotel) runHotel();
        if (jobs) runJobs();
        if (lift) runLift();
        if (peaceable) runPeaceable();
        if (redblack) runRedBlack();
        if (netconfig) runNetconfig();
		if (ring) runRing();
		if (span) runSpanTree();

	}

	private static void printHeader() {
		Format formatter = new SimpleDateFormat("YYYY-MM-dd_HH-mm-ss");
		log.append("\n------\n");
		log.append(formatter.format(new Date()));
		log.append("\n");
		log.append("Examples: ");
		if (diffeg) log.append("DiffEg ");
		if (dijkstra) log.append("Dijkstra ");
		if (dining) log.append("DiningPhil ");
		if (file) log.append("FileSystem ");
		if (handshake) log.append("Handshake ");
		if (hotel) log.append("HotelLocking ");
        if (jobs) log.append("Jobs ");
        if (lift) log.append("ElevatorSPL ");
        if (peaceable) log.append("PeaceableQueens ");
        if (redblack) log.append("RedBlackTree ");
        if (netconfig) log.append("NetConfig ");
		if (ring) log.append("Ring ");
		if (span) log.append("SpanTree ");
		log.append("\n");

		log.append("Modes: ");
		log.append(Modes.STATS);
		log.append("\n");
		
		log.append("Threads: ");
		log.append(threads);
		log.append("\n");

		header.append("n\t#\tS\tU\t%\tV1\tC1\tV2\tC2\tt\n");
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
		
		Process p = Runtime.getRuntime().exec(args);

		InputStream stderr = p.getErrorStream();
		InputStreamReader isr = new InputStreamReader(stderr);
		BufferedReader br = new BufferedReader(isr);
		String line = null;
		while ( (line = br.readLine()) != null)
			System.out.println(line);
		exitVal = p.waitFor();
		System.out.print("OK\t\t");
		
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

		args[0] = Modes.STATS.name();
		args[1] = Solvers.GLUCOSE.name();
		runModelInstance(model,args);
	}

	private static void runDiffEg() throws IOException, InterruptedException {
		String model = DiffEgP.class.getCanonicalName();
		log.append("DiffEg"+"\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 30; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+""});
			log.append("\n"); flush();
		}
		log.append("\n");
	}


	private static void runDijkstra() throws IOException, InterruptedException {

		String model = DijkstraP.class.getCanonicalName();
		int t = 15;
		DijkstraP.Variant v = DijkstraP.Variant.values()[0];
//		for (DijkstraP.Variant v : DijkstraP.Variant.values()) {
			log.append("Dijkstra"+t+" "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 12; i <= 12; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", i+"", t+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
//		}
			v = DijkstraP.Variant.values()[1];

			log.append("Dijkstra"+t+" "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 12; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", i+"", t+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
	}
	


	private static void runDining() throws IOException, InterruptedException {
		String model = DiningP.class.getCanonicalName();
		log.append("Dining"+"\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 8; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"",20+""});
			log.append("\n"); flush();
		}
		log.append("\n");		
	}

	private static void runFileSystem() throws IOException, InterruptedException {
		String model = FilesystemP.class.getCanonicalName();
	
		for (FilesystemP.Variant v : FilesystemP.Variant.values()) {
			log.append("FileSystem "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 5; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", v.name()});
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
				log.append("Handshake "+v.name()+" "+s.name()+"\n"); 
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

	/**
	 * Tests the performance of all variants of the Hotel example.
	 */
	private static void runHotel() throws IOException, InterruptedException {
		String model = HotelP.class.getCanonicalName();
	
		int t = 10;
	
		for (HotelP.Variant v : HotelP.Variant.values()) {
			log.append("Hotel "+v.name()+" "+t+"\n"); 
			log.append(header);
			flush();
			for (int i = 1; i <= 5; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"", v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	
		t = 20;
	
		for (HotelP.Variant v : HotelP.Variant.values()) {
			log.append("Hotel "+v.name()+" "+t+"\n"); 
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

	private static void runJobs() throws IOException, InterruptedException {
		String model = JobsP.class.getCanonicalName();
		log.append("Jobs"+"\n"); 
		log.append(header);
		flush();
		log.append("\t"); flush();
		runModes(model, new String[]{});
		log.append("\n"); flush();
		log.append("\n");		
	}

	private static void runLift() throws IOException, InterruptedException {
		String model = LiftP.class.getCanonicalName();
		log.append("Lift"+"\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 4; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"",20+""});
			log.append("\n"); flush();
		}
		log.append("\n");		
	}

	private static void runNetconfig() throws IOException, InterruptedException {

		String model = NetconfigP.class.getCanonicalName();
		log.append("Netconfig"+"\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 16; i ++)  {
			log.append(i+"\t"); flush();
			runModes(model, new String[]{i+"",1+"",i+"",20+""});
			log.append("\n"); flush();
		}
		log.append("\n");
	}

	
	private static void runPeaceable() throws IOException, InterruptedException {

		String model = PeaceableP.class.getCanonicalName();
		log.append("Peaceable Queens\n"); 
		log.append(header);
		flush();
		for (int i = 2; i <= 8; i ++)  {
			for (int j = 2; j <= 8; j ++)  {
				log.append(i+" "+j+"\t"); flush();
				runModes(model, new String[]{i+"",j+""});
				log.append("\n"); flush();
			}		
		}
		log.append("\n");		
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
				log.append("Ring "+v.name()+" "+s.name()+" "+t+"\n"); 
				log.append(header);
				flush();
				for (int i = 1; i <= 7; i ++)  {
					log.append(i+"\t"); flush();
					runModes(model, new String[]{i+"", t+"", v.name(), s.name()});
					log.append("\n"); flush();
				}
				log.append("\n");
			}
	
		t = 20;
	
		for (RingP.Variant2 s : RingP.Variant2.values())
			for (RingP.Variant1 v : RingP.Variant1.values()) {
				log.append("Ring "+v.name()+" "+s.name()+" "+t+"\n"); 
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

	private static void runSpanTree() throws IOException, InterruptedException {

		String model = SpanP.class.getCanonicalName();
		int t = 8;
		for (SpanP.Variant v : SpanP.Variant.values()) {
			log.append("Span"+t+" "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 14; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}

		t = 12;
		for (SpanP.Variant v : SpanP.Variant.values()) {
			log.append("Span"+t+" "+v.name()+"\n"); 
			log.append(header);
			flush();
			for (int i = 2; i <= 14; i ++)  {
				log.append(i+"\t"); flush();
				runModes(model, new String[]{i+"", t+"",v.name()});
				log.append("\n"); flush();
			}
			log.append("\n");
		}
	}

}