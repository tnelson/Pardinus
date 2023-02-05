package kodkod.test.cli;

import kodkod.cli.KodkodParser;
import kodkod.cli.KodkodServer;
import kodkod.cli.StandardKodkodOutput;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.parboiled.Parboiled;
import org.parboiled.parserunners.ErrorLocatingParseRunner;
import org.parboiled.parserunners.TracingParseRunner;
import org.parboiled.support.Chars;
import org.parboiled.support.ParsingResult;

import java.io.*;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

/**
 * Basic "does not crash" tests for stepper parsing (including temporal problems)
 */
@RunWith(Parameterized.class)
public class TestCLIStepper {

    static final String eoiString = String.valueOf(Chars.EOI);
    private KodkodParser parser;

    @Parameterized.Parameters
    public static List<Object[]> testFileNames() {
        // List.of requires Java 9
        final List<Object[]> tests = new ArrayList<>();
        tests.add(new Object[]{"singleStepper_bridgeCrossing.txt", KodkodServer.Feature.PLAIN_STEPPER});
        tests.add(new Object[]{"singleTemporal_lightsPuzzle.txt", KodkodServer.Feature.TEMPORAL});
        tests.add(new Object[]{"multipleStepper_graphRuns.txt", KodkodServer.Feature.PLAIN_STEPPER});
        tests.add(new Object[]{"singleStepper_unsatGraph.txt", KodkodServer.Feature.PLAIN_STEPPER});
        return tests;
    }

    @Parameterized.Parameter
    public String fileName;

    @Parameterized.Parameter(1)
    public KodkodServer.Feature feature;

    @Before
    public void setupEach() {
        parser = Parboiled.createParser(KodkodParser.class, feature, new StandardKodkodOutput());
    }

    /**
     * Wrap configuration (including assertions) and commands in (with ID ...)
     * Terminate "(with ...)" with an EOI. Don't send EOI except after "with"
     *
     * Because of this protocol, it's troublesome to test via the *IntelliJ* command line specifically
     * since ctrl-D ends the stream, rather than sending EOI.
     *
     * @throws IOException
     */
    @Test
    public void testCLI() throws IOException {
        URL dataUrl = getClass().getClassLoader().getResource(fileName);
        File dataFile = new File(dataUrl.getPath());
        byte[] dataBytes = Files.readAllBytes(dataFile.toPath());
        String data = new String(dataBytes, StandardCharsets.UTF_8).replaceAll("\\*\\*EOI\\*\\*", eoiString);

        for(String block : data.split(eoiString)) {
            //System.out.println("***** running "+block.substring(0, Math.min(30, block.length())));
            //new BasicParseRunner<>(parser.StepperStart()).run(block);
            ParsingResult<Object> result = new ErrorLocatingParseRunner<>(parser.StepperStart()).run(block);

            // KodkodServer will terminate if any parse errors occur
            //System.out.println("matched="+result.matched +" : hasErrors()="+result.hasErrors()+" : errors="+result.parseErrors);

            // For debugging (verbose)
            //new TracingParseRunner<>(parser.StepperStart()).run(block);
        }

    }
}
