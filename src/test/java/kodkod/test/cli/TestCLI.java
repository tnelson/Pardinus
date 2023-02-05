package kodkod.test.cli;

import kodkod.cli.KodkodParser;
import kodkod.cli.KodkodProblem;
import kodkod.cli.KodkodServer;
import kodkod.cli.StandardKodkodOutput;
import org.junit.Before;
import org.junit.Test;
import org.parboiled.Parboiled;
import org.parboiled.parserunners.BasicParseRunner;
import org.parboiled.parserunners.ErrorLocatingParseRunner;
import org.parboiled.parserunners.TracingParseRunner;
import org.parboiled.support.Chars;
import org.parboiled.support.ParsingResult;

import java.io.*;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;

/**
 *
 */
public class TestCLI {

    static final String eoiString = String.valueOf(Chars.EOI);

    @Before
    public void setupEach() {

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
        // Use this, not the constructor
        KodkodParser parser = Parboiled.createParser(KodkodParser.class, KodkodServer.Feature.PLAIN_STEPPER, new StandardKodkodOutput());
        URL dataUrl = getClass().getClassLoader().getResource("singleStepper_bridgeCrossing.txt");
        File dataFile = new File(dataUrl.getPath());
        byte[] dataBytes = Files.readAllBytes(dataFile.toPath());
        String data = new String(dataBytes, StandardCharsets.UTF_8).replaceAll("\\*\\*EOI\\*\\*", eoiString);

        for(String block : data.split(eoiString)) {
            //new BasicParseRunner<>(parser.StepperStart()).run(block);
            new ErrorLocatingParseRunner<>(parser.StepperStart()).run(block);
            // For debugging (verbose)
            //new TracingParseRunner<>(parser.StepperStart()).run(block);
        }

    }

}
