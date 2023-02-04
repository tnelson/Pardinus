package kodkod.test.cli;

import kodkod.cli.KodkodParser;
import kodkod.cli.KodkodProblem;
import kodkod.cli.StandardKodkodOutput;
import org.junit.Before;
import org.junit.Test;
import org.parboiled.Parboiled;
import org.parboiled.parserunners.BasicParseRunner;
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
     * Old process: Problem and then Serve
     *
     * We EOI-terminate to say "ok, get to work"; server truncates at EOI.
     * Do not EOI within a "with" block.
     * @throws IOException
     */
    @Test
    public void testCLI() throws IOException {
        // Use this, not the constructor
        KodkodParser parser = Parboiled.createParser(KodkodParser.class, KodkodProblem.stepper(), new StandardKodkodOutput());
        URL dataUrl = getClass().getClassLoader().getResource("singleStepper_bridgeCrossing.txt");
        File dataFile = new File(dataUrl.getPath());
        byte[] dataBytes = Files.readAllBytes(dataFile.toPath());
        String data = new String(dataBytes, StandardCharsets.UTF_8).replaceAll("\\*\\*EOI\\*\\*", eoiString);

        boolean first = true;
        for(String block : data.split(eoiString)) {
            if(first)
                new BasicParseRunner<>(parser.StepperProblem()).run(block);
            else
                new BasicParseRunner<>(parser.StepperServe()).run(block);
            first = false;
        }

    }

}
