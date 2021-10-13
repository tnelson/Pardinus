package kodkod.engine.proofExplanation.repl;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.util.HashMap;
import java.util.Map;

/** A Read,Eval,Print Loop class that provides the user with an interface to
 * perform a variety of commands that they specify on data that they provide.
 */
public class REPLInterface {

  /** The commands available for the user while interacting
   * with the REPL.
   */
  private final Map<String, Command> commands;
  private final BufferedReader reader;

  /** A constructor that generates a new REPLInterface from an InputStream.

   * @param inputStream The InputStream from which the BufferedReader
   *                    associated with this REPLInterface.
   */
  public REPLInterface(InputStream inputStream) {
    this.reader = new BufferedReader(new InputStreamReader(inputStream));
    this.commands = new HashMap<>();
  }

  /** A constructor that sets creates a REPLInterface with an empty commands
   * Map and a BufferedReader that reads from System.in.
   */
  public REPLInterface() {
    this(System.in);
  }

  /** Adds a given Command to the Map of commands such that the name of the Command
   * maps to the Command itself.

   * @param command The Command to be added.
   */
  public void addCommand(Command command) {
    this.commands.put(command.getName(), command);
  }

  /** Starts the REPL loop and continues accepting user commands
   * until the user end-of-file by entering ctrl-D.
   */
  public void start() {
    String commandLine;
    while (true) {
      try {
        commandLine = reader.readLine();
      } catch (IOException e) {
        break;
      }
      if (commandLine == null) {
        break;
      }
      try {
        String[] lineComponents = commandLine.split(" ", 2);
        String commandKey = lineComponents[0];
        String paramString = lineComponents[1];
        try {
          printEvalResult(commandKey, paramString);
        } catch (Exception e) {
          System.out.println(e.getMessage());
        }
      } catch (Exception e) {
        System.out.println("ERROR: Enter a command and a keyword");
      }
    }
  }

  /** Given a string representing a command and a string containing
   * the parameters for the command, this method executes the
   * command on said parameters and prints the results.
   *
   * @param commandKey The string the user enters to reference the
   *                   command to be executed.
   * @param paramString The string to parse for the parameters of
   *                    the command to be executed.
   * @throws Exception If invalid command entered or if an error occurs in processing.
   * */
  public void printEvalResult(String commandKey, String paramString) throws Exception {
    if (!(commands.containsKey(commandKey))) {
      throw new Exception("ERROR: Invalid command entered.");
    }
    Command toExecute = commands.get(commandKey);
    toExecute.displayExecutedResult(paramString);
  }
}

