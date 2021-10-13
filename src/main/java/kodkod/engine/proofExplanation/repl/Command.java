package kodkod.engine.proofExplanation.repl;

/** An interface representing a command, providing options to
 * parse its parameters from a string and execute its functionality
 * on said parameters.
 * @param <T> represents the return type upon executing said functionality.
 **/
public interface Command<T> {
  /** Obtains the name of the given Command.

   * @return The name of the given Command.
   */
  String getName();

  /** Parses a string representing the parameters of a Command's functionality
   * (i.e. the string entered after the command name in the command line), and executes
   * said functionality on these parameters.

   * @param paramString The string representing the arguments sent into the Command
   *                    with individual components separated by spaces.
   * @return The result of executing the Command's functionality on these parameters.
   * @throws Exception If an error occurs during parsing or execution.
   */
  T parseAndExecute(String paramString) throws Exception;

  /** Displays the result of executing a Command on a String of parameters.

   * @param paramString The string representing the parameters to be acted upon.
   * @throws Exception If an error occurs during parsing, execution, or printing.
   */
  void displayExecutedResult(String paramString) throws Exception;
}
