package kodkod.instance;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryIntExpression;
import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.Comprehension;
import kodkod.ast.ConstantExpression;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Decl;
import kodkod.ast.Decls;
import kodkod.ast.ExprToIntCast;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IfExpression;
import kodkod.ast.IfIntExpression;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.IntConstant;
import kodkod.ast.IntExpression;
import kodkod.ast.IntToExprCast;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryExpression;
import kodkod.ast.NaryFormula;
import kodkod.ast.NaryIntExpression;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.ProjectExpression;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.SumExpression;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryExpression;
import kodkod.ast.UnaryIntExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.VarRelation;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.IntOperator;
import kodkod.ast.operator.Multiplicity;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.VoidVisitor;
import kodkod.engine.bool.BooleanFormula;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.engine.fol2sat.Translator;
import kodkod.util.ints.IndexedEntry;
import kodkod.util.ints.IntSet;
import kodkod.util.ints.SparseSequence;


// TODO: get bounds after symmetry breaking for predicates

public class ElectrodProblemPrinter {

	public static String print(Formula formula, PardinusBounds bounds) {
		Options opt = new ExtendedOptions();
		StringBuilder temp = new StringBuilder();
		Reporter reporter = new Reporter() {
			
			@Override
			public void translatingToCNF(BooleanFormula circuit) {}
			
			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {}
			
			@Override
			public void solvingCNF(int primaryVars, int vars, int clauses) {}
			
			@Override
			public void skolemizing(Decl decl, Relation skolem, List<Decl> context) {}
			
			@Override
			public void reportLex(List<Entry<Relation, Tuple>> _original,
					List<Entry<Relation, Tuple>> _permuted) {
				String tmp = printTupleList(_original,false);
				temp.append(tmp.substring(0,tmp.length()-1));
				temp.append(" <= ");
				temp.append(printTupleList(_permuted,false).substring(1));
				temp.append(";\n");
			}
			
			@Override
			public void optimizingBoundsAndFormula() {}
			
			@Override
			public void generatingSBP() {}
			
			@Override
			public void detectingSymmetries(Bounds bounds) {}
			
			@Override
			public void detectedSymmetries(Set<IntSet> parts) {}

			@Override
			public void debug(String debug) {}
		};
		
		opt.setReporter(reporter);
		Instance config = bounds.config;
		try {
		Translator.translate(Expression.NONE.some().or(Expression.NONE.no()), bounds, opt);
		} catch (Exception e) {}
		StringBuilder sb = new StringBuilder();
		sb.append(printUniverse(bounds.universe()));
		sb.append(printBounds(bounds));
		sb.append(printPartialIntance(config));
		sb.append(printSymmetries(temp.toString()));
		sb.append(printConstraint(formula));
		return sb.toString();
	}

	private static String printUniverse(Universe universe) {
		StringBuilder sb = new StringBuilder("univ : { ");
		Iterator<Object> it = universe.iterator();
		while (it.hasNext()) {
			sb.append(normRel(it.next().toString()));
			sb.append(" ");
		}
		sb.append("};\n\n");
		return sb.toString();
	}

	private static String printConstraint(Formula formula) {
		StringBuilder sb = new StringBuilder("run\n");
		if (formula instanceof NaryFormula && ((NaryFormula) formula).op() == FormulaOperator.AND) {
			for (int i = 0; i < ((NaryFormula) formula).size(); i++) {
				sb.append(printFormula(((NaryFormula) formula).child(i)));
				sb.append(";\n");
			}
		} else {
			sb.append(printFormula(formula));
			sb.append(";\n");
		}
		return sb.toString();
	}

	private static String printSymmetries(String tmp) {
		StringBuilder sb = new StringBuilder("sym\n");
		sb.append(normRel(tmp));
		sb.append("\n");
		return sb.toString();
	}

	private static String printBounds(Bounds bounds) {
		StringBuilder sb = new StringBuilder();
		Bounds bnd = bounds; //. amalgamated();
		for (Relation r : bnd.relations()) {
			if (r instanceof VarRelation)
				sb.append("var ");
			else
				sb.append("const ");
			sb.append(normRel(r.toString()));
			sb.append(" :");
			sb.append(r.arity());
			sb.append(" ");
			if (bnd.lowerBound(r).size() == bnd.upperBound(r).size()) {
				sb.append(printTupleList(bnd.lowerBound(r)));
			}
			else {
				sb.append(printTupleList(bnd.lowerBound(r)));
				sb.append(" ");
				sb.append(printTupleList(bnd.upperBound(r)));
			}
			sb.append(";\n");
		}
		sb.append("const ints :1 ");
		sb.append(printTupleList(bnd.intBounds()));
		sb.append(";\n\n");
		return sb.toString();
	}

	private static String printPartialIntance(Instance config) {
		StringBuilder sb = new StringBuilder();
		if (config != null) {
			sb.append("inst\n");
			for (Relation r : config.relations()) {
				sb.append(normRel(r.toString()));
				sb.append(" = ");
				sb.append(printTupleList(config.tuples(r)));
				sb.append(";\n");
			}
		sb.append("\n");
		}
		return sb.toString();
	}
	
	static String printTupleList(Collection<Tuple> col) {
		StringBuilder sb = new StringBuilder("{ ");
		for (Tuple t : col) {
			sb.append("(");
			sb.append(printTuple(t));
			sb.append(") ");
		}
		sb.append("}");
		return sb.toString();
	}
	
	private static Object printTupleList(SparseSequence<TupleSet> intBounds) {
		StringBuilder sb = new StringBuilder("{ ");
		Iterator<IndexedEntry<TupleSet>> it = intBounds.iterator();
		while (it.hasNext()) {
			sb.append("(");
			sb.append(it.next());
			sb.append(") ");
		}
		sb.append("}");
		return sb.toString();
	}
	
	static String printTupleList(List<Entry<Relation, Tuple>> col, boolean b) {
		StringBuilder sb = new StringBuilder("");
		sb.append("[ ");
		for (Entry<Relation, Tuple> t : col) {
			sb.append("( "); 
			sb.append(t.getKey());
			sb.append(printTuple(t.getValue()));
			sb.append(") ");
		}
		sb.append("] ");
		return sb.toString().substring(0,sb.length()-1);
	}
	
	
	static String printTuple(Tuple t) {
		StringBuilder sb = new StringBuilder(" ");
		for (int i = 0; i < t.arity(); i++) {
			sb.append(normRel(t.atom(i).toString()));
			sb.append(" ");
		}
		return sb.toString();
	}
	
	static String printFormula(Formula f) {
		final Formatter formatter = new Formatter(0,80);
		f.accept(formatter);
		return formatter.tokens.toString();
	
	}
		/**
		 * Generates a buffer of tokens comprising the string representation
		 * of a given node.  The buffer contains at least the parentheses 
		 * needed to correctly represent the node's tree structure.
		 * 
		 * @specfield tokens: seq<Object> 
		 * @author Emina Torlak
		 */
	private static class Formatter implements VoidVisitor {
			final StringBuilder tokens ;
			//final int offset;
			private final int lineLength;
			private int indent, lineStart;
			
			/**
			 * Constructs a new tokenizer.
			 * @ensures no this.tokens
			 */
			Formatter(int offset, int line) {
				assert offset >= 0 && offset < line;
				this.tokens = new StringBuilder();
				//this.offset = offset;
				this.lineLength = line;
				this.lineStart = 0;
				this.indent = offset;
				indent();
			}
			
			/*--------------FORMATTERS---------------*/
			
				
			/** @ensures this.tokens' = concat [ this.tokens, " ", token, " " ]*/
			private void infix(Object token) { 
				space();
				tokens.append(token);
				space();
			}
			
			/** @ensures this.tokens' = concat [ this.tokens, token, " " ]*/
			private void keyword(Object token) { 
				append(token);
				space();
			}
			
			/** @ensures this.tokens' = concat [ this.tokens, ", " ]*/
			private void comma() { 
				tokens.append(","); 
				space(); 
			}
			
			/** @ensures this.tokens' = concat [ this.tokens, ": " ]*/
			private void colon() { 
				tokens.append(":"); 
				space(); 
			}
			
			/** @ensures adds this.indent spaces to this.tokens */
			private void indent() { for(int i = 0; i < indent; i++) { space(); } }
			
			/** @ensures adds newline plus this.indent spaces to this.tokens */
			private void newline() { 
				tokens.append("\n");
				lineStart = tokens.length();
				indent();
			}
			
			/** @ensures this.tokens' = concat[ this.tokens,  " " ] **/
			private void space() { tokens.append(" "); }
		
			/** @ensures this.tokens' = concat [ this.tokens, token ]*/
			private void append(Object token) { 
				final String str = String.valueOf(token);
				if ((tokens.length() - lineStart + str.length()) > lineLength) {
					newline();
				}
				tokens.append(str);
			}
			
			/*--------------LEAVES---------------*/
			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(Relation node) { 
				String s = String.valueOf(node);
				append(normRel(s)); 
			}

			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(Variable node) { append(node); }

			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(ConstantExpression node) { append(node); }
			
			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(IntConstant node) { append(node); }
			
			/** @ensures this.tokens' = concat[ this.tokens, node ] */
			public void visit(ConstantFormula node) { append(node); }
			
			/*--------------DECLARATIONS---------------*/
			/** 
			 * @ensures this.tokens' = 
			 *   concat[ this.tokens, tokenize[ node.variable ], ":", tokenize[ node.expression ] 
			 **/
			public void visit(Decl node) {
				node.variable().accept(this);
				colon();
				if (node.multiplicity()!=Multiplicity.ONE) {
					append(node.multiplicity());
					space();
				}
				node.expression().accept(this);
			}
			
			/** 
			 * @ensures this.tokens' = 
			 *   concat[ this.tokens, tokenize[ node.declarations[0] ], ",", 
			 *    ..., tokenize[ node.declarations[ node.size() - 1 ] ] ] 
			 **/
			public void visit(Decls node) {
				Iterator<Decl> decls = node.iterator();
				decls.next().accept(this);
				while(decls.hasNext()) { 
					comma();
					decls.next().accept(this);
				}
			}
			
			/*--------------UNARY NODES---------------*/
			
			/** @ensures this.tokenize' = 
			 *   (parenthesize => concat [ this.tokens, "(", tokenize[child], ")" ] else 
			 *                    concat [ this.tokens, tokenize[child] ]*/
			private void visitChild(Node child, boolean parenthesize) { 
				if (parenthesize) { append("("); }
				child.accept(this);
				if (parenthesize) { append(")"); }
			}
			
			/** @return true if the given expression should be parenthesized when a 
			 * child of a compound parent */
			private boolean parenthesize(Expression child) { 
				return child instanceof BinaryExpression || child instanceof IfExpression; 
			}
			
			/** @return true if the given expression should be parenthesized when a 
			 * child of a compound parent */
			private boolean parenthesize(IntExpression child) { 
				return !(child instanceof UnaryIntExpression || 
						 child instanceof IntConstant || 
						 child instanceof ExprToIntCast); 
			}
			
			/** @return true if the given formula should be parenthesized when a 
			 * child of a compound parent */
			private boolean parenthesize(Formula child) { 
				return !(child instanceof NotFormula || child instanceof ConstantFormula || 
						 child instanceof RelationPredicate);
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			public void visit(UnaryExpression node) { 
				append(node.op());
				visitChild(node.expression(), parenthesize(node.expression()));
			}
			
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's not an instance of unary int expression or int constant. **/
			public void visit(UnaryIntExpression node)  { 
				final IntExpression child = node.intExpr();
				final IntOperator op = node.op();
				final boolean parens = 
					(op==IntOperator.ABS) || (op==IntOperator.SGN) || 
					parenthesize(child);
				append(node.op());
				visitChild(child, parens);
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's not an instance of not formula, constant formula, or 
			 * relation predicate. **/
			public void visit(NotFormula node) {
				append("!");
				final boolean pchild = parenthesize(node.formula());
				indent += pchild ? 2 : 1;
				visitChild(node.formula(), parenthesize(node.formula()));
				indent -= pchild ? 2 : 1;
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			public void visit(MultiplicityFormula node) {
				keyword(node.multiplicity());
				visitChild(node.expression(), parenthesize(node.expression()));
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			// [HASLab]
			public void visit(UnaryTempFormula node) { 
				keyword(node.op());
				indent++;
				visitChild(node.formula(), parenthesize(node.op(), node.formula()));
				indent--;
			}
			
			/** @ensures appends the given op and child to this.tokens; the child is 
			 * parenthesized if it's an instance of binary expression or an if expression. **/
			// [HASLab]
			public void visit(TempExpression node) { 
				visitChild(node.expression(), parenthesize(node.op(), node.expression()));
				keyword(node.op());
			}



			/*--------------BINARY NODES---------------*/
			
			/** @return true if the given  expression needs to be parenthesized if a 
			 * child of a binary  expression with the given operator */
			private boolean parenthesize(ExprOperator op, Expression child) { 
				return child instanceof IfExpression ||
					   child instanceof NaryExpression ||
				       (child instanceof BinaryExpression && 
				        (op==ExprOperator.JOIN || 
				         ((BinaryExpression)child).op()!=op));
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(BinaryExpression node) {
				final ExprOperator op = node.op();
				visitChild(node.left(), parenthesize(op, node.left()));
				infix(op);
				visitChild(node.right(), parenthesize(op, node.right()));
			}
			
			

			/** @return true if the given operator is assocative */
			private boolean associative(IntOperator op) { 
				switch(op) { 
				case DIVIDE : case MODULO : case SHA : case SHL : case SHR : return false;
				default : return true;
				}
			}
			
			/** @return true if the given int expression needs to be parenthesized if a 
			 * child of a binary int expression with the given operator */
			private boolean parenthesize(IntOperator op, IntExpression child) { 
				return child instanceof SumExpression ||
					   child instanceof IfIntExpression || 
					   child instanceof NaryIntExpression ||
				       (child instanceof BinaryIntExpression && 
				        (!associative(op) || ((BinaryIntExpression)child).op()!=op));
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(BinaryIntExpression node) {
				final IntOperator op = node.op();
				visitChild(node.left(), parenthesize(op, node.left()));
				infix(op);
				visitChild(node.right(), parenthesize(op, node.right()));
			}
			
			/** @return true if the given formula needs to be parenthesized if a 
			 * child of a binary formula with the given operator */
			private boolean parenthesize(FormulaOperator op, Formula child) { 
				return child instanceof QuantifiedFormula || 
					   //child instanceof NaryFormula ||
				       (child instanceof BinaryFormula && 
				        (op==FormulaOperator.IMPLIES || 
				         ((BinaryFormula)child).op()!=op));
			}

			/** @return true if the given temporal formula needs to be parenthesized, 
			 * assumed to be always */
			// [HASLab]
			private boolean parenthesize(TemporalOperator op, Formula child) { 
				return true;
			}
			
			/** @return true if the given temporal expression needs to be parenthesized, 
			 * assumed to be always */
			// [HASLab]
			private boolean parenthesize(TemporalOperator op, Expression child) { 
				return true;
			}

			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(BinaryFormula node) {
				final FormulaOperator op = node.op();
				final boolean pleft = parenthesize(op, node.left());
				if (pleft) indent++;
				visitChild(node.left(), pleft);
				if (pleft) indent--;
				if (op == FormulaOperator.AND && indent==0)
					append(";");
				else
					infix(op);
				newline();
				final boolean pright =  parenthesize(op, node.right());
				if (pright) indent++;
				visitChild(node.right(), pright);
				if (pright) indent--;
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, tokenize[node.left], node.op, tokenize[node.right] */
			public void visit(ComparisonFormula node) {
				visitChild(node.left(), parenthesize(node.left()));
				infix(node.op());
				visitChild(node.right(), parenthesize(node.right()));
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, tokenize[node.left], node.op, tokenize[node.right] */
			public void visit(IntComparisonFormula node) {
				visitChild(node.left(), parenthesize(node.left()));
				infix(node.op());
				visitChild(node.right(), parenthesize(node.right()));
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			// [HASLab]
			public void visit(BinaryTempFormula node) {
				final TemporalOperator op = node.op();
				final boolean pleft = parenthesize(op, node.left());
				if (pleft) indent++;
				visitChild(node.left(), pleft);
				if (pleft) indent--;
				infix(op);
				newline();
				final boolean pright =  parenthesize(op, node.right());
				if (pright) indent++;
				visitChild(node.right(), pright);
				if (pright) indent--;
			}
			
			/*--------------TERNARY NODES---------------*/
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(IfExpression node) {
				visitChild(node.condition(), parenthesize(node.condition()));
				infix("=>");
				indent++;
				newline();
				visitChild(node.thenExpr(), parenthesize(node.thenExpr()));
				infix("else");
				newline();
				visitChild(node.elseExpr(), parenthesize(node.elseExpr()));
				indent--;
			}
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(IfIntExpression node) {
				visitChild(node.condition(), parenthesize(node.condition()));
				infix("=>");
				indent++;
				newline();
				visitChild(node.thenExpr(), parenthesize(node.thenExpr()));
				infix("else");
				newline();
				visitChild(node.elseExpr(), parenthesize(node.elseExpr()));
				indent--;
			}
			
			/*--------------VARIABLE CREATOR NODES---------------*/
			/** @ensures this.tokens' = concat[ this.tokens, 
			 *   "{", tokenize[node.decls], "|", tokenize[ node.formula ], "}" ]*/
			public void visit(Comprehension node) {
				append("{");
				node.decls().accept(this);
				infix("|");
				node.formula().accept(this);
				append("}");	
			}
			
			/** @ensures this.tokens' = concat[ this.tokens,  "sum",
			 *   tokenize[node.decls], "|", tokenize[ node.intExpr ],  ]*/
			public void visit(SumExpression node) {
				keyword("sum");
				node.decls().accept(this);
				infix("|");
				node.intExpr().accept(this);
			}
			
			/** @ensures this.tokens' = concat[ this.tokens,  node.quantifier,
			 *   tokenize[node.decls], "|", tokenize[ node.formula ] ]*/
			public void visit(QuantifiedFormula node) {
				keyword(node.quantifier());
				node.decls().accept(this);
				infix("|");
				indent++;
				newline();
				node.formula().accept(this);
				indent--;
			}
			
			/*--------------NARY NODES---------------*/
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(NaryExpression node) {
				final ExprOperator op = node.op();
				visitChild(node.child(0), parenthesize(op, node.child(0)));
				for(int i = 1, size = node.size(); i < size; i++) {
					infix(op);
					visitChild(node.child(i), parenthesize(op, node.child(i)));
				}
			}
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(NaryIntExpression node) {
				final IntOperator op = node.op();
				visitChild(node.child(0), parenthesize(op, node.child(0)));
				for(int i = 1, size = node.size(); i < size; i++) {
					infix(op);
					visitChild(node.child(i), parenthesize(op, node.child(i)));
				}
			}
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(NaryFormula node) {
				final FormulaOperator op = node.op();
				boolean parens = parenthesize(op, node.child(0));
				if (parens) indent++;
				visitChild(node.child(0), parens);
				if (parens) indent--;
				for(int i = 1, size = node.size(); i < size; i++) { 
					if (op == FormulaOperator.AND && indent==0)
						append(";");
					else
						infix(op);
					newline();
					parens = parenthesize(op, node.child(i));
					if (parens) indent++;
					visitChild(node.child(i), parens);
					if (parens) indent--;
				}
			}
			/*--------------OTHER NODES---------------*/
			
			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(ProjectExpression node) {
				append("project");
				append("[");
				node.expression().accept(this);
				comma();
				append("<");
				final Iterator<IntExpression> cols = node.columns();
				cols.next().accept(this);
				while(cols.hasNext()) { 
					comma();
					cols.next().accept(this);
				}
				append(">");
				append("]");
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, "Int","[",
			 *   tokenize[node.intExpr], "]" ] **/
			public void visit(IntToExprCast node) {
				append("Int");
				append("[");
				node.intExpr().accept(this);
				append("]");
			}
			
			/** @ensures this.tokens' = concat[ this.tokens, "int","[",
			 *   tokenize[node.expression], "]" ] **/
			public void visit(ExprToIntCast node) {
				switch(node.op()) { 
				case SUM:
					append("int");
					append("[");
					node.expression().accept(this);
					append("]");
					break;
				case CARDINALITY : 
					append("#");
					append("(");
					node.expression().accept(this);
					append(")");
					break;
				default : throw new IllegalArgumentException("unknown operator: " + node.op());
				}
				
			}

			/** @ensures appends the tokenization of the given node to this.tokens */
			public void visit(RelationPredicate node) {
				switch(node.name()) { 
				case ACYCLIC : 
					append("acyclic");
					append("[");
					node.relation().accept(this);
					append("]");
					break;
				case FUNCTION : 
					visit((QuantifiedFormula) node.toConstraints());
					break;
				case TOTAL_ORDERING : 
					visit((NaryFormula) node.toConstraints());
					break;
				default:
					throw new AssertionError("unreachable");
				}
				
			}
			
		}
	
	private static String normRel(String s) {
		return s.replace("/", "##").replace(".", "#");
	}
	
	//TODO: 
}

