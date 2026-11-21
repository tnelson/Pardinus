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
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine.fol2sat;

import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryFormula;
import kodkod.ast.Expression;
import kodkod.ast.Node;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.Quantifier;
import kodkod.engine.bool.BooleanMatrix;
import kodkod.util.collections.IdentityHashSet;
import kodkod.util.nodes.AnnotatedNode;


/**
 * Manages the caching policy for a translation from FOL to boolean.  
 * In particular it determines which translations
 * to cache, when to throw them out of the cache, etc. 
 * 
 * @specfield node: Node // node being translated
 * @specfield cached: node.*children  // the nodes whose translations are cached
 * @specfield cache: cached -> (Object ->lone Environment)
 * @author Emina Torlak
 */
final class FOL2BoolCache {
	private final Map<Node,Record> cache;
	// Used if overflow-prevention is enabled. If so, caching needs to be polarity-aware.
	private final Map<Node,Record> negatedCache;
	private final Translation.CacheStats stats;

	/**
	 * Constructs a new translation cache for the given annotated node.
	 * @ensures this.node' = annotated.node
	 */
	FOL2BoolCache(AnnotatedNode<? extends Node> annotated, boolean overflowPrevention, Translation.CacheStats stats, int recordLimit) {
		this.stats = stats;
		final CacheCollector collector = new CacheCollector(
				overflowPrevention ? new IdentityHashSet<Node>(annotated.sharedNodes()) : annotated.sharedNodes(),
				overflowPrevention);
		annotated.node().accept(collector);

		this.cache = new IdentityHashMap<Node, Record>(collector.cache().size());
		this.negatedCache = overflowPrevention ? new IdentityHashMap<Node, Record>(collector.cache().size()) : this.cache;
		for(Map.Entry<Node, Set<Variable>> e :  collector.cache().entrySet()) {
			Set<Variable> freeVars = e.getValue();
			if (freeVars.isEmpty())
				this.cache.put(e.getKey(), new NoVarRecord());
			else
				this.cache.put(e.getKey(), new MultiVarRecord(freeVars, overflowPrevention, recordLimit));
			if (overflowPrevention)
				this.negatedCache.put(e.getKey(), freeVars.isEmpty() ? new NoVarRecord() : new MultiVarRecord(freeVars, overflowPrevention, recordLimit));
		}
	}

	
	/**
	 * If the translation of the given node, with its free variables
	 * bound as they are in the given environment, has been cached, 
	 * the cached value is returned.  Otherwise, null is returned.
	 * @return this.cache[node][Object] in env.map =>
	 *         this.cache[node].map, null
	 */
	@SuppressWarnings("unchecked")
	<T> T lookup(Node node, Environment<BooleanMatrix, Expression> env) { // [AM]
		final Record info = (env.isNegated() ? negatedCache : cache).get(node);
		final T ret = info==null ? null : (T) info.get(env);
		if (ret != null) stats.hits++;
		return ret;
	}
	
	/**
	 * Caches the given translation for the specified node, if the given node is
	 * in this.cached.  Otherwise does nothing.  
	 * The method returns the specified translation. 
	 * @ensures node in this.cached => 
	 *           this.cache' = this.cache ++ node->translation->env, 
	 *           this.cache' = this.cache
	 * @return translation
	 */
	final <T> T cache(Node node, T translation, Environment<BooleanMatrix, Expression> env) { // [AM]
		final Record info = (env.isNegated() ? negatedCache : cache).get(node);
		if (info != null) {
			final int before = info.size();
			info.set(translation, env);
			stats.recordResized(before, info.size());
		}
		return translation;
	}
		
	/**
	 * Collects the free variables of the nodes in a given AST whose
	 * translations should be cached.
	 * @specfield root: Node
	 * @specfield cached: root.*children -> Set<Variable>
	 * @invariant all c: root.*children | some cached[c] => cached[c] = freeVariables(c)
	 * @author Emina Torlak
	 */
	private static final class CacheCollector extends FreeVariableCollector {

		private final boolean cacheIffOperands;

		/**
		 * Constructs a new cache collector.
		 */
		protected CacheCollector(Set<Node> cached, boolean cacheIffOperands) {
			super(cached);
			this.cacheIffOperands = cacheIffOperands;
		}

		// If overflow-prevention is enabled, IFF desugars to a conjunction of implications. Because 
		// those translations happen differently for both polarities, we need the cache in the negative 
		// case as well to avoid blowup on chained IFF. 
		@Override
		public Set<Variable> visit(BinaryFormula binFormula) {
			if (cacheIffOperands && binFormula.op() == FormulaOperator.IFF) {
				cached.add(binFormula.left());
				cached.add(binFormula.right());
			}
			return super.visit(binFormula);
		}

		/**
		 * Returns this.cache.  This method should be called *after* the
		 * visitor has been applied to this.root.
		 * @return this.cache
		 */
		final Map<Node,Set<Variable>> cache() {
			return cache;
		}
		
		/**
		 * TN: before changing this for Forge, the following sentences were true: 
		 * "We record the set of free variables for the given node if the node is shared,
		 * or if it has free variables, none of which is the most recently declared variable."
		 * 
		 * This method is a pre-walk before translation happens; it records which nodes are 
		 * assigned a cache record: the free-variable sets become eventual keys. The goal is 
		 * for a cached node's translation to be used for bindings to variables it does not 
		 * mention. For example, for subformulas of F in {@code all x: A | all y: B | all z: C | F}:
		 *   P(x)        is translated once per x. 
		 *   P(y)        is translated once per y. 
		 *   P(z)        is translated once per z. 
		 *   P(x, z)     is translated once per (x, z).
		 *   P(x, y, z)  isn't cached, because all variables are mentioned.
		 *
		 * @ensures node in sharedNodes ||
		 *          ((node.^(~children) in (QuantifiedFormula + Comprehension)) &&
		 *           (some v: varsInScope | !freeVars.contains(v))) =>
		 *            this.cache' = this.cache ++ node->freeVars,
		 *            this.cache' = this.cache
		 * @return freeVars
		 */
		@Override
		protected final Set<Variable> cache(Node node, Set<Variable> freeVars) {
			boolean cacheIt = cached.contains(node);
			for (Variable v : varsInScope)
				cacheIt = cacheIt || !freeVars.contains(v);
			if (cacheIt) {
				cache.put(node, reduce(freeVars));
			}
			return freeVars;
		}
		
	}
	
	/**
	 * A container class that stores the translation of a shared node
	 * (BooleanValue for formulas and BooleanMatrix for expressions)
	 * and bindings for the node's free variables which were used to 
	 * generate the translation.
	 * Storing the bindings is necessary for proper handling of 
	 * sharing within quantified formulas and comprehensions.
	 * This implementation assumes that each free variable is 
	 * mapped to a BooleanMatrix of density one, whose sole entry
	 * is the BooleanConstant TRUE.
	 * @specfield varBinding: Variable -> lone int
	 * @specfield translation: lone Object
	 */
	private static abstract class Record {
		Object translation;
		/**
		 * Returns this.translation if the given environment
		 * has the same mappings for the free variables of 
		 * the translated node as the ones used to generate
		 * this.translation.  Otherwise returns null.  
		 * @requires all v: varBinding.int | some e.lookup(v)
		 * @return all v: varBinding.int | e.lookup(v).get(varBinding[v])=TRUE => this.translation, null
		 * @throws NullPointerException  e = null
		 */
		abstract Object get(Environment<BooleanMatrix, Expression> e);  // [AM]
		
		/**
		 * Sets this.translation to the given translation
		 * and sets the free variable bindings to those 
		 * given by the specified environment.
		 * @requires all v: varBinding.int | some env.lookup(v)
		 * @ensures this.translation' = translation && 
		 *          this.varBinding' = 
		 *           {v: this.varBinding.int, tupleIndex: int | 
		 *             tupleIndex = env.lookup(v).iterator().next().index() }
		 */
		abstract void set(Object transl, Environment<BooleanMatrix, Expression> env);  // [AM]

		/** How many instantiated translations are held by this record */
		abstract int size();
	}
	
	/**
	 * A TranslationInfo for a node with one or more free variables. 
	 * 
	 * Keep translations per *tuple of free-variable bindings*. The cache is cleared when
	 * it fills up. 
	 */
	private static final class MultiVarRecord extends Record {
		final int recordLimit; 
		final boolean withKinds; // used if overflow prevention is on
		final Variable[] vars;
		final Map<List<Integer>, Object> translations = new HashMap<List<Integer>, Object>();
		
		/**
		 * Constructs a translation unit for a node which
		 * has the given set of free variables.
		 * @ensures this.freeVariables' = vars &&
		 *          no this.translation' 
		 */
		MultiVarRecord(Set<Variable> freeVariables, boolean withKinds, int recordLimit) {
			this.vars = freeVariables.toArray(new Variable[freeVariables.size()]);
			this.withKinds = withKinds;
			this.recordLimit = recordLimit;
		}
		
		/**
		 * The cache key is a list of current values for all of this node's free variables. 
		 * If overflow prevention is enabled, also store a bit flag in each cache component 
		 * that indicates whether the variable is quantified some/all.
		 * 
		 * E.g. for P(x, z), when {x = a0, z = c1}, the key is [a0, c1].
		 */
		private List<Integer> key(Environment<BooleanMatrix, Expression> env) {
			final Integer[] tuples = new Integer[vars.length];
			for(int i = 0; i < vars.length; i++) {
				tuples[i] = env.lookup(vars[i]).iterator().next().index();
				if (withKinds) tuples[i] = 2 * tuples[i] + (enteredAsAll(env, vars[i]) ? 1 : 0);
			}
			return Arrays.asList(tuples);
		}
		
		/** 
		 * Was v's quantifier "all"? This matters for overflow prevention, because then 
		   polarity needs to be tracked by the cache. 
		 */
		private static boolean enteredAsAll(Environment<BooleanMatrix, Expression> env, Variable v) {
			while (!env.isEmpty() && env.variable() != v) env = env.parent();
			return env.envType() == Quantifier.ALL;
		}
		
		/**
		 * @see kodkod.engine.fol2sat.FOL2BoolCache.Record#get(kodkod.engine.fol2sat.Environment)
		 */
		Object get(Environment<BooleanMatrix, Expression> e) {  // [AM]
			return translations.isEmpty() ? null : translations.get(key(e));
		}
		
		/**
		 * @see kodkod.engine.fol2sat.FOL2BoolCache.Record#set(java.lang.Object, kodkod.engine.fol2sat.Environment)
		 */
		void set(Object transl, Environment<BooleanMatrix, Expression> env) {  // [AM]
			// Recall that this object is specialized to one node. 
			// Moreover, transl is of type BooleanValue | BooleanMatrix | Int. 
			// BooleanMatrix is mutable, and in practice is mutated only for env.lookup(v) 
			// for some variable v as Pardinus walks over all possible atoms that could 
			// be bound to v.
			
			// Store transl as this node's translation for the values of its free variables
			// under env. If transl is the exact BooleanMatrix for some variable, we make 
			// a copy to freeze the value due to the mutation above. 
			Object stored = transl;
			for (Variable v : vars) {
				// env.lookup(v) returns a BooleanMatrix 
				if (transl == env.lookup(v)) {
					stored = ((BooleanMatrix) transl).clone();
					break;
				}
			}
			if (translations.size() >= recordLimit) {
				translations.clear();
			}
			translations.put(key(env), stored);
		}

		
		int size() { return translations.size(); }
		
		/**
		 * @see java.lang.Object#toString()
		 */
		public String toString() {
			return Arrays.toString(vars) + translations;
		}
	}
	
	/**
	 * A TranslationInfo for a node with no free variables. 
	 */
	private static final class NoVarRecord extends Record {
		
		/**
		 * @see kodkod.engine.fol2sat.FOL2BoolCache.Record#get(kodkod.engine.fol2sat.Environment)
		 */
		Object get(Environment<BooleanMatrix, Expression> e) {  // [AM]
			return translation;
		}
		
		/**
		 * @see kodkod.engine.fol2sat.FOL2BoolCache.Record#set(java.lang.Object, kodkod.engine.fol2sat.Environment)
		 */
		void set(Object transl, Environment<BooleanMatrix, Expression> env) {  // [AM]
			translation = transl;
		}
		
		int size() { return translation == null ? 0 : 1; }
		
		/**
		 * @see java.lang.Object#toString()
		 */
		public String toString() {
			return "{" + translation+ "}";
		}
	}
}
