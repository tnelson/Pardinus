package kodkod.instance;

import java.util.HashMap;
import java.util.Map;

import kodkod.ast.Relation;

public class RelativeBounds extends Bounds {

	private Map<Relation,Relation[]> lowers = new HashMap<Relation,Relation[]>();
	private Map<Relation,Relation[]> uppers = new HashMap<Relation,Relation[]>();
	
	public RelativeBounds(Universe universe) {
		super(universe);
	}
	
	public void bound(Relation relation, Relation[] upper) {
		lowers.put(relation, null);
		uppers.put(relation, upper);
		TupleSet aux = super.upperBound(upper[0]);
		for (int i = 1; i < upper.length; i++)
			aux = aux.product(super.upperBound(upper[i]));
		super.bound(relation, aux);
	}

	public void boundExactly(Relation relation, Relation[] upper) {
		lowers.put(relation, upper);
		uppers.put(relation, upper);
		TupleSet aux = super.upperBound(upper[0]);
		for (int i = 1; i < upper.length; i++)
			aux = aux.product(super.upperBound(upper[i]));
		super.boundExactly(relation, aux);	
		}
	
	public void bound(Relation relation, Relation[] lower, Relation[] upper) {
		lowers.put(relation, lower);
		uppers.put(relation, upper);
		TupleSet aux1 = super.upperBound(lower[0]);
		TupleSet aux2 = super.upperBound(upper[0]);
		for (int i = 1; i < upper.length; i++) {
			aux1 = aux1.product(super.lowerBound(lower[i])); 
			aux2 = aux2.product(super.upperBound(upper[i])); 
		}
		super.bound(relation, aux1, aux2);	
	}

	public void resolve() {
		for (Relation r : lowers.keySet()) {
			TupleSet aux1;
			TupleSet aux2;
			if (lowers.get(r) == null || lowers.get(r).length == 0)
				aux1 = universe().factory().noneOf(r.arity());
			else {
				aux1 = super.lowerBound(lowers.get(r)[0]);
				for (int i = 1; i < lowers.get(r).length; i++)
					aux1 = aux1.product(super.lowerBound(lowers.get(r)[i]));
			}
			
			if (uppers.get(r) == null || uppers.get(r).length == 0)
				aux2 = universe().factory().noneOf(r.arity());
			else {
				aux2 = super.lowerBound(uppers.get(r)[0]);
				for (int i = 1; i < uppers.get(r).length; i++)
					aux2 = aux2.product(super.upperBound(uppers.get(r)[i]));
			}
			
			super.bound(r, aux1, aux2);
		}
	}

}
