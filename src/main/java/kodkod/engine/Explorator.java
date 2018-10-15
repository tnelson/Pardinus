package kodkod.engine;

import java.util.Iterator;

import kodkod.ast.Formula;

public interface Explorator<T> extends Iterator<T> {
	public void extend(Formula form);
}
