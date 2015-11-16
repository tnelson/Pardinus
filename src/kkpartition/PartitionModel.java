package kkpartition;

import kodkod.ast.Formula;
import kodkod.instance.Bounds;

public interface PartitionModel {

	public Bounds bounds1();
	public Bounds bounds2();
	public Formula partition1();
	public Formula partition2();
	public int getBitwidth();
	
}
