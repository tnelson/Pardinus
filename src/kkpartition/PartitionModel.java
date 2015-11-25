package kkpartition;

import kodkod.ast.Formula;
import kodkod.instance.Bounds;

public interface PartitionModel {

	/**
	 * Bounds of the first partition.
	 * @return
	 */
	public Bounds bounds1();

	/**
	 * Bounds of the second partition.
	 * @requires bounds1().relations() & bounds2.requires() = empty
	 * @return
	 */
	public Bounds bounds2();

	/**
	 * Formula for the first partition. Formula must refer to every relation in bounds1().
 	 * @requires partition1().relations() = bounds1().relations()
	 * @return
	 */
	public Formula partition1();
	
	/**
	 * Formula for the second partition.
	 * @return
	 */
	public Formula partition2();

	/**
	 * The bits required to encode the model.
 	 * @requires partition2().relations() in bounds1().relations() + bounds2().relations() 
	 * @return
	 */
	public int getBitwidth();
	
}
