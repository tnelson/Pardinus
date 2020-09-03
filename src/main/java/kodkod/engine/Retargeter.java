package kodkod.engine;

import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.TargetOptions;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.satlab.TargetSATSolver;

/**
 * Describes a re-targeting strategy.
 * This exposes the TargetSATSolver, Translation, etc. to
 * enable maximum flexibility for the caller.
 */
public interface Retargeter {
    void retarget(TargetSATSolver tcnf, ExtendedOptions opts, Translation transl);
}
