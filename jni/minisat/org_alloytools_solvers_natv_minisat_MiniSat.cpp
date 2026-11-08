#include <jni.h>

#include "minisat/minisat/core/Solver.h"

using namespace Minisat;

/*
 * Class:     org_alloytools_solvers_natv_minisat_MiniSat
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_org_alloytools_solvers_natv_minisat_MiniSat_make
  (JNIEnv *, jclass) {
  Solver* solver = new Solver();
  return ((jlong) solver);
}

/*
 * Class:     org_alloytools_solvers_natv_minisat_MiniSat
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_org_alloytools_solvers_natv_minisat_MiniSat_free
  (JNIEnv *, jobject, jlong solver) {
  delete ((Solver*)solver);
}

/*
 * Class:     org_alloytools_solvers_natv_minisat_MiniSat
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_org_alloytools_solvers_natv_minisat_MiniSat_addVariables
  (JNIEnv *, jobject, jlong solver, jint  numVars) {
  Solver* solverPtr = (Solver*) solver;
  for(int i = 0; i < numVars; ++i) {
     solverPtr->newVar();
  }
}

/*
 * Class:     org_alloytools_solvers_natv_minisat_MiniSat
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_org_alloytools_solvers_natv_minisat_MiniSat_addClause
  (JNIEnv * env, jobject, jlong solver, jintArray clause) {
    jsize length = env->GetArrayLength(clause);
    jint* buf = env->GetIntArrayElements(clause, JNI_FALSE);
    Solver* solverPtr = ((Solver*)solver);
    vec<Lit> lits;
    for(int i = 0; i < length; ++i) {
        int var = *(buf+i);
        lits.push((var > 0) ?  mkLit(var-1) : ~mkLit(-var-1));
    }
    solverPtr->addClause(lits);
    env->ReleaseIntArrayElements(clause, buf, 0);
    return solverPtr->okay();
 }

/*
 * Class:     org_alloytools_solvers_natv_minisat_MiniSat
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_org_alloytools_solvers_natv_minisat_MiniSat_solve
  (JNIEnv *, jobject, jlong solver) {
   return ((Solver*)solver)->solve();
  }

/*
 * Class:     org_alloytools_solvers_natv_minisat_MiniSat
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_org_alloytools_solvers_natv_minisat_MiniSat_valueOf
  (JNIEnv *, jobject, jlong solver, jint var) {
  return ((Solver*)solver)->model[var-1]==l_True;
 }
