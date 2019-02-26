#include "klee/Solver.h"
using namespace klee;
///

Solver *klee::createCCacheSolver(Solver *s){
	//return new Solver(new CachingSolver(_solver));
	//Need to implement a new layer here that contacts the outside cache.
	return s;
}
