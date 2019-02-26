//===-- CachingSolver.cpp - Caching expression solver ---------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//


#include "klee/Solver.h"

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/IncompleteSolver.h"
#include "klee/SolverImpl.h"

#include "klee/SolverStats.h"
#include "llvm/Support/Casting.h"

#include <ciso646>
#ifdef _LIBCPP_VERSION
#include <unordered_map>
#define unordered_map std::unordered_map
#else
#include <tr1/unordered_map>
#define unordered_map std::tr1::unordered_map
#endif

using namespace klee;

class CachingSolver : public SolverImpl {
private:
  ref<Expr> canonicalizeQuery(ref<Expr> originalQuery,
                              bool &negationUsed);

  void cacheInsert(const Query& query,
                   IncompleteSolver::PartialValidity result);

  bool cacheLookup(const Query& query,
                   IncompleteSolver::PartialValidity &result);
  
  bool checkCacheHit(ref<Expr> q);

  struct CacheEntry {
    CacheEntry(const ConstraintManager &c, ref<Expr> q)
      : constraints(c), query(q) {}

    CacheEntry(const CacheEntry &ce)
      : constraints(ce.constraints), query(ce.query) {}
    
    ConstraintManager constraints;
    ref<Expr> query;

    bool operator==(const CacheEntry &b) const {
      return constraints==b.constraints && *query.get()==*b.query.get();
    }
  };
  
  struct CacheEntryHash {
    unsigned operator()(const CacheEntry &ce) const {
      unsigned result = ce.query->hash();
      
      for (ConstraintManager::constraint_iterator it = ce.constraints.begin();
           it != ce.constraints.end(); ++it)
        result ^= (*it)->hash();
      
      return result;
    }
  };

  typedef unordered_map<CacheEntry, 
                        IncompleteSolver::PartialValidity, 
                        CacheEntryHash> cache_map;
  
  Solver *solver;
  cache_map cache;

  std::set<ref<Expr> > cachedConstraints;
  FILE* timelog;
  long totaltime;


public:
  CachingSolver(Solver *s, std::set<ref<Expr> > _cachedConstraints) : solver(s), cachedConstraints(_cachedConstraints),totaltime(0) {
		 timelog = fopen("/home/gladtbx/Documents/runtimestats/CachingSolvertime","a");
		 if(!timelog){
		  	assert(0 && "Fopen for caching solver log failed");
		 }
  }
  ~CachingSolver() { cache.clear(); delete solver; }

  bool computeValidity(const Query&, Solver::Validity &result);
  bool computeTruth(const Query&, bool &isValid);
  bool computeValue(const Query& query, ref<Expr> &result) {
    ++stats::queryCacheMisses;
    return solver->impl->computeValue(query, result);
  }
  bool computeInitialValues(const Query& query,
                            const std::vector<const Array*> &objects,
                            std::vector< std::vector<unsigned char> > &values,
                            bool &hasSolution) {
    ++stats::queryCacheMisses;
    return solver->impl->computeInitialValues(query, objects, values, 
                                              hasSolution);
  }
  SolverRunStatus getOperationStatusCode();
  char *getConstraintLog(const Query&);
  void setCoreSolverTimeout(double timeout);
};

/** @returns the canonical version of the given query.  The reference
    negationUsed is set to true if the original query was negated in
    the canonicalization process. */
ref<Expr> CachingSolver::canonicalizeQuery(ref<Expr> originalQuery,
                                           bool &negationUsed) {
  ref<Expr> negatedQuery = Expr::createIsZero(originalQuery);

  // select the "smaller" query to the be canonical representation
  if (originalQuery.compare(negatedQuery) < 0) {
    negationUsed = false;
    return originalQuery;
  } else {
    negationUsed = true;
    return negatedQuery;
  }
}

bool compareExpr(ref<Expr> l, ref<Expr> r){
	Expr::Kind lk = l->getKind();
	Expr::Kind rk = r->getKind();
	if(lk != rk){
		return false;
	}
	if(lk == Expr::Constant){
		const ConstantExpr *rl = llvm::dyn_cast<ConstantExpr>(l);
		const ConstantExpr *rr = llvm::dyn_cast<ConstantExpr>(r);
		return (llvm::APInt::isSameValue(rl->getAPValue(),rr->getAPValue()));
	}
	if(lk == Expr::Read){
		const ReadExpr *rl = llvm::dyn_cast<ReadExpr>(l);
		const ReadExpr *rr = llvm::dyn_cast<ReadExpr>(r);
		if(rl->updates.root->name == rr->updates.root->name){
			return compareExpr(rl->index, rr->index);
		}
	}
	int numKids = l->getNumKids();
	for(int i = 0; i < numKids; i++){
		if(!compareExpr(l->getKid(i), r->getKid(i))){
			return false;
		}
	}
	return true;
}

bool CachingSolver::checkCacheHit(ref<Expr> q){
	printf("Checking if cache hit for: \n");
	q->dump();
	for(std::set<ref<Expr> >::iterator it = cachedConstraints.begin(), itEnd =cachedConstraints.end();
		it != itEnd; it++){
		printf("Constraints now:\n");
		(*it)->dump();
		if(compareExpr(*it,q)){
			return true;
		}
	}
	return false;
}

/** @returns true on a cache hit, false of a cache miss.  Reference
    value result only valid on a cache hit. */
bool CachingSolver::cacheLookup(const Query& query,
                                IncompleteSolver::PartialValidity &result) {
  std::chrono::high_resolution_clock::time_point s = std::chrono::high_resolution_clock::now();

  bool negationUsed;
  ref<Expr> canonicalQuery = canonicalizeQuery(query.expr, negationUsed);

  //Check if Gladtbx implemented cache is a hit
//  if(checkCacheHit(canonicalQuery)){
//	  ++stats::cachedConstraintsHit;
//	  return true;
//  }

  CacheEntry ce(query.constraints, canonicalQuery);
  //Gladtbx: Cached query are checked with strict equality
  //Is it really necessary?
  //If we can do check each ref<Expr> of the constraints with the one in cache
  //We should be able to improve hit rate?
  //We have to make sure the cache entries are True.
  cache_map::iterator it = cache.find(ce);
  std::chrono::high_resolution_clock::time_point e = std::chrono::high_resolution_clock::now();
  totaltime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
  if (it != cache.end()) {
    result = (negationUsed ?
              IncompleteSolver::negatePartialValidity(it->second) :
              it->second);
    return true;
  }
  
  return false;
}

/// Inserts the given query, result pair into the cache.
void CachingSolver::cacheInsert(const Query& query,
                                IncompleteSolver::PartialValidity result) {
  bool negationUsed;
  std::chrono::high_resolution_clock::time_point s = std::chrono::high_resolution_clock::now();

  ref<Expr> canonicalQuery = canonicalizeQuery(query.expr, negationUsed);

  CacheEntry ce(query.constraints, canonicalQuery);
  IncompleteSolver::PartialValidity cachedResult = 
    (negationUsed ? IncompleteSolver::negatePartialValidity(result) : result);
  
  cache.insert(std::make_pair(ce, cachedResult));
  std::chrono::high_resolution_clock::time_point e = std::chrono::high_resolution_clock::now();
  totaltime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
}

bool CachingSolver::computeValidity(const Query& query,
                                    Solver::Validity &result) {
  IncompleteSolver::PartialValidity cachedResult;
  bool tmp, cacheHit = cacheLookup(query, cachedResult);
  
  if (cacheHit) {
    switch(cachedResult) {
    case IncompleteSolver::MustBeTrue:   
      result = Solver::True;
      ++stats::queryCacheHits;
      return true;
    case IncompleteSolver::MustBeFalse:  
      result = Solver::False;
      ++stats::queryCacheHits;
      return true;
    case IncompleteSolver::TrueOrFalse:  
      result = Solver::Unknown;
      ++stats::queryCacheHits;
      return true;
    case IncompleteSolver::MayBeTrue: {
      ++stats::queryCacheMisses;
      if (!solver->impl->computeTruth(query, tmp))
        return false;
      if (tmp) {
        cacheInsert(query, IncompleteSolver::MustBeTrue);
        result = Solver::True;
        return true;
      } else {
        cacheInsert(query, IncompleteSolver::TrueOrFalse);
        result = Solver::Unknown;
        return true;
      }
    }
    case IncompleteSolver::MayBeFalse: {
      ++stats::queryCacheMisses;
      if (!solver->impl->computeTruth(query.negateExpr(), tmp))
        return false;
      if (tmp) {
        cacheInsert(query, IncompleteSolver::MustBeFalse);
        result = Solver::False;
        return true;
      } else {
        cacheInsert(query, IncompleteSolver::TrueOrFalse);
        result = Solver::Unknown;
        return true;
      }
    }
    default: assert(0 && "unreachable");
    }
  }

  ++stats::queryCacheMisses;
  
  if (!solver->impl->computeValidity(query, result))
    return false;

  switch (result) {
  case Solver::True: 
    cachedResult = IncompleteSolver::MustBeTrue; break;
  case Solver::False: 
    cachedResult = IncompleteSolver::MustBeFalse; break;
  default: 
    cachedResult = IncompleteSolver::TrueOrFalse; break;
  }
  
  cacheInsert(query, cachedResult);
  return true;
}

bool CachingSolver::computeTruth(const Query& query,
                                 bool &isValid) {
  IncompleteSolver::PartialValidity cachedResult;
  bool cacheHit = cacheLookup(query, cachedResult);

  // a cached result of MayBeTrue forces us to check whether
  // a False assignment exists.
  if (cacheHit && cachedResult != IncompleteSolver::MayBeTrue) {
    ++stats::queryCacheHits;
    isValid = (cachedResult == IncompleteSolver::MustBeTrue);
    return true;
  }

  ++stats::queryCacheMisses;
  
  // cache miss: query solver
  if (!solver->impl->computeTruth(query, isValid))
    return false;

  if (isValid) {
    cachedResult = IncompleteSolver::MustBeTrue;
  } else if (cacheHit) {
    // We know a true assignment exists, and query isn't valid, so
    // must be TrueOrFalse.
    assert(cachedResult == IncompleteSolver::MayBeTrue);
    cachedResult = IncompleteSolver::TrueOrFalse;
  } else {
    cachedResult = IncompleteSolver::MayBeFalse;
  }
  
  cacheInsert(query, cachedResult);
  return true;
}

SolverImpl::SolverRunStatus CachingSolver::getOperationStatusCode() {
  return solver->impl->getOperationStatusCode();
}

char *CachingSolver::getConstraintLog(const Query& query) {
  return solver->impl->getConstraintLog(query);
}

void CachingSolver::setCoreSolverTimeout(double timeout) {
  solver->impl->setCoreSolverTimeout(timeout);
}

///

Solver *klee::createCachingSolver(Solver *_solver, std::set<ref<Expr> > cachedConstraints) {
  return new Solver(new CachingSolver(_solver, cachedConstraints));
}
