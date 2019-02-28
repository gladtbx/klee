#include "klee/Config/config.h"
#include "klee/Solver.h"
#include "klee/util/ExprSMTLIBPrinter.h"
#include "klee/SolverImpl.h"
#include "klee/IncompleteSolver.h"
#include "klee/SolverStats.h"


#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <chrono>
#include <stdio.h>
#include <string>

#define BUFSIZE (4096)

using namespace klee;

class CcacheSolver : public SolverImpl {
private:
	  int ccache_socket;
	  FILE* timelog;
	  long int totaltime = 0;
	  Solver *solver;
	  ExprSMTLIBPrinter printer;


	  void report_and_die(char* message) {
	  	fprintf(stderr, "ERROR: %s\n", message);
	  	//exit(-1);
	  }
	  void initialize(int port) {
	    	struct sockaddr_in server;       /* Green server address */

	    	/* Create a reliable, stream socket using TCP */
	    	if ((ccache_socket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP)) < 0) {
	    		report_and_die("socket() failed");
	    	}

	    	/* Construct the server address structure */
	    	memset(&server, 0, sizeof(server));              /* Zero out structure */
	    	server.sin_family      = AF_INET;                /* Internet address family */
	    	server.sin_addr.s_addr = inet_addr("127.0.0.1"); /* Server IP address */
	    	server.sin_port        = port;            /* Server port */

	    	/* Establish the connection to the echo server */
	    	if (connect(ccache_socket, (struct sockaddr *) &server, sizeof(server)) < 0) {
	    		report_and_die("connect() failed");
	    	}
	    	timelog = fopen("/home/gladtbx/Documents/runtimestats/ccachetime","a");
	    	if(!timelog){
	    		report_and_die("Fopen failed");
	    	}
	    }

	    void shutdown() {
	    	if (send(ccache_socket, "CLOSE", 5, 0) != 5) {
	    		// do nothing
	    	}
	    	close(ccache_socket);
	    	fprintf(timelog, "%ld\n",totaltime);
	    	fclose(timelog);
	    	exit(0);
	    }

	      ref<Expr> canonicalizeQuery(ref<Expr> originalQuery,
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

	    bool check_ccache(const Query& _query, char* result, bool& negationUsed) {
	      	int query_len;
	      	int bytes_rcvd;
	      	char _result[BUFSIZE];

	        //bool negationUsed;
	        ref<Expr> canonicalQuery = canonicalizeQuery(_query.expr, negationUsed);

	        std::string BufferString;
	    	llvm::raw_string_ostream queryBuffer(BufferString);
	    	printer.setOutput(queryBuffer);
	    	printer.setQuery(Query(_query.constraints,canonicalQuery));
    	    printer.generateOutput();

    	    const char* query= ("check "+BufferString).c_str();
	      	query_len = strlen(query);
	      	printf("Sending query: ");
	      	printf("%s \n",query);
	      	std::chrono::high_resolution_clock::time_point s = std::chrono::high_resolution_clock::now();
	      	if (send(ccache_socket, query, query_len, 0) != query_len) {
	      		report_and_die("send() sent a different number of bytes than expected");
	      		return false;
	      	}

	      	if ((bytes_rcvd = recv(ccache_socket, _result, BUFSIZE - 1, 0)) <= 0) {
	      		report_and_die("recv() failed or connection closed prematurely");
	      		return false;
	      	}
	      	std::chrono::high_resolution_clock::time_point e = std::chrono::high_resolution_clock::now();
	      	totaltime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();

	      	result[bytes_rcvd]=NULL;
	      	if(result[0] == 'G'){//Cache Hit
	      		strcpy(result, _result+2);
	      		return true;
	      	}
	      	return false;
	      }

	    void cacheInsert(const Query& _query, IncompleteSolver::PartialValidity result){
			bool negationUsed;
			std::chrono::high_resolution_clock::time_point s = std::chrono::high_resolution_clock::now();

			ref<Expr> canonicalQuery = canonicalizeQuery(_query.expr, negationUsed);
			IncompleteSolver::PartialValidity cachedResult =
			  (negationUsed ? IncompleteSolver::negatePartialValidity(result) : result);
			int cR = cachedResult + 2;
			std::ostringstream temp;
			temp << (cR);
			/*
			* Send the result to the server and cache it.
			*/
			std::string BufferString;
			llvm::raw_string_ostream queryBuffer(BufferString);
			printer.setOutput(queryBuffer);
	    	printer.setQuery(Query(_query.constraints,canonicalQuery));
    	    printer.generateOutput();

			const char* query= ("insert "+ temp.str() +" "+BufferString).c_str();
			int query_len = strlen(query);
	      	printf("Inserting query: ");
	      	printf("%s \n",query);

	      	if (send(ccache_socket, query, query_len, 0) != query_len) {
	      		report_and_die("send() sent a different number of bytes than expected");
	      		return ;
	      	}

			std::chrono::high_resolution_clock::time_point e = std::chrono::high_resolution_clock::now();
			totaltime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
			return;
	    }

	      IncompleteSolver::PartialValidity parseValidity(char* c, bool ne){
	    	  switch(*c){
	    	  case '0':
	    		  return (ne)? IncompleteSolver::MayBeTrue : IncompleteSolver::MayBeFalse;
	    	  case '1':
	    		  return (ne) ? IncompleteSolver::MustBeTrue : IncompleteSolver::MustBeFalse;
	    	  case '2':
	    		  return IncompleteSolver::TrueOrFalse;
	    	  case '3':
	    		  return (ne) ? IncompleteSolver::MustBeFalse : IncompleteSolver::MustBeTrue;
	    	  case '4':
	    		  return (ne) ? IncompleteSolver::MayBeFalse : IncompleteSolver::MayBeTrue;
	    	  default:
	    		  assert(0 && "unreachable");
	    		  break;
	    	  }
	    	  return IncompleteSolver::None;
	      }

	    public:
	      CcacheSolver(Solver *s);
	      ~CcacheSolver();

	      char *getConstraintLog(const Query &);
	      void setCoreSolverTimeout(double timeout) {
	        solver->impl->setCoreSolverTimeout(timeout);
	      }
	      bool computeValidity(const Query&, Solver::Validity &result);
	      bool computeTruth(const Query &, bool &isValid);
	      bool computeValue(const Query & query, ref<Expr> &result){
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
};

CcacheSolver::CcacheSolver(Solver *s) :solver(s){
	initialize(9407);
}

CcacheSolver::~CcacheSolver(){
	shutdown();
}

char *CcacheSolver::getConstraintLog(const Query &query) {
  return solver->impl->getConstraintLog(query);
}

bool CcacheSolver::computeValidity(const Query& query,
                                    Solver::Validity &result) {
  IncompleteSolver::PartialValidity cachedResult;
  char charresult[2];
  bool negationUsed;
  bool tmp, cacheHit = check_ccache(query, charresult,negationUsed);

  if (cacheHit) {
	cachedResult = parseValidity(charresult,negationUsed);
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

bool CcacheSolver::computeTruth(const Query& query,
                                 bool &isValid) {
  IncompleteSolver::PartialValidity cachedResult;
  char charresult[2];
  bool negationUsed;
  bool cacheHit = check_ccache(query, charresult,negationUsed);
  if(cacheHit){
	  cachedResult = parseValidity(charresult,negationUsed);
  }


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


SolverImpl::SolverRunStatus CcacheSolver::getOperationStatusCode() {
	  return solver->impl->getOperationStatusCode();
}

///

Solver *klee::createCCacheSolver(Solver *s){
	//return new Solver(new CachingSolver(_solver));
	//Need to implement a new layer here that contacts the outside cache.

	return new Solver(new CcacheSolver(s));
}
