//===-- Z3Solver.cpp -------------------------------------------*- C++ -*-====//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/Config/config.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/Internal/Support/FileHandling.h"
#ifdef ENABLE_Z3
#include "Z3Solver.h"
#include "Z3Builder.h"
#include "klee/Constraints.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <chrono>
#include <stdio.h>
#include <string>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#define BUFSIZE (4096)

namespace {
// NOTE: Very useful for debugging Z3 behaviour. These files can be given to
// the z3 binary to replay all Z3 API calls using its `-log` option.
llvm::cl::opt<std::string> Z3LogInteractionFile(
    "debug-z3-log-api-interaction", llvm::cl::init(""),
    llvm::cl::desc("Log API interaction with Z3 to the specified path"));

llvm::cl::opt<std::string> Z3QueryDumpFile(
    "debug-z3-dump-queries", llvm::cl::init(""),
    llvm::cl::desc("Dump Z3's representation of the query to the specified path"));

llvm::cl::opt<bool> Z3ValidateModels(
    "debug-z3-validate-models", llvm::cl::init(false),
    llvm::cl::desc("When generating Z3 models validate these against the query"));

llvm::cl::opt<unsigned>
    Z3VerbosityLevel("debug-z3-verbosity", llvm::cl::init(0),
                     llvm::cl::desc("Z3 verbosity level (default=0)"));
}

#include "llvm/Support/ErrorHandling.h"

namespace klee {

class Z3SolverImpl : public SolverImpl {
private:
  Z3Builder *builder;
  double timeout;
  SolverRunStatus runStatusCode;
  llvm::raw_fd_ostream* dumpedQueriesFile;
  ::Z3_params solverParameters;
  // Parameter symbols
  ::Z3_symbol timeoutParamStrSymbol;
  FILE* timelog;
  long int solvetime = 0;
  long int setuptime = 0;
  long int cachetime = 0;

  bool internalRunSolver(const Query &,
                         const std::vector<const Array *> *objects,
                         std::vector<std::vector<unsigned char> > *values,
                         bool &hasSolution);
bool validateZ3Model(::Z3_solver &theSolver, ::Z3_model &theModel);


	int ccache_socket;
	FILE* cachetimelog;
	long int itotaltime = 0;
	long int istringtime = 0;
	long int cstringtime = 0;
	long int csendtime = 0;
	long int crecvtime = 0;
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
  	server.sin_port        = htons(port);            /* Server port */

  	/* Establish the connection to the echo server */
  	if (connect(ccache_socket, (struct sockaddr *) &server, sizeof(server)) < 0) {
  		report_and_die("connect() failed");
  	}
  	cachetimelog = fopen("/home/gladtbx/Documents/runtimestats/ccachetime","a");
  	if(!timelog){
  		report_and_die("Fopen failed");
  	}
  }

  void shutdown() {
  	if (send(ccache_socket, "CLOSE", 5, 0) != 5) {
  		// do nothing
  	}
  	close(ccache_socket);
  	fprintf(cachetimelog, "%ld, %ld, %ld, %ld, %ld\n",cstringtime,istringtime,csendtime,crecvtime,itotaltime);
  	fclose(cachetimelog);
  	exit(0);
  }

  ::Z3_lbool check_ccache(const char* query,std::vector<std::vector<unsigned char> > *values) {
    	int query_len;
    	int bytes_rcvd;
    	char _result[BUFSIZE];

		std::chrono::high_resolution_clock::time_point s = std::chrono::high_resolution_clock::now();

	    std::string iq = "check ";
	    iq.append(query);

	    query= iq.c_str();
    	query_len = strlen(query);
    	std::chrono::high_resolution_clock::time_point e = std::chrono::high_resolution_clock::now();
    	cstringtime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
    	//printf("Sending query: ");
    	//printf("%s \n",query);
    	s = std::chrono::high_resolution_clock::now();
    	if (send(ccache_socket, query, query_len, 0) != query_len) {
    		report_and_die("send() sent a different number of bytes than expected");
    		return Z3_L_UNDEF;
    	}
    	e = std::chrono::high_resolution_clock::now();
    	csendtime+=(std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
		auto duration = e.time_since_epoch();
		//fprintf(timelog,"Current Time for check: %ld\n",std::chrono::duration_cast<std::chrono::nanoseconds> (duration).count());
    	s = std::chrono::high_resolution_clock::now();

    	if ((bytes_rcvd = recv(ccache_socket, _result, BUFSIZE - 1, 0)) <= 0) {
    		report_and_die("recv() failed or connection closed prematurely");
    		return Z3_L_UNDEF;
    	}
    	e = std::chrono::high_resolution_clock::now();
		duration = e.time_since_epoch();
		//fprintf(timelog,"Current Time for reply: %ld\n",std::chrono::duration_cast<std::chrono::nanoseconds> (duration).count());
    	crecvtime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();

    	_result[bytes_rcvd]=NULL;
    	if(_result[0] == 'T'){//Cache Hit, need parsing
//    		strcpy(result, _result+2);
    		int i = 2;
			std::vector<unsigned char> array;
    		while(i < bytes_rcvd){
    			if(_result[i]=='|'){//Dangerous, fixme
    				values->push_back(array);
    				array.clear();
    				i++;
    				continue;
    			}
    			array.push_back(_result[i]);
    			i++;
    		}
    		if(array.size()){
    			values->push_back(array);
    		}
    		return Z3_L_TRUE;
    	}else if(_result[0] == 'F'){
        	return Z3_L_FALSE;
    	}
    	return Z3_L_UNDEF;
    }

  void cacheInsert(const char* _query, ::Z3_lbool res ,std::vector<std::vector<unsigned char> > *values){
		std::chrono::high_resolution_clock::time_point s = std::chrono::high_resolution_clock::now();

		/*
		* Send the result to the server and cache it.
		*/
		//printf("Inserting query result for %s\n",_query);
		int size = values->size();
	    std::string iq = "insert";
		iq+=" " + std::to_string(strlen(_query)) + " ";
		if(res==Z3_L_TRUE){
			iq+= 'T';
		}else{
			iq+= 'F';
		}
		iq+=' ';
		for(std::vector<std::vector<unsigned char> >::iterator it = values->begin(); it != values->end(); it++){
	    	iq.append(it->begin(),it->end());
	    	iq+='|';
	    }
	    iq.append(_query);

		const char* query= iq.c_str();
		int query_len = iq.size();
		std::chrono::high_resolution_clock::time_point e = std::chrono::high_resolution_clock::now();
		istringtime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
    	//printf("Inserting query: ");
    	//printf("%s \n",query);
		s = std::chrono::high_resolution_clock::now();

    	if (send(ccache_socket, query, query_len, 0) != query_len) {
    		report_and_die("send() sent a different number of bytes than expected");
    		return ;
    	}

		e = std::chrono::high_resolution_clock::now();
		itotaltime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
		char ack[4];
	      	if ((recv(ccache_socket, ack, 3, 0)) <= 0) {
	      		report_and_die("recv() failed or connection closed prematurely");
    			return;
    		}

		return;
  }

public:
  Z3SolverImpl();
  ~Z3SolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(double _timeout) {
    assert(_timeout >= 0.0 && "timeout must be >= 0");
    timeout = _timeout;

    unsigned int timeoutInMilliSeconds = (unsigned int)((timeout * 1000) + 0.5);
    if (timeoutInMilliSeconds == 0)
      timeoutInMilliSeconds = UINT_MAX;
    Z3_params_set_uint(builder->ctx, solverParameters, timeoutParamStrSymbol,
                       timeoutInMilliSeconds);
  }

  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution);
  SolverRunStatus
  handleSolverResponse(::Z3_solver theSolver, ::Z3_lbool satisfiable,
                       const std::vector<const Array *> *objects,
                       std::vector<std::vector<unsigned char> > *values,
                       bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
};

Z3SolverImpl::Z3SolverImpl()
    : builder(new Z3Builder(
          /*autoClearConstructCache=*/false,
          /*z3LogInteractionFileArg=*/Z3LogInteractionFile.size() > 0
              ? Z3LogInteractionFile.c_str()
              : NULL)),
      timeout(0.0), runStatusCode(SOLVER_RUN_STATUS_FAILURE),
      dumpedQueriesFile(0) {
  assert(builder && "unable to create Z3Builder");
  solverParameters = Z3_mk_params(builder->ctx);
  Z3_params_inc_ref(builder->ctx, solverParameters);
  timeoutParamStrSymbol = Z3_mk_string_symbol(builder->ctx, "timeout");
  setCoreSolverTimeout(timeout);
  timelog = fopen("/home/gladtbx/Documents/runtimestats/z3time","a");


  if (!Z3QueryDumpFile.empty()) {
    std::string error;
    dumpedQueriesFile = klee_open_output_file(Z3QueryDumpFile, error);
    if (!error.empty()) {
      klee_error("Error creating file for dumping Z3 queries: %s",
                 error.c_str());
    }
    klee_message("Dumping Z3 queries to \"%s\"", Z3QueryDumpFile.c_str());
  }

  // Set verbosity
  if (Z3VerbosityLevel > 0) {
    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    ss << Z3VerbosityLevel;
    ss.flush();
    Z3_global_param_set("verbose", underlyingString.c_str());
  }
  initialize(9407);
}

Z3SolverImpl::~Z3SolverImpl() {
  Z3_params_dec_ref(builder->ctx, solverParameters);
  delete builder;
  fprintf(timelog, "%ld, %ld, %ld\n",setuptime,solvetime,cachetime);
  fclose(timelog);
  if (dumpedQueriesFile) {
    dumpedQueriesFile->close();
    delete dumpedQueriesFile;
  }
	shutdown();
}

Z3Solver::Z3Solver() : Solver(new Z3SolverImpl()) {}

char *Z3Solver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void Z3Solver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}

char *Z3SolverImpl::getConstraintLog(const Query &query) {
  std::vector<Z3ASTHandle> assumptions;
  // We use a different builder here because we don't want to interfere
  // with the solver's builder because it may change the solver builder's
  // cache.
  // NOTE: The builder does not set `z3LogInteractionFile` to avoid conflicting
  // with whatever the solver's builder is set to do.
  Z3Builder temp_builder(/*autoClearConstructCache=*/false,
                         /*z3LogInteractionFile=*/NULL);

  for (std::vector<ref<Expr> >::const_iterator it = query.constraints.begin(),
                                               ie = query.constraints.end();
       it != ie; ++it) {
    assumptions.push_back(temp_builder.construct(*it));
  }
  ::Z3_ast *assumptionsArray = NULL;
  int numAssumptions = query.constraints.size();
  if (numAssumptions) {
    assumptionsArray = (::Z3_ast *)malloc(sizeof(::Z3_ast) * numAssumptions);
    for (int index = 0; index < numAssumptions; ++index) {
      assumptionsArray[index] = (::Z3_ast)assumptions[index];
    }
  }

  // KLEE Queries are validity queries i.e.
  // ∀ X Constraints(X) → query(X)
  // but Z3 works in terms of satisfiability so instead we ask the
  // the negation of the equivalent i.e.
  // ∃ X Constraints(X) ∧ ¬ query(X)
  Z3ASTHandle formula = Z3ASTHandle(
      Z3_mk_not(temp_builder.ctx, temp_builder.construct(query.expr)),
      temp_builder.ctx);

  ::Z3_string result = Z3_benchmark_to_smtlib_string(
      temp_builder.ctx,
      /*name=*/"Emited by klee::Z3SolverImpl::getConstraintLog()",
      /*logic=*/"",
      /*status=*/"unknown",
      /*attributes=*/"",
      /*num_assumptions=*/numAssumptions,
      /*assumptions=*/assumptionsArray,
      /*formula=*/formula);

  if (numAssumptions)
    free(assumptionsArray);

  // We need to trigger a dereference before the `temp_builder` gets destroyed.
  // We do this indirectly by emptying `assumptions` and assigning to
  // `formula`.
  assumptions.clear();
  formula = Z3ASTHandle(NULL, temp_builder.ctx);
  // Client is responsible for freeing the returned C-string
  return strdup(result);
}

bool Z3SolverImpl::computeTruth(const Query &query, bool &isValid) {
  bool hasSolution;
  bool status =
      internalRunSolver(query, /*objects=*/NULL, /*values=*/NULL, hasSolution);
  isValid = !hasSolution;
  return status;
}

bool Z3SolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  // Find the object used in the expression, and compute an assignment
  // for them.
  findSymbolicObjects(query.expr, objects);
  if (!computeInitialValues(query.withFalse(), objects, values, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  Assignment a(objects, values);
  result = a.evaluate(query.expr);

  return true;
}

bool Z3SolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  return internalRunSolver(query, &objects, &values, hasSolution);
}

bool Z3SolverImpl::internalRunSolver(
    const Query &query, const std::vector<const Array *> *objects,
    std::vector<std::vector<unsigned char> > *values, bool &hasSolution) {

  TimerStatIncrementer t(stats::queryTime);
  // NOTE: Z3 will switch to using a slower solver internally if push/pop are
  // used so for now it is likely that creating a new solver each time is the
  // right way to go until Z3 changes its behaviour.
  //
  // TODO: Investigate using a custom tactic as described in
  // https://github.com/klee/klee/issues/653
  Z3_solver theSolver = Z3_mk_solver(builder->ctx);
  Z3_solver_inc_ref(builder->ctx, theSolver);
  Z3_solver_set_params(builder->ctx, theSolver, solverParameters);

  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  for (ConstraintManager::const_iterator it = query.constraints.begin(),
                                         ie = query.constraints.end();
       it != ie; ++it) {
    Z3_solver_assert(builder->ctx, theSolver, builder->construct(*it));
  }
  ++stats::queries;
  if (objects)
    ++stats::queryCounterexamples;

  std::chrono::high_resolution_clock::time_point s = std::chrono::high_resolution_clock::now();

  Z3ASTHandle z3QueryExpr =
      Z3ASTHandle(builder->construct(query.expr), builder->ctx);

	std::chrono::high_resolution_clock::time_point e = std::chrono::high_resolution_clock::now();
	setuptime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();


	s = std::chrono::high_resolution_clock::now();

	// KLEE Queries are validity queries i.e.
  // ∀ X Constraints(X) → query(X)
  // but Z3 works in terms of satisfiability so instead we ask the
  // negation of the equivalent i.e.
  // ∃ X Constraints(X) ∧ ¬ query(X)
  Z3_solver_assert(
      builder->ctx, theSolver,
      Z3ASTHandle(Z3_mk_not(builder->ctx, z3QueryExpr), builder->ctx));
  e = std::chrono::high_resolution_clock::now();
  setuptime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();

	s = std::chrono::high_resolution_clock::now();

	const char* z3solver = Z3_solver_to_string(builder->ctx,theSolver);
//	fprintf(timelog,"%s\n",z3solver);
	::Z3_lbool cacheResult = check_ccache(z3solver,values);
	if(cacheResult != Z3_L_UNDEF){
		if(cacheResult == Z3_L_FALSE || objects->size()==0 || (objects->size() == values->size())){
			if(cacheResult == Z3_L_TRUE){
				hasSolution = true;
				runStatusCode= SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
			    ++stats::queriesInvalid;
			}else{
				hasSolution = false;
				runStatusCode = SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
			    ++stats::queriesValid;
			}
			e = std::chrono::high_resolution_clock::now();
		  	cachetime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
		    Z3_solver_dec_ref(builder->ctx, theSolver);
		    builder->clearConstructCache();
		    return true;
		}
	}
	e = std::chrono::high_resolution_clock::now();
  	cachetime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
  if (dumpedQueriesFile) {
    *dumpedQueriesFile << "; start Z3 query\n";
    *dumpedQueriesFile << Z3_solver_to_string(builder->ctx, theSolver);
    *dumpedQueriesFile << "(check-sat)\n";
    *dumpedQueriesFile << "(reset)\n";
    *dumpedQueriesFile << "; end Z3 query\n\n";
    dumpedQueriesFile->flush();
  }
	s = std::chrono::high_resolution_clock::now();

  ::Z3_lbool satisfiable = Z3_solver_check(builder->ctx, theSolver);

  runStatusCode = handleSolverResponse(theSolver, satisfiable, objects, values,
                                       hasSolution);
  e = std::chrono::high_resolution_clock::now();
  solvetime += (std::chrono::duration_cast<std::chrono::nanoseconds> (e-s)).count();
  //fprintf(timelog, "%ld, %ld, %ld\n",setuptime,solvetime,cachetime);

  //Update the cache here
  if(satisfiable != Z3_L_UNDEF){
	  cacheInsert(z3solver,satisfiable,values);
  }

  Z3_solver_dec_ref(builder->ctx, theSolver);
  // Clear the builder's cache to prevent memory usage exploding.
  // By using ``autoClearConstructCache=false`` and clearning now
  // we allow Z3_ast expressions to be shared from an entire
  // ``Query`` rather than only sharing within a single call to
  // ``builder->construct()``.
  builder->clearConstructCache();

  if (runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE ||
      runStatusCode == SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE) {
    if (hasSolution) {
      ++stats::queriesInvalid;
    } else {
      ++stats::queriesValid;
    }
    return true; // success
  }
  return false; // failed
}

SolverImpl::SolverRunStatus Z3SolverImpl::handleSolverResponse(
    ::Z3_solver theSolver, ::Z3_lbool satisfiable,
    const std::vector<const Array *> *objects,
    std::vector<std::vector<unsigned char> > *values, bool &hasSolution) {
  switch (satisfiable) {
  case Z3_L_TRUE: {
    hasSolution = true;
    if (!objects) {
      // No assignment is needed
      assert(values == NULL);
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    }
    assert(values && "values cannot be nullptr");
    ::Z3_model theModel = Z3_solver_get_model(builder->ctx, theSolver);
    assert(theModel && "Failed to retrieve model");
    Z3_model_inc_ref(builder->ctx, theModel);
    values->reserve(objects->size());
    for (std::vector<const Array *>::const_iterator it = objects->begin(),
                                                    ie = objects->end();
         it != ie; ++it) {
      const Array *array = *it;
      std::vector<unsigned char> data;

      data.reserve(array->size);
      for (unsigned offset = 0; offset < array->size; offset++) {
        // We can't use Z3ASTHandle here so have to do ref counting manually
        ::Z3_ast arrayElementExpr;
        Z3ASTHandle initial_read = builder->getInitialRead(array, offset);

        bool successfulEval =
            Z3_model_eval(builder->ctx, theModel, initial_read,
                          /*model_completion=*/Z3_TRUE, &arrayElementExpr);
        assert(successfulEval && "Failed to evaluate model");
        Z3_inc_ref(builder->ctx, arrayElementExpr);
        assert(Z3_get_ast_kind(builder->ctx, arrayElementExpr) ==
                   Z3_NUMERAL_AST &&
               "Evaluated expression has wrong sort");

        int arrayElementValue = 0;
        bool successGet = Z3_get_numeral_int(builder->ctx, arrayElementExpr,
                                             &arrayElementValue);
        assert(successGet && "failed to get value back");
        assert(arrayElementValue >= 0 && arrayElementValue <= 255 &&
               "Integer from model is out of range");
        data.push_back(arrayElementValue);
        Z3_dec_ref(builder->ctx, arrayElementExpr);
      }
      values->push_back(data);
    }

    // Validate the model if requested
    if (Z3ValidateModels) {
      bool success = validateZ3Model(theSolver, theModel);
      if (!success)
        abort();
    }

    Z3_model_dec_ref(builder->ctx, theModel);
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  }
  case Z3_L_FALSE:
    hasSolution = false;
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  case Z3_L_UNDEF: {
    ::Z3_string reason =
        ::Z3_solver_get_reason_unknown(builder->ctx, theSolver);
    if (strcmp(reason, "timeout") == 0 || strcmp(reason, "canceled") == 0 ||
        strcmp(reason, "(resource limits reached)") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
    }
    if (strcmp(reason, "unknown") == 0) {
      return SolverImpl::SOLVER_RUN_STATUS_FAILURE;
    }
    klee_warning("Unexpected solver failure. Reason is \"%s,\"\n", reason);
    abort();
  }
  default:
    llvm_unreachable("unhandled Z3 result");
  }
}

bool Z3SolverImpl::validateZ3Model(::Z3_solver &theSolver, ::Z3_model &theModel) {
  bool success = true;
  ::Z3_ast_vector constraints =
      Z3_solver_get_assertions(builder->ctx, theSolver);
  Z3_ast_vector_inc_ref(builder->ctx, constraints);

  unsigned size = Z3_ast_vector_size(builder->ctx, constraints);

  for (unsigned index = 0; index < size; ++index) {
    Z3ASTHandle constraint = Z3ASTHandle(
        Z3_ast_vector_get(builder->ctx, constraints, index), builder->ctx);

    ::Z3_ast rawEvaluatedExpr;
    bool successfulEval =
        Z3_model_eval(builder->ctx, theModel, constraint,
                      /*model_completion=*/Z3_TRUE, &rawEvaluatedExpr);
    assert(successfulEval && "Failed to evaluate model");

    // Use handle to do ref-counting.
    Z3ASTHandle evaluatedExpr(rawEvaluatedExpr, builder->ctx);

    Z3SortHandle sort =
        Z3SortHandle(Z3_get_sort(builder->ctx, evaluatedExpr), builder->ctx);
    assert(Z3_get_sort_kind(builder->ctx, sort) == Z3_BOOL_SORT &&
           "Evaluated expression has wrong sort");

    Z3_lbool evaluatedValue =
        Z3_get_bool_value(builder->ctx, evaluatedExpr);
    if (evaluatedValue != Z3_L_TRUE) {
      llvm::errs() << "Validating model failed:\n"
                   << "The expression:\n";
      constraint.dump();
      llvm::errs() << "evaluated to \n";
      evaluatedExpr.dump();
      llvm::errs() << "But should be true\n";
      success = false;
    }
  }

  if (!success) {
    llvm::errs() << "Solver state:\n" << Z3_solver_to_string(builder->ctx, theSolver) << "\n";
    llvm::errs() << "Model:\n" << Z3_model_to_string(builder->ctx, theModel) << "\n";
  }

  Z3_ast_vector_dec_ref(builder->ctx, constraints);
  return success;
}

SolverImpl::SolverRunStatus Z3SolverImpl::getOperationStatusCode() {
  return runStatusCode;
}
}
#endif // ENABLE_Z3
