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
#ifdef ENABLE_GREEN
#include "Z3Builder.h"
#include "klee/Constraints.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"
#include "klee/util/ExprSMTLIBPrinter.h"

#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>

#define GREEN_BUFSIZE (4096)

namespace klee {

class GreenSolverImpl : public SolverImpl {
private:
  double timeout;
  SolverRunStatus runStatusCode;
  // Parameter symbols

  ExprSMTLIBPrinter printer;

  bool internalRunSolver(const Query &,
                         const std::vector<const Array *> *objects,
                         std::vector<std::vector<unsigned char> > *values,
                         bool &hasSolution);

  int green_socket;

  /**
   * Error reporting routine.
   */

  void report_and_die(char* message) {
  	fprintf(stderr, "ERROR: %s\n", message);
  	//exit(-1);
  }

  /**
   * Initialize the Green client.  This amounts to connecting to the server.  If
   * the parameter is the server port.  For now we assume that the server is
   * running on the local machine, but this might change in the future.
   */

  void green_initialize(int port) {
  	struct sockaddr_in server;       /* Green server address */

  	/* Create a reliable, stream socket using TCP */
  	if ((green_socket = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP)) < 0) {
  		report_and_die("socket() failed");
  	}

  	/* Construct the server address structure */
  	memset(&server, 0, sizeof(server));              /* Zero out structure */
  	server.sin_family      = AF_INET;                /* Internet address family */
  	server.sin_addr.s_addr = inet_addr("127.0.0.1"); /* Server IP address */
  	server.sin_port        = htons(port);            /* Server port */

  	/* Establish the connection to the echo server */
  	if (connect(green_socket, (struct sockaddr *) &server, sizeof(server)) < 0) {
  		report_and_die("connect() failed");
  	}
  }

  void green_shutdown() {
  	if (send(green_socket, "CLOSE", 5, 0) != 5) {
  		// do nothing
  	}
  	close(green_socket);
  	exit(0);
  }

  int green_issat(const char* query, char* result) {
  	int query_len;
  	int bytes_rcvd;

  	query_len = strlen(query);
  	printf("Sending query: ");
  	printf("%s \n",query);

  	if (send(green_socket, query, query_len, 0) != query_len) {
  		report_and_die("send() sent a different number of bytes than expected");
  		return 1;
  	}

  	if ((bytes_rcvd = recv(green_socket, result, GREEN_BUFSIZE - 1, 0)) <= 0) {
  		report_and_die("recv() failed or connection closed prematurely");
  		return 2;
  	}
  	result[bytes_rcvd]=NULL;
  	return 0;
  }

  int parseResponse(const char* response,const std::vector<const Array *> *objects,
          std::vector<std::vector<unsigned char> > *values );

public:
  GreenSolverImpl();
  ~GreenSolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(double _timeout) {
    assert(_timeout >= 0.0 && "timeout must be >= 0");
    /*Gladtbx We can't set timeout here for Green*/

  }

  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution);
  SolverRunStatus getOperationStatusCode();
};

GreenSolver::GreenSolver() :Solver(new GreenSolverImpl()){
}

GreenSolverImpl::GreenSolverImpl()
    :timeout(0.0),
      runStatusCode(SOLVER_RUN_STATUS_FAILURE) {
	green_initialize(9408);
  	setCoreSolverTimeout(timeout);
}

GreenSolverImpl::~GreenSolverImpl(){
	green_shutdown();
}

char *GreenSolver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void GreenSolver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}

char * GreenSolverImpl::getConstraintLog(const Query &query) {
	return 0;
}

bool GreenSolverImpl::computeTruth(const Query &query, bool &isValid){
	  bool hasSolution;
	  bool status =
	      internalRunSolver(query, /*objects=*/NULL, /*values=*/NULL, hasSolution);
	  isValid = !hasSolution;
	  return status;
}

bool GreenSolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  return internalRunSolver(query, &objects, &values, hasSolution);
}

bool GreenSolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  // Find the object used in the expression, and compute an assignment
  // for them.
  /* Gladtbx: I don't want to run findSymbolicObjects because Green will do it for us
   * However I have to because we might miss some objs if we rely on Green.*/
  findSymbolicObjects(query.expr, objects);
  if (!internalRunSolver(query.withFalse(), &objects, &values, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  Assignment a(objects, values);
  result = a.evaluate(query.expr);

  return true;
}

bool GreenSolverImpl::internalRunSolver(
    const Query &query, const std::vector<const Array *> *objects,
    std::vector<std::vector<unsigned char> > *values, bool &hasSolution) {
/*
 * Need to talk to Green via socket, send request and get the result back
 * Need to set the runStatusCode as well. Seems it is not currently implemented
 */
	/*
	 * Need to print the query as a string, using some sstream.
	 */
  	char recv[GREEN_BUFSIZE];
  	std::string BufferString;
	llvm::raw_string_ostream queryBuffer(BufferString);
	printer.setOutput(queryBuffer);
	printer.setQuery(query);
    printer.generateOutput();
	printf("$s\n",BufferString.c_str());
	int retVal = green_issat(queryBuffer.str().c_str(),recv);
	if(retVal != 0){
		runStatusCode = SOLVER_RUN_STATUS_FAILURE;
		hasSolution = false;
		return false;
	}
	//If the received message is 0, it means not sat.
	if(recv[0] == '0'){
		runStatusCode = SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
		hasSolution= false;
		return true;
	}
	if(!objects){
		runStatusCode = SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
		hasSolution= true;
		return true;
	}
	retVal = parseResponse(recv, objects, values);
	if(retVal != 0){
		hasSolution = false;
		runStatusCode = SOLVER_RUN_STATUS_FAILURE;
		return false;
	}
	runStatusCode = SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
	hasSolution= true;
	return true;
}

int GreenSolverImpl::parseResponse(const char* response,const std::vector<const Array *> *objects,
        std::vector<std::vector<unsigned char> > *values ){
	if(response[0] != '1'){
		printf("Error, response is unsolveable\n");
		printf("%s\n",response);
		return 1;
	}
	printf("Getting response from Green Solver:\n");
	printf("%s\n",response);
	std::stringstream mappingStream(&response[2]);
	std::map<std::string, std::vector<unsigned char> > pValues;
	std::string objName;
	std::string vals;
	while(mappingStream >> objName){
		if(!(mappingStream >> vals)){
			printf("ERROR: Not getting assigned value from Green Solver\n");
			return 1;
		}
		printf("vals: %s\n", vals.c_str());
		std::stringstream valsStream(vals);
		std::string valInt;
		std::vector<unsigned char> data;
		while(std::getline(valsStream,valInt,'|')){
			//Here the valInt is the integer value of the byte
			int val = std::atoi(valInt.c_str());
			assert(val >= 0 && val <= 255 &&
			               "Integer from model is out of range");
			data.push_back(val);
		}
		pValues.insert(std::pair<std::string, std::vector<unsigned char> >(objName,data));
	}
	for(std::vector<const Array*>::const_iterator it = objects->begin(), itEnd = objects->end();
			it != itEnd; it++){
		std::string objName = (*it)->getName();
		std::map<std::string, std::vector<unsigned char> >::iterator targetIt = pValues.find(objName);
		if(targetIt == pValues.end()){
			printf("ERROR: Var name not found for Green Solver\n");
			return 1;
		}
		int objsize=(*it)->size;
		int valsize=targetIt->second.size();
		if(objsize>valsize){
			printf("ERROR: Var size smaller than required for Green Solver\n");
			return 1;
		}
		if(objsize<valsize){
			printf("Warning: Var size greater than required for Green Solver, required size: %d, val size: %d \n",objsize, valsize);
			targetIt->second.resize(objsize);
		}
		values->push_back(targetIt->second);
	}
	return 0;
}

SolverImpl::SolverRunStatus GreenSolverImpl::getOperationStatusCode() {
  return runStatusCode;
}

}

/* Need to implement all the above functions.*/
#endif
