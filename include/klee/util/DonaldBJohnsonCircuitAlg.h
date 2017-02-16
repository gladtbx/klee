#ifndef DONALDBJOHNSONCIRCUIT_H_
#define DONALDBJOHNSONCIRCUIT_H_
#include "klee/util/TarjanSCC.h"
class dbjCircuit{
private:
	int n;//The number of nodes
	std::vector<int> A;
	std::vector<int> B;
	std::vector<bool> blocked;
	int s;
	Graph<errPercNode>* graph;
public:

};

#endif
