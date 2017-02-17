#ifndef DONALDBJOHNSONCIRCUIT_H_
#define DONALDBJOHNSONCIRCUIT_H_
#include "klee/util/TarjanSCC.h"
class dbjCircuit{
private:
	int n;//The number of nodes
	std::vector<std::pair<int, errPercNode*> > A;
	std::vector<int> B;
	std::vector<bool> blocked;
	std::stack<int> stack;
	int s;
	Graph<errPercNode>* graph;
	errPercNode* root;
	dbjCircuit():n(0),s(0),graph(NULL),root(NULL){

	}

	void clear(){
		A.clear();
		B.clear();
		blocked.clear();
		while(stack.size()){
			stack.pop();
		}
		s = 0;
	}
public:
	dbjCircuit(int _n, errPercNode* _root):n(_n),s(0),root(_root){
		graph = new Graph<errPercNode>(n,root);
		graph->init();
	}

	void genCircuit(){
		clear();
		s = 1;
		while (s < n){
			graph->SCC(s);
			std::vector<std::set<std::pair<int,errPercNode*> > > partition = graph->getPartition();
			for(std::vector<std::set<std::pair<int,errPercNode*> > >::iterator i = partition.begin(); i != partition.end(); i++){
				for(std::set<std::pair<int,errPercNode*> >::iterator j = i->begin(); j != i->end(); j++ ){

				}
			}
		}
	}

};

#endif
