#ifndef TARJANSCC_H_
#define TARJANSCC_H_
#include "klee/util/errPercNode.h"
#include <list>
#include <stack>
#include <set>
#include <vector>

/*
 * The Tarjan's algorithm finds all the strongly connected components of a directed graph.
 * It is then used by Johnson's algorithm to find all circuits.
 * Each circuit is a potential loop for the program.
 * The loop info is then used to reduce the path info, as well as reduce the execution space we need to explore.
 * Usage: after constructing, use init to initialize the DG.
 * Before each calculation of new partition, use clearPartition to clear out the labels, and then use SCC() to calculate
 * new partation.
 */
template<class DAT>
class Graph
{
private:
	DAT* root;
	int	V;//number of vertices.
	DAT** nodes;//list of errPercNodes
	DAT* nil;
	int *disc;
	int *low;
	bool *stackMember;
	std::stack<int> *st;
	std::vector<std::set<std::pair<int,DAT*> > > partition;
	int time;
	int current_s;


	int min(int a, int b){
		return (a < b)? a : b;
	}

	void SCCUtil(int u){
		disc[u] = low[u] = ++time;
		st->push(u);
		stackMember[u] = true;
		typename std::vector<DAT*>::const_iterator i;
		for(i = nodes[u]->getSuccessor().begin();i != nodes[u]->getSuccessor().end(); ++i){
			int v = (*i)->get_tarjanid();
			if(disc[v] == -1){
				SCCUtil(v);
				low[u] = min(low[u],low[v]);
			}
			else if(stackMember[v] == true){
				low[u] = min(low[u],disc[v]);
			}
		}
		int w = 0;
		std::set<std::pair<int,DAT*> > scc_set;
		if( low[u] == disc[u]){
			while(st->top()!= u){
				w = (int) st->top();
				//Save SCC here
				scc_set.insert(std::make_pair(w,nodes[w]));
				stackMember[w] = false;
				st->pop();
			}
			w = (int) st->top();
			//Save the last node of SCC here
			scc_set.insert(std::make_pair(w,nodes[w]));
			stackMember[w] = false;
			st->pop();
			partition.push_back(scc_set);
		}
	}


public:
	Graph(int _V, DAT* _root):root(_root),V(_V),
	nil(NULL),disc(NULL),low(NULL),stackMember(new bool[V]),
	st(new std::stack<int>()),time(0),current_s(-1){
		nodes = (DAT**) malloc(V*sizeof(DAT*));
		disc = (int*) malloc(V*sizeof(int));
		low = (int*) malloc(V*sizeof(int));
		for(int i = 0; i < V; i++){
			disc[i] = -1;
			low[i] = -1;
			stackMember[i] = false;
			nodes[i] = NULL;
		}
	}

	~Graph(){
		free(nodes);
		free(disc);
		free(low);
		free(stackMember);
		free(st);
	}

	void init(){
		std::stack<DAT*> worklist;
		std::vector<bool> pushed(V);
		pushed[0] = true;
		for(int i = 1; i < V; i++){
			pushed[i] = false;
		}
		worklist.push(root);
		while(!worklist.empty()){
			DAT* current = worklist.top();
			worklist.pop();
			int tarjanid = current->get_tarjanid();
			nodes[tarjanid] = current;
			std::vector<DAT*> succ = current->getSuccessor();
			for(typename std::vector<DAT*>::const_iterator i = succ.begin(); i != succ.end(); i++){
				if(!pushed[(*i)->get_tarjanid()]){
					pushed[(*i)->get_tarjanid()] = true;
					worklist.push(*i);
				}
			}
			std::vector<DAT*> fcalls = current->getFcall();
			for(typename std::vector<DAT*>::const_iterator i = fcalls.begin(); i != fcalls.end(); i++){
				if(!pushed[(*i)->get_tarjanid()]){
					pushed[(*i)->get_tarjanid()] = true;
					worklist.push(*i);
				}
			}
		}
	}

	void SCC(){
		time = 0;
		current_s = 0;
		for(int i = 0; i < V; i++){
			if(disc[i] == -1){
				SCCUtil(i);
			}
		}
		return;
	}

	void SCC(int u){
		time = 0;
		current_s = u;
		for(int i = 0; i < V; i++){
			if(i < u){
				disc[i] = 1;
				continue;
			}
			if(disc[i] == -1){
				SCCUtil(i);
			}
		}
		return;
	}

	int get_current_s(){
		return current_s;
	}

	void clearPartition(){
		for(typename std::vector<std::set<std::pair<int,DAT*> > >::iterator i = partition.begin(); i != partition.end(); i++){
			i->clear();
		}
		for(int i = 0; i < V; i++){
			disc[i] = -1;
			low[i] = -1;
			stackMember[i] = false;
			nodes[i] = NULL;
		}
	}

	std::vector<std::set<std::pair<int,DAT*> > >& getPartition(){
		return partition;
	}
};
#endif
