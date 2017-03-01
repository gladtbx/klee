#ifndef DONALDBJOHNSONCIRCUIT_H_
#define DONALDBJOHNSONCIRCUIT_H_
#include "klee/util/TarjanSCC.h"

template <class DAT>
class dbjCircuit{
private:
	int n;//The number of nodes
	std::set<std::pair<int, DAT*> > A;
	std::vector<std::set<int> > B;
	std::vector<bool> blocked;
	std::list<int> stack;
	int s;
	Graph<DAT>* graph;
	DAT* root;
	std::vector<std::vector<int> > cycles;
	dbjCircuit():n(0),s(0),graph(NULL),root(NULL){

	}

	void clear(){
		A.clear();
		B.clear();
		blocked.clear();
		stack.clear();
		s = 0;
		cycles.clear();
	}

	void Unblock(int u){
		blocked[u] = false;
		for(std::set<int>::iterator i = B[u].begin() ; i != B[u].end() ; i++ ){
			if(blocked[*i]){
				Unblock(*i);
			}
		}
		B[u].clear();
	}

	bool Circuit(int v){
		bool f=false;
		stack.push_back(v);
		blocked[v]=true;
		std::pair<int, DAT*> Akv;
		for(typename std::set<std::pair<int,DAT*> >::iterator i = A.begin(); i != A.end(); i++){
			if(i->first == v){//finding Ak[v]
				Akv = *i;
				for(typename std::vector<DAT*>::const_iterator j = i->second->getSuccessor().begin(); j != i->second->getSuccessor().end() ; j++ ){
				//for w in Ak(v)
					int w = (*j)->get_tarjanid();
					if(A.find(std::make_pair(w,(*j))) != A.end()){
						if(w == s){//if w == s then
							std::vector<int> cycle;
							for(std::list<int>::iterator k = stack.begin(); k != stack.end(); k++){
								cycle.push_back(*k);
							}
							cycle.push_back(w);
							cycles.push_back(cycle);
							f=true;
						}else if (!blocked[w]){
							if(Circuit(w)){
								f=true;
							}
						}
					}
				}
				break;
			}
		}
		if(f){
			Unblock(v);
		}
		else{
			for(typename std::vector<DAT*>::const_iterator i=Akv.second->getSuccessor().begin();i != Akv.second->getSuccessor().end();i++){
				int w = (*i)->get_tarjanid();
				B[w].insert(v);
			}
		}
		stack.remove(v);
		return f;
	}
public:
	dbjCircuit(int _n, DAT* _root):n(_n),B(std::vector<std::set<int> >(_n)),blocked(std::vector<bool>(_n)),s(0),root(_root){
		graph = new Graph<DAT>(n,root);
		graph->init();
	}

	void genCircuit(){
		clear();
		s = 1;
		while (s < n){
			graph->clearPartition();
			graph->SCC(s);
			//graph->print();
			// Get the partition
			typename std::vector<std::set<std::pair<int,DAT*> > > partition = graph->getPartition();
			// Find the partition with the smallest vertex s.
			typename std::vector<std::set<std::pair<int,DAT*> > >::iterator Ak;
			int least_index = n;
			for(typename std::vector<std::set<std::pair<int,DAT*> > >::iterator i = partition.begin(); i != partition.end(); i++){
				for(typename std::set<std::pair<int,DAT*> >::iterator j = i->begin(); j != i->end(); j++ ){
					if(j->first == s){//If we find s, it is the smallest so we stop loop
						Ak=i;
						least_index = s;
						break;
					}
					if(j->first < least_index){
						least_index = j->first;
						Ak = i;
					}
				}
				if(least_index==s){
					break;
				}
			}
			A=*Ak;
			if(A.size()){
				s = least_index;
				for(typename std::set<std::pair<int,DAT*> >::iterator i = A.begin(); i != A.end(); i++){
					blocked[i->first] = false;
					B[i->first].clear();
				}
				Circuit(s);
				s+=1;
			}
			else{
				s = n;
			}
		}
	}

	void printCycle(){
		graph->clearPartition();
		graph->SCC();
		//graph->print();
		// Get the partition
		typename std::vector<std::set<std::pair<int,DAT*> > > partition = graph->getPartition();
		for(typename std::vector<std::set<std::pair<int,DAT*> > >::iterator i = partition.begin(); i != partition.end(); i++){
			for(typename std::set<std::pair<int,DAT*> >::iterator j = i->begin(); j != i->end(); j++ ){
				std::cout<<j->first << " : " << j->second->getBB()->getParent()->getName().str()<< std::endl;
				std::cout<<j->second<<std::endl;
				std::vector<DAT*> const succ = j->second->getSuccessor();
				for(typename std::vector<DAT*>::const_iterator i = succ.begin(); i != succ.end(); i++){
					std::cout<< "        "<< *i << std::endl;
				}
				std::cout<<std::endl;
			}
		}

		for(std::vector<std::vector<int> >::iterator i = cycles.begin(); i != cycles.end();i++){
			for(std::vector<int>::iterator j = i->begin(); j != i->end(); j++){
				std::cout<<*j<<",";
			}
			std::cout<<std::endl;
		}
	}
};

#endif
