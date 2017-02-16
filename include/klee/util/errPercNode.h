#ifndef ERRPERCNODE_H
#define ERRPERCNODE_H
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/Support/DebugLoc.h"
#include "llvm/Support/Casting.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/DebugInfo.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/util/TarjanSCC.h"

#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <map>
#include <set>
#include "unistd.h"

class errPercNode{
private:
	const llvm::BasicBlock* BB;
	std::vector<errPercNode*> successors;
	std::vector<errPercNode*> fCalls;
	int visited;
	int correctVisit;
	int errorVisit;
	bool isBR;
	double hue;
	int tarjanid;
	std::map<const llvm::BasicBlock*, unsigned int> blockFail;
	std::pair<errPercNode*, std::vector<errPercNode*>::iterator> retLoc;
public:
	errPercNode():BB(0),visited(0),correctVisit(0),errorVisit(0),isBR(false),hue(0.0),tarjanid(0){

	}
	errPercNode(const llvm::BasicBlock* _BB, int __tarjanid):BB(_BB),visited(0),correctVisit(0),errorVisit(0),isBR(false),hue(0.0),tarjanid(__tarjanid){

	}

	const llvm::BasicBlock* getBB(){
		return BB;
	}

	void insertSuccessor(errPercNode* const _succ){
		successors.push_back(_succ);
	}

	void insertFcall(errPercNode* const fCall){
		fCalls.push_back(fCall);
	}

	std::vector<errPercNode*> const &getSuccessor(){
		return successors;
	}

	std::vector<errPercNode*> &getFcall(){
		return fCalls;
	}

	void set_isBR(){
		isBR = true;
	}

	bool is_BR(){
		return isBR;
	}

	void set_visited(){
		visited = -1;
	}

	int get_visited(){
		return visited;
	}

	void set_unvisited(){
		visited = 0;
	}

	void set_visited(int id){
		visited = id;
	}

	void set_correct(bool const pass){
		if(pass){
			correctVisit++;
		}
		else{
			errorVisit++;
		}
	}

	int get_correct(){
		return correctVisit;
	}

	int get_error(){
		return errorVisit;
	}

	void setRetLoc(std::pair<errPercNode*, std::vector<errPercNode*>::iterator> _retLoc){
		retLoc = _retLoc;
	}

	std::pair<errPercNode*, std::vector<errPercNode*>::iterator> getRetLoc(){
		return retLoc;
	}

	void setBlockFail(const llvm::BasicBlock* block);

	void calc_hue(unsigned int const totalpassed, unsigned int const totalfailed){
		if((correctVisit + errorVisit) == 0){
			hue = 1;
			return;
		}
		if(errorVisit == 0){
			hue = 1;
			return;
		}
		if(correctVisit == 0){
			hue = 0;
			return;
		}

		hue = (correctVisit/(double)totalpassed)/(correctVisit/(double)totalpassed+errorVisit/(double)totalfailed);
	}

	double get_hue(){
		return hue;
	}

	int get_tarjanid(){
		return tarjanid;
	}
};



#endif
