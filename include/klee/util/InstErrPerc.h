#ifndef INSTERRPERC_H_
#define INSTERRPERC_H_
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
	std::map<const llvm::BasicBlock*, unsigned int> blockFail;
	std::pair<errPercNode*, std::vector<errPercNode*>::iterator> retLoc;
public:
	errPercNode():BB(0),visited(0),correctVisit(0),errorVisit(0),isBR(false),hue(0.0){

	}
	errPercNode(const llvm::BasicBlock* _BB):BB(_BB),visited(0),correctVisit(0),errorVisit(0),isBR(false),hue(0.0){

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
};

class instErrPerc{
private:
	errPercNode* root;
	instErrPerc():root(NULL),totalpassed(0),totalfailed(0),id(-1){
	}

	errPercNode* find_Block_Rec(errPercNode* curr, const llvm::BasicBlock* target, int __id);

	errPercNode* find_Block(const llvm::BasicBlock* target){
		errPercNode* ret = find_Block_Rec(root, target,id);
		id--;
		return ret;
	}

	errPercNode* insertSuccNode(errPercNode* parent, const llvm::BasicBlock* succ);

	errPercNode* insertFcallNode(errPercNode* parent, const llvm::BasicBlock* succ);

	const llvm::Function* getTargetFunction(const llvm::Value *calledVal);

	void init();

	unsigned int totalpassed;
	unsigned int totalfailed;
	std::vector< std::pair<double,errPercNode*> > suspiciousList;
	int id;
	std::string tab;
public:
	instErrPerc(errPercNode* &_root){
		root = _root;
		totalpassed = 0;
		totalfailed = 0;
		id = -1;
		init();
	}

	instErrPerc(llvm::BasicBlock* const BB){
		root = new errPercNode(BB);
		totalpassed = 0;
		totalfailed = 0;
		id = -1;
		init();
	}

	void processTestCase(bool const pass,std::vector<unsigned char> const &concreteBranches, int const id);

	void calcHue(std::string outFileName);
};

#endif
