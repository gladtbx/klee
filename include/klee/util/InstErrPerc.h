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
#include "klee/util/DonaldBJohnsonCircuitAlg.h"
#include "klee/util/errPercNode.h"
#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <map>
#include <set>
#include "unistd.h"

class instErrPerc{
private:
	errPercNode* root;
	instErrPerc():root(NULL),totalpassed(0),totalfailed(0),id(-1),tarjanid(0),dbj(NULL){
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
	int tarjanid;
	std::string tab;
	dbjCircuit<errPercNode>* dbj;
public:
	instErrPerc(errPercNode* &_root){
		root = _root;
		totalpassed = 0;
		totalfailed = 0;
		id = -1;
		tarjanid = 0;
		init();
		dbj = new dbjCircuit<errPercNode>(tarjanid,root);
	}

	instErrPerc(llvm::BasicBlock* const BB){
		root = new errPercNode(BB, 0);
		tarjanid = 1;
		totalpassed = 0;
		totalfailed = 0;
		id = -1;
		init();
		dbj = new dbjCircuit<errPercNode>(tarjanid,root);
		dbj->genCircuit();
		dbj->printCycle();
	}

	void processTestCase(bool const pass,std::vector<unsigned char> const &concreteBranches, int const id);

	void calcHue(std::string outFileName);
};

#endif
