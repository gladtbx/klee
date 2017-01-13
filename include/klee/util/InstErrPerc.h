#ifndef INSTERRPERC_H_
#define INSTERRPERC_H_
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Support/DebugLoc.h"
#include "llvm/Support/Casting.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <map>

class errPercNode{
private:
	llvm::BasicBlock* BB;
	std::vector<errPercNode*> successors;
	int visited;
	int correctVisit;
	int errorVisit;
	bool isBR;
	double hue;
	std::map<llvm::BasicBlock*, unsigned int> blockFail;
public:
	errPercNode():BB(0),visited(0),correctVisit(0),errorVisit(0),isBR(false),hue(0.0){

	}
	errPercNode(llvm::BasicBlock* const _BB):BB(_BB),visited(0),correctVisit(0),errorVisit(0),isBR(false),hue(0.0){

	}

	llvm::BasicBlock* getBB(){
		return BB;
	}

	void insertSuccessor(errPercNode* const _succ){
		successors.push_back(_succ);
	}

	std::vector<errPercNode*> const &getSuccessor(){
		return successors;
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

	void setBlockFail(llvm::BasicBlock* block);

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
	instErrPerc():root(NULL),totalpassed(0),totalfailed(0){
	}

	errPercNode* find_Block_Rec(errPercNode* curr, llvm::BasicBlock* const target);

	errPercNode* find_Block(llvm::BasicBlock* const target){
		return find_Block_Rec(root, target);
	}

	void init();

	unsigned int totalpassed;
	unsigned int totalfailed;
	std::vector< std::pair<double,errPercNode*> > suspiciousList;
public:
	instErrPerc(errPercNode* &_root){
		root = _root;
		totalpassed = 0;
		totalfailed = 0;
		init();
	}

	instErrPerc(llvm::BasicBlock* const BB){
		root = new errPercNode(BB);
		init();
	}

	void processTestCase(bool const pass,std::vector<unsigned char> const &concreteBranches, int const id);

	void calcHue(std::string outFileName);
};

#endif
