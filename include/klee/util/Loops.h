#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "klee/util/Ref.h"
#include "klee/Expr.h"

//#include "llvm/Support/CFG.h"

#include <algorithm>
#include <queue>
#include <set>
#include <iostream>
#ifndef LOOPS_H
#define LOOPS_H
namespace klee{

class Path{
private:
	std::vector<llvm::BasicBlock*> path;
	//The branch at the end of the block is invariant.
	std::vector<llvm::BasicBlock*> invariantBranches;
public:
	Path(){

	}
	virtual ~Path(){
		path.clear();
	}

	Path(std::vector<llvm::BasicBlock*>& p):path(p){

	}

	Path(const Path& rhs):path(rhs.path),invariantBranches(rhs.invariantBranches){
		//std::cerr<<"***********************CPY Called!"<<std::endl;
		//dump();
		//std::cerr<<"***********************"<<std::endl;
	}

	void addBlock(llvm::BasicBlock* bb){
		path.push_back(bb);
	}

	void addCond(llvm::BasicBlock* bit){
		invariantBranches.push_back(bit);
	}

	std::vector<llvm::BasicBlock*>::iterator begin(){
		return path.begin();
	}

	std::vector<llvm::BasicBlock*>::iterator end(){
		return path.end();
	}

	bool same(const std::vector<llvm::BasicBlock*>& in){
		return std::equal(path.begin(),path.end(),in.begin());
	}

	long unsigned int size() const{
		return path.size();
	}

	void dump() const{
		std::cout<<"Invariants for path:";
		for(std::vector<llvm::BasicBlock*>::const_iterator BBit = path.begin(),
			BBitEnd = path.end(); BBit != BBitEnd; BBit++){
			std::cout<< *BBit<<":" << (*BBit)->begin()->getDebugLoc().getLine() << "->" ;
			//(*BBit)->dump();
		}
		std::cout<< std::endl<<"Invariant Branches:              ";
		for(std::vector<llvm::BasicBlock*>::const_iterator invit = invariantBranches.begin(),
				invitEnd=invariantBranches.end();invit != invitEnd; invit++){
			std::cout<<*invit<<"  ";
		}
		std::cout<<std::endl;
	}

	bool uncoverablePath(std::vector<llvm::BasicBlock*> loopPath){
		std::vector<llvm::BasicBlock*>::iterator invariantBlockit = invariantBranches.begin();
		if(invariantBlockit!=invariantBranches.end()){
			std::vector<llvm::BasicBlock*>::iterator checkit = path.begin();
			std::vector<llvm::BasicBlock*>::iterator loopit = loopPath.begin();
/*			std::cerr<<"Check uncoverable path: ";
			for(std::vector<llvm::BasicBlock*>::iterator BBit = loopPath.begin(),
				BBitEnd = loopPath.end(); BBit != BBitEnd; BBit++){
				std::cerr<< *BBit<<":" << (*BBit)->begin()->getDebugLoc().getLine() << "->" ;
			}
			std::cerr<< "              ";
			std::cerr<< "for path: ";
			for(std::vector<llvm::BasicBlock*>::iterator BBit = path.begin(),
				BBitEnd = path.end(); BBit != BBitEnd; BBit++){
				std::cerr<< *BBit<<":" << (*BBit)->begin()->getDebugLoc().getLine() << "->" ;
			}
			std::cerr<<std::endl;*/
			/*
			 * Go through each block of the current uncovered path and the current loop path.
			 * If all the blocks until a invariant block is the same, and the block following the invariant block is different
			 * return true. Because the block is invariant, the current is never going to be covered.
			 * Do for every invariant block.
			 */
			while(checkit != path.end() && loopit != loopPath.end()){
				if(*checkit != *loopit){
					return false;
				}
				if(*checkit== *invariantBlockit){
					checkit++;
					loopit++;
					if(checkit != path.end()){
						if(loopit!=loopPath.end()){
							if(*checkit!=*loopit){
								return true;
							}
						}
					}
					invariantBlockit++;
					if(invariantBlockit==invariantBranches.end()){
						return false;
					}
					break;
				}
				checkit++;
				loopit++;
			}
		}
		return false;
	}
};

typedef std::vector<Path> Paths;
/*class Paths{
private:
	std::vector<Path> pathsToHead;
public:
	Paths(){

	}

	virtual ~Paths(){
		pathsToHead.clear();
	}

	void addPaths(std::vector<llvm::BasicBlock*> path){
		pathsToHead.push_back(Path(path));
	}

	std::vector<Path>::iterator& begin(){
		return pathsToHead.begin();
	}

	std::vector<Path>::iterator& end(){
		return pathsToHead.end();
	}

	void erase(std::vector<Path>::iterator& p){
		pathsToHead.erase(p);
	}

	bool empty(){
		return pathsToHead.empty();
	}
};*/

class KLoops{
private:
	std::vector<llvm::Loop*> kloops;
	KLoops(){};
	//std::map<llvm::Loop*,std::vector<std::vector<llvm::BasicBlock*> > > loopPaths;
	//std::map<llvm::Loop*, std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > > > pathsToExits;//For each exit, there is a vector of path.
	std::map<llvm::Loop*, Paths> pathsToHead;
	std::map<llvm::Loop*, std::set<llvm::Value*> > readList;
	std::map<llvm::Loop*, std::set<llvm::Value*> > writtenList;
	std::map<llvm::Loop*, std::set<llvm::Value*> > invariantList;
	std::vector<llvm::Loop*> processedloops;

	llvm::Function* getTargetFunction( llvm::Value *calledVal) {
		using namespace llvm;
	  SmallPtrSet< GlobalValue*, 3> Visited;

	  Constant *c = dyn_cast<Constant>(calledVal);
	  if (!c)
	    return 0;

	  while (true) {
	    if ( GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
	      if (!Visited.insert(gv))
	        return 0;

	      if ( Function *f = dyn_cast<Function>(gv))
	        return f;
	      else if ( GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
	        c = ga->getAliasee();
	      else
	        return 0;
	    } else if ( llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
	      if (ce->getOpcode()==Instruction::BitCast)
	        c = ce->getOperand(0);
	      else
	        return 0;
	    } else
	      return 0;
	  }
	  return NULL;
	}
public:
	KLoops(llvm::BasicBlock* _root){
		using namespace llvm;
		 llvm::Function* func = _root->getParent();
		std::vector< llvm::Function*> worklist;
		worklist.push_back(func);
		std::vector< llvm::Function*> processedList;
		while(worklist.size()){
			func = worklist.back();
			worklist.pop_back();
			//get the dominatortree of the current function
			llvm::DominatorTree* DT = new llvm::DominatorTree();
			if( func->isDeclaration()){
				continue;
			}
			//if function is not reachable from main, we should not include any loop here.
			if(	func->isDefTriviallyDead()){
				std::cout<<func->getName().str()<<" is trivially Dead" << std::endl;
				continue;
			}
			if( func->isDiscardableIfUnused())
			std::cout<< func->getName().str()<< std::endl;
			DT->DT->recalculate(*func);
			//generate the LoopInfoBase for the current function
			llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>* FLoop = new llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>();
			FLoop->releaseMemory();
			FLoop->Analyze(DT->getBase());
			for(llvm::LoopInfoBase<llvm::BasicBlock, llvm::Loop>::iterator loop_it = FLoop->begin(), loop_end = FLoop->end(); loop_it != loop_end; loop_it++){
				//Go through each loop inside the function.
				//llvm::BasicBlock* entry = (*loop_it)->getHeader();
				//llvm::SmallVector<llvm::BasicBlock*,8> exitBlocks;
				//(*loop_it)->getExitBlocks(exitBlocks);
				kloops.push_back(*loop_it);
			}
			processedList.push_back(func);
			//Add more functions called to the worklist.
			for(llvm::Function::iterator BBit = func->begin(), BBitend = func->end(); BBit!=BBitend;BBit++){
				for(llvm::BasicBlock::iterator it = BBit->begin(), itend = BBit->end(); it != itend; it++){
					if(it->getOpcode() == llvm::Instruction::Call){
						 llvm::CallInst* callInst = cast<CallInst>(it);
						 llvm::Value* targetValue = callInst->getCalledValue();
						 llvm::Function* targetFunc = getTargetFunction(targetValue);
						if(targetFunc && ! targetFunc->isDeclaration()){
							if(targetFunc->begin() != targetFunc->end()){
								if(std::find(processedList.begin(),processedList.end(),targetFunc) == processedList.end()){
									worklist.push_back(targetFunc);//If the called node hasn't been explored before, we need to add it to the worklist.
								}
							}
						}
					}
				}
			}
		}
	}

	void genReadWrittenList(llvm::BasicBlock* currBlock, llvm::Loop* curr){
		if(curr->contains(currBlock)){
			for(llvm::BasicBlock::iterator iit = currBlock->begin(), iitEnd = currBlock->end();iit!=iitEnd;iit++){
				if(llvm::LoadInst* lins = llvm::dyn_cast<llvm::LoadInst>(&*iit)){
					llvm::Value* loaded = lins->getPointerOperand();
					readList[curr].insert(loaded);
				}
				if(llvm::StoreInst* lins = llvm::dyn_cast<llvm::StoreInst>(&*iit)){
					llvm::Value* loaded = lins->getPointerOperand();
					writtenList[curr].insert(loaded);
				}
			}
		}
	}

	void genInvariantList(llvm::Loop* curr){
		//std::cout<<"Invariant List For Loop:" << curr << std::endl;
		for(std::set<llvm::Value*>::iterator rit = readList[curr].begin(), ritEnd=readList[curr].end(); rit != ritEnd; rit++){
			if(writtenList[curr].find(*rit) == writtenList[curr].end()){
				invariantList[curr].insert(*rit);
				//(*rit)->dump();
			}
		}
	}

	bool isInvariant(llvm::Loop* curr, llvm::Value* op,std::set<llvm::Value*>& invariants){
		if(invariants.find(op) != invariants.end()){
			return true;
		}
		if (dyn_cast<llvm::Constant>(op)) {
			return true;
		}
		return false;
	}

	/*
	 * Go through each path, and calculate the conditions at each branch with relationship of the invariants.
	 */
	void processPathConds(llvm::Loop* curr){
		//go through pathsToHead and gen the conditions for the path to be coverable.
		Paths* paths = &pathsToHead[curr];
		std::set<llvm::Value*> invariants;
		for(std::vector<Path>::iterator pit=paths->begin(), pitEnd= paths->end();
				pit != pitEnd; pit++ ){
			invariants = invariantList[curr];
			//pit->dump();
			for(std::vector<llvm::BasicBlock*>::iterator bit = pit->begin(), bitEnd=pit->end() ; bit != bitEnd ; bit++ ){
				llvm::BasicBlock* currBlock = (*bit);
				//go through each line of inst of bit, check if the inst operands are invariant and constant. If so, add inst to invariant list.
				for(llvm::BasicBlock::iterator iit = currBlock->begin(), iitEnd = currBlock->end();iit!=iitEnd;iit++){
					llvm::Instruction *i = &*iit;
					//i->dump();
					switch (i->getOpcode()) {
						case llvm::Instruction::Switch:
						//TODO: add support for switch command;
						case llvm::Instruction::Br:{
							llvm::BranchInst *bi = cast<llvm::BranchInst>(i);
							if(!bi->isUnconditional()){
								assert(bi->getCondition() == bi->getOperand(0) && "Wrong operand index!");
								//i->dump();
								if(invariants.find(bi->getCondition()) != invariants.end()){
									//If the condition is invariant, we add it to the constraints of the loop path.
									//std::cerr<<"$$$$$$$$$$$$$$$$$$$$$Condition Added"<< std::endl;
									pit->addCond(currBlock);
								}
								//We need to check if the condition set
							}
							break;
						}
						//Binary Ops
						case llvm::Instruction::Add:
						case llvm::Instruction::Sub:
						case llvm::Instruction::Mul:
						case llvm::Instruction::UDiv:
						case llvm::Instruction::SDiv:
						case llvm::Instruction::URem:
						case llvm::Instruction::SRem:
						case llvm::Instruction::And:
						case llvm::Instruction::Or:
						case llvm::Instruction::Xor:
						case llvm::Instruction::Shl:
						case llvm::Instruction::LShr:
						case llvm::Instruction::AShr:
						case llvm::Instruction::ICmp:
						case llvm::Instruction::FAdd:
						case llvm::Instruction::FSub:
						case llvm::Instruction::FMul:
						case llvm::Instruction::FDiv:
						case llvm::Instruction::FRem:
						case llvm::Instruction::FCmp:
						case llvm::Instruction::Store:{
							llvm::Value* left=i->getOperand(0);
							llvm::Value* right=i->getOperand(1);
							if(isInvariant(curr, left, invariants) && isInvariant(curr, right, invariants)){
								invariants.insert(i);
								//std::cout<<"	Binary added"<<std::endl;
								//i->dump();
							}
							break;
						}
						//Unary Ops;
						case llvm::Instruction::Trunc:
						case llvm::Instruction::ZExt:
						case llvm::Instruction::SExt:
						case llvm::Instruction::IntToPtr:
						case llvm::Instruction::PtrToInt:
						case llvm::Instruction::BitCast:
						case llvm::Instruction::Load:
						case llvm::Instruction::FPTrunc:
						case llvm::Instruction::FPExt:
						case llvm::Instruction::FPToUI:
						case llvm::Instruction::FPToSI:
						case llvm::Instruction::UIToFP:
						case llvm::Instruction::SIToFP:{
							if(isInvariant(curr,i->getOperand(0),invariants)){
								invariants.insert(i);
								//std::cout<<"		Unary added"<<std::endl;
								//i->dump();
							}
							break;
						}
						default:{
							break;
						}
					}
				}
			}

			pit->dump();
			/*
			for(std::set<llvm::Value*>::iterator vi = invariants.begin(); vi != invariants.end();vi++){
				(*vi)->dump();
			}
			*/
		}
	}

	//FIXME: If loop has only one block, should not consider as a loop.
	void calcPath(llvm::Loop* curr){
		//We first check if all the subloops have been dealt with
		const std::vector<llvm::Loop*> subloops = curr->getSubLoops();
		for(std::vector<llvm::Loop*>::const_iterator subloop = subloops.begin(),
				subloopEnd = subloops.end();subloop != subloopEnd;subloop++){
			if(std::find(processedloops.begin(),processedloops.end(),(*subloop))== processedloops.end()){
				//If subloop have not been processed yet.
				calcPath(*subloop);
				//We need to add the readlist and written list of the sub loop to the current loop.
				readList[curr].insert(readList[*subloop].begin(),readList[*subloop].end());
				writtenList[curr].insert(writtenList[*subloop].begin(),writtenList[*subloop].end());
			}
		}
		//Now we need to process current loop.
		//For each block, if it is the head of one of the subloops, we need to pay attention.
		//We do BFS here to explore path. We try to find two paths, one for path to the head, one for path to each exit.
		//We should be able to hit the backedge once.
		std::queue<std::vector<llvm::BasicBlock*> > Q;
		std::vector<llvm::BasicBlock*> headPath;
		//Instead of pushing the header, we push the successors of the head.
		llvm::BasicBlock* head = curr->getHeader();
		//We need to update the readList and writtenList of the head block.
		genReadWrittenList(head, curr);

		llvm::TerminatorInst* headTerminator = head->getTerminator();
		for(unsigned i = 0, j=headTerminator->getNumSuccessors(); i < j; i++){
			headPath.push_back(headTerminator->getSuccessor(i));
			Q.push(headPath);
			headPath.clear();
		}
		llvm::SmallVector<llvm::BasicBlock*,8> exitBlocks;
		curr->getExitBlocks(exitBlocks);

		std::vector<llvm::BasicBlock*> currPath;
		llvm::BasicBlock* currBlock;
		llvm::SmallVector<llvm::BasicBlock*,8> subExitBlocks;
		unsigned numSucc;
		llvm::TerminatorInst* currTerminator;

		while(Q.size()){
			currPath = Q.front();
			Q.pop();//currPath is the path until now.
			currBlock = currPath.back();//currBlock is the current BasicBlock we need to explore.

			//We need to update the readList and writtenList of the currBlock.
			genReadWrittenList(currBlock, curr);

			//Check if we find an exit.
			if(std::find(exitBlocks.begin(),exitBlocks.end(),currBlock) != exitBlocks.end()&&
					  !curr->contains(currBlock)){
				//We find one of the exit blocks.
				pathsToHead[curr].push_back(currPath);
				continue;
			}
			//We need to check if currBlock is the head node.
			if(currBlock == head){
				pathsToHead[curr].push_back(currPath);
				continue;
			}

			//Now we check if currBlock is the head of one of the subloops.
			for(std::vector<llvm::Loop*>::const_iterator subloop = subloops.begin(),
							subloopEnd = subloops.end();subloop != subloopEnd;subloop++){
				if((*subloop)->getHeader() == currBlock){
					//We find the head of one of the subloops.
					(*subloop)->getExitBlocks(subExitBlocks);//We get all the blocks *right outside* the *subloop*
					for(llvm::SmallVector<llvm::BasicBlock*,8>::iterator nextBlock = subExitBlocks.begin(),
							nextBlockEnd = subExitBlocks.end(); nextBlock != nextBlockEnd; nextBlock++){
						//FIXME: If we detect a cycle, we should not generate path info for the loop, the loop is simply not suitable for simplification.
						if(std::find(currPath.begin(),currPath.end(),*nextBlock) == currPath.end()){//If next is not on the current path, we assume that the head is not an exit.
							currPath.push_back(*nextBlock);
							Q.push(currPath);
							currPath.pop_back();//Make sure if we have multiple next blocks, we don't overwrite each other
						}
					}
					continue;
				}
			}

			currTerminator = currBlock->getTerminator();
			numSucc = currTerminator->getNumSuccessors();
			for(unsigned i = 0; i < numSucc; i++){
				llvm::BasicBlock* nextBlock = currTerminator->getSuccessor(i);
				//FIXME: If we detect a cycle, we should not generate path info for the loop, the loop is simply not suitable for simplification.
				if(std::find(currPath.begin(),currPath.end(),nextBlock) == currPath.end()){//If next is not on the current path, we assume that the head is not an exit.
					currPath.push_back(nextBlock);
					Q.push(currPath);
					currPath.pop_back();//Make sure if we have multiple nextblocks, we don't overwrite each other
				}
			}
		}

		//The difference of readList and writtenList is the invariant list.
		genInvariantList(curr);

		//We need to cross list all the path from the head to exit with the path from head to head
		//std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > > ptoexits = pathsToExits[curr];
		//std::vector<std::vector<llvm::BasicBlock*> > pathHtoH = pathsToHead[curr];
		/*
		for(std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > >::iterator exit = ptoexits.begin(),
				exitEnd = ptoexits.end(); exit!=exitEnd;exit++){
			std::cout<<"Processing for exit: " << exit->first->begin()->getDebugLoc().getLine() <<
					" , We have " << exit->second.size() << " paths."<< std::endl;
			for(std::vector<std::vector<llvm::BasicBlock*> >::iterator exitpath = exit->second.begin(),
					exitpathEnd = exit->second.end(); exitpath!=exitpathEnd;exitpath++){
				//For each path from head to exit, we need to include the path itself, and also H->H->E.
				std::cout<< " 	path length: " << exitpath->size() << std::endl;
				std::vector<llvm::BasicBlock*> outputPath(*exitpath);
				loopPaths[curr].push_back(outputPath);
				for(std::vector<std::vector<llvm::BasicBlock*> >::iterator pHH = pathHtoH.begin(),
						pHHEnd = pathHtoH.end(); pHH != pHHEnd; pHH++){
					//If outputPath size is one, it is a direct edge out of the loop.
					//If outputPath size is greater than one, then size-1 is the exit block, size-2 is the head, size-3 is the backedge block.
					if(outputPath.size()>1 && outputPath[outputPath.size()-3]!=(*pHH)[pHH->size()-2]){
						std::cout << "		Exit: " << outputPath[outputPath.size()-2] <<" , Backedge: " << ((*pHH)[pHH->size()-2]) << std::endl;
						outputPath = std::vector<llvm::BasicBlock*>(*exitpath);
						outputPath.insert(outputPath.begin(),pHH->begin(),pHH->end());
						loopPaths[curr].push_back(outputPath);
					}
				}
			}
		}
		*/

		//Now we need to update the equvalence relationship for at each branch inst.
		processPathConds(curr);
		processedloops.push_back(curr);
	}

	void genPath(){
		//For each loop, we need to find all possible paths from the entry to exit
		//We start from the inner most loop (loop do not contain any loops).
		//Then we abstract the inner loops when calculating path for outer loops.
		//To calculate path for each loop, we use BFS.
		for(std::vector<llvm::Loop*>::iterator loop = kloops.begin(), end=kloops.end();loop!= end; loop++){
			if((*loop)->getHeader()->begin()->getDebugLoc().getLine()!=0){
				if(std::find(processedloops.begin(),processedloops.end(),(*loop))== processedloops.end()){
					//We find a new loop that is not processed.
					calcPath(*loop);
				}
			}
		}
	}

	void printLoop(){
		for(std::vector<llvm::Loop*>::iterator kloop = kloops.begin(),end=kloops.end(); kloop != end;kloop++){
			std::vector<llvm::BasicBlock*> bbs = (*kloop)->getBlocks();
			for(std::vector<llvm::BasicBlock*>::iterator bit = bbs.begin(),bitEnd=bbs.end();bit!=bitEnd;bit++){
				std::cout<<*bit<<":"<<std::endl;
				(*bit)->dump();
			}
		}
	}

	void printPath(){
		for(std::map<llvm::Loop*,Paths>::const_iterator paths = pathsToHead.begin(),
				pathEnd = pathsToHead.end(); paths != pathEnd; paths++){
			std::cout<< "Path for loop: " << paths->first << " at line: " << paths->first->getHeader()->begin()->getDebugLoc().getLine() << std::endl;
			for(std::vector<Path>::const_iterator path = paths->second.begin(),
					pathEnd = paths->second.end(); path != pathEnd; path++){
				path->dump();
			}
		}
	}

	const std::vector<llvm::Loop*> &getLoops(){
		return processedloops;
	}

	const std::map<llvm::Loop*,Paths> &getPathsH2H(){
		return pathsToHead;
	}

/*	const std::map<llvm::Loop*, std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > > > &getPathsH2E(){
		return pathsToExits;
	}*/

	void printReadWritten(){
		for(std::map<llvm::Loop*, std::set<llvm::Value*> >::iterator it = readList.begin(), itEnd=readList.end();it != itEnd; it++){
			for(std::set<llvm::Value*>::iterator sit = it->second.begin(), sitEnd=it->second.end(); sit != sitEnd; sit++){
				(*sit)->dump();
			}
			std::cout<<"======================="<<std::endl;
		}
		for(std::map<llvm::Loop*, std::set<llvm::Value*> >::iterator it = writtenList.begin(), itEnd=writtenList.end();it != itEnd; it++){
			for(std::set<llvm::Value*>::iterator sit = it->second.begin(), sitEnd=it->second.end(); sit != sitEnd; sit++){
				(*sit)->dump();
			}
			std::cout<<"=============================="<<std::endl;
		}
		for(std::map<llvm::Loop*, std::set<llvm::Value*> >::iterator it = invariantList.begin(), itEnd=invariantList.end();it != itEnd; it++){
			for(std::set<llvm::Value*>::iterator sit = it->second.begin(), sitEnd=it->second.end(); sit != sitEnd; sit++){
				(*sit)->dump();
			}
			std::cout<<"============================================="<<std::endl;
		}
	}
};
}

#endif
