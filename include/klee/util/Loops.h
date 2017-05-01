#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Module.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/SmallPtrSet.h"


//#include "llvm/Support/CFG.h"

#include <algorithm>
#include <queue>
#include <set>
#include <iostream>
#ifndef LOOPS_H
#define LOOPS_H
namespace klee{
/*
class Loop{
private:
	int entry;
	int exit;
	std::vector<int> cycle;
	Loop():entry(0),exit(0){}
public:
	Loop(int _entry, int _exit, const std::vector<int> & _cycle):entry(_entry),exit(_exit),cycle(_cycle){
	}
	~Loop(){
		cycle.clear();
	}

	void print(){
		std::cout<< "entry: "<< entry << " , exit: " << exit << std::endl;
	}
};

class Loops{
private:
	const std::vector<std::vector<int> > cycles;
	std::vector<errPercNode*> tarjanNodes;
	std::vector<Loop> loops;

public:
	Loops(const std::vector<std::vector<int> >& _cycles,
			const std::vector<errPercNode*> _tarjanNodes):cycles(_cycles),tarjanNodes(_tarjanNodes){
	}

	void print(){
		for(std::vector<Loop>::iterator loop = loops.begin(); loop != loops.end(); loop++){
			loop->print();
		}
	}

	void gen_loops(){
		for(std::vector<std::vector<int> >::const_iterator i = cycles.begin(); i != cycles.end(); i++){
			//For each cycle, potentially it is a loop.
			std::cout<< "=====================cycle starts========================" << std::endl;
			int loop_exit_id = -1;
			int loop_entry_id = -1;
			for(std::vector<int>::const_iterator j = i->begin(); j != i->end(); j++){
				//for each cycle, find the entry and exit
				//entry is the block which has all the successors in the same cycle, with one of ancestors outside the cycle
				//exit is the block with all the ancestors in the same cycle, and one of the successors outside the cycle.
				errPercNode* curr = tarjanNodes[*j];
				std::vector<errPercNode*> succs= curr->getSuccessor();
				int outCount = 0;
				int inCount = 0;
				int succNodeId;
				//check succs
				for(std::vector<errPercNode*>::const_iterator succ = succs.begin(); succ != succs.end(); succ++){
					int tarjanID = (*succ)->get_tarjanid();
					if(std::find(i->begin(),i->end(),tarjanID) == i->end()){
						//Succ is not in Cycle
						outCount++;
						succNodeId = tarjanID;
					}
				}
				//check preds
				for(llvm::const_pred_iterator pred = pred_begin(curr->getBB()); pred != pred_end(curr->getBB());pred++){
					bool pred_in_cycle = false;
					for(std::vector<int>::const_iterator k = i->begin(); k != i->end(); k++){//K loops over the cycle
						if(tarjanNodes[*k]->getBB() == *pred){
							// pred is inside the loop
							pred_in_cycle = true;
							break;
						}
					}
					if(!pred_in_cycle){
						inCount++;
					}
				}
				//FIXME: Should it be one?
				if(outCount >= 1){
					if(loop_exit_id == -1){
						loop_exit_id = *j;
						std::cout<<"Succ ID set to " << succNodeId << std::endl;
					}
					else{
						std::cout<< "More than one exit found! The Succ ID is now " << succNodeId << std::endl;
						loop_exit_id = *j;
					}
				}
				//Assuming there is not cycle with size one.
				if(inCount == 1){
					if(loop_entry_id == -1){
						loop_entry_id = *j;
					}
					else{
						//std::cout<< "More than one entry found!" << std::endl;
						loop_entry_id = -2;
					}
				}
			}
			if(loop_exit_id != -1 && loop_exit_id != -2 && loop_entry_id != -1 && loop_entry_id != -2){
				//We found a loop!
				Loop loop(loop_entry_id, loop_exit_id, *i);
				loops.push_back(loop);
			}
			std::cout<< "=====================cycle finishes========================" << std::endl;
		}
	}
};
*/
class KLoop{
private:
	llvm::Loop* loop;
	std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > > pathsToExits;//For each exit, there is a vector of path.
	std::vector<std::vector<llvm::BasicBlock*> > pathsToHead;
	KLoop():loop(0){}
public:
	KLoop(llvm::Loop* _loop):loop(_loop){

	}
	~KLoop(){
		//Fixme: clear needs work;
		pathsToExits.clear();
		pathsToHead.clear();
	}

	/*llvm::BasicBlock* selectPath(const std::vector<llvm::BasicBlock*>& currPath){
		llvm::BasicBlock* ret = NULL;
		for(std::map<std::vector<llvm::BasicBlock*>,bool>::iterator pathIt = paths.begin(),
				pathItEnd=paths.end(); pathIt != pathItEnd; pathIt++){
			//Loop through all the paths, if it is already taken, then don't need to explore again.
			if(pathIt->second){
				continue;
			}
			for(std::vector<llvm::BasicBlock*>::const_iterator inBlockIt = currPath.begin(), blockIt = pathIt->first.begin(),
					inBlockItEnd = currPath.end(); (inBlockIt != inBlockItEnd) && (*inBlockIt == *blockIt); inBlockIt++, blockIt++  ){

			}
		}
	}*/


	llvm::Loop* getloop(){
		return loop;
	}

	bool cycleExists(llvm::Loop* loop){

		return false;
	}
};

class KLoops{
private:
	std::vector<llvm::Loop*> kloops;
	KLoops(){};
	//std::map<llvm::Loop*,std::vector<std::vector<llvm::BasicBlock*> > > loopPaths;
	std::map<llvm::Loop*, std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > > > pathsToExits;//For each exit, there is a vector of path.
	std::map<llvm::Loop*, std::vector<std::vector<llvm::BasicBlock*> > > pathsToHead;
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

	//FIXME: If loop has only one block, should not consider as a loop.
	void calcPath(llvm::Loop* curr){
		//We first check if all the subloops have been dealt with
		const std::vector<llvm::Loop*> subloops = curr->getSubLoops();
		for(std::vector<llvm::Loop*>::const_iterator subloop = subloops.begin(),
				subloopEnd = subloops.end();subloop != subloopEnd;subloop++){
			if(std::find(processedloops.begin(),processedloops.end(),(*subloop))== processedloops.end()){
				//If subloop have not been processed yet.
				calcPath(*subloop);
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
			//Check if we find an exit.
			if(std::find(exitBlocks.begin(),exitBlocks.end(),currBlock) != exitBlocks.end()){
				//We find one of the exit blocks.
				pathsToExits[curr][currBlock].push_back(currPath);
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
							currPath.pop_back();//Make sure if we have multiple nextblocks, we don't overwrite each other
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
		//We need to cross list all the path from the head to exit with the path from head to head
		std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > > ptoexits = pathsToExits[curr];
		std::vector<std::vector<llvm::BasicBlock*> > pathHtoH = pathsToHead[curr];
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
			(*kloop)->dump();
		}
	}

	void printPath(){
		for(std::map<llvm::Loop*,std::vector<std::vector<llvm::BasicBlock*> > >::iterator paths = pathsToHead.begin(),
				pathEnd = pathsToHead.end(); paths != pathEnd; paths++){
			std::cout<< "Path for loop: " << paths->first << " at line: " << paths->first->getHeader()->begin()->getDebugLoc().getLine() << std::endl;
			for(std::vector<std::vector<llvm::BasicBlock*> >::iterator path = paths->second.begin(),
					pathEnd = paths->second.end(); path != pathEnd; path++){
				std::cout<<"	";
				for(std::vector<llvm::BasicBlock*>::iterator BBit = path->begin(),
						BBitEnd = path->end(); BBit != BBitEnd; BBit++){
					std::cout<< *BBit<<":" << (*BBit)->begin()->getDebugLoc().getLine() << "->" ;
					(*BBit)->dump();
				}
				std::cout<<std::endl;
			}
		}
	}

	const std::vector<llvm::Loop*> &getLoops(){
		return processedloops;
	}

	const std::map<llvm::Loop*,std::vector<std::vector<llvm::BasicBlock*> > > &getPathsH2H(){
		return pathsToHead;
	}

	const std::map<llvm::Loop*, std::map<llvm::BasicBlock*, std::vector<std::vector<llvm::BasicBlock*> > > > &getPathsH2E(){
		return pathsToExits;
	}
};
}

#endif
