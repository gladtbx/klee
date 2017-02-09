#include "klee/util/InstErrPerc.h"
using namespace llvm;

void errPercNode::setBlockFail(const llvm::BasicBlock* block){
	std::pair<std::map<const llvm::BasicBlock*, unsigned int>::iterator,bool> it =
			blockFail.insert(std::pair<const llvm::BasicBlock*, unsigned int> (block,1));
	if(!it.second){
		return;
	}
	it.first->second++;
	return;
}

bool suspiciousCmp(const std::pair<double,errPercNode*> & first, const std::pair<double,errPercNode*>& second){
	//Gladtbx: now we just compare the hue of the pair. We can add the functionality to compare based on the relation of the instruction and the position of the appearance of error.
	if(first.first<second.first){
		return true;
	}
	return false;
}

//Gladtbx: Need to explore fCalls as well.
void instErrPerc::calcHue(std::string outFileName){
	std::ofstream hueOutputFile;
	std::ofstream gdbOutputFile;
	gdbOutputFile.open(outFileName.insert(outFileName.find_last_of('/')+1,"gdb").c_str(),std::ofstream::out);
	if(!gdbOutputFile){
		klee::klee_error("Failed to open gdbSuspicious.txt");
	}

	hueOutputFile.open(outFileName.c_str(),std::ofstream::out);

	if(!hueOutputFile){
		klee::klee_error("Failed to open suspiciousInstList.txt");
	}

	if(totalfailed == 0){
		klee::klee_warning("No failed pass. No error percentage calculated\n");
		hueOutputFile<<"No failed pass. No error percentage calculated\n";
		gdbOutputFile<<"No failed pass. No gdb debugging info generated\n";
		hueOutputFile.close();
		gdbOutputFile.close();
		return;
	}
	std::vector<errPercNode*> worklist;
	worklist.push_back(root);
	while(!worklist.empty()){
		errPercNode* current = worklist.back();
		worklist.pop_back();
		current->set_visited(-2);
		//Actual calculation done here.
		current->calc_hue(totalpassed,totalfailed);
		suspiciousList.push_back(std::pair<double,errPercNode*> (current->get_hue(),current));
		std::vector<errPercNode*> successor = current->getSuccessor();
		for(unsigned int i = 0; i < successor.size() ; i++){
			if(successor[i]->get_visited() != -2){
				worklist.push_back(successor[i]);
			}
		}
		std::vector<errPercNode*> fCalls = current->getFcall();
		for(unsigned int j = 0; j < fCalls.size(); j++){
			if(fCalls[j]->get_visited() != -2){
				worklist.push_back(fCalls[j]);
			}
		}
	}
	std::sort(suspiciousList.begin(),suspiciousList.end(),suspiciousCmp);
	//Temp output procedure
	hueOutputFile<<"Total correct run: " << totalpassed << std::endl;
	hueOutputFile<<"Total failed run: " << totalfailed << std::endl;

	for(unsigned int i = 0; i < suspiciousList.size();i++){
		if(suspiciousList[i].second->getBB()->getParent()){
			std::vector<unsigned int> lineNum;
            for (BasicBlock::const_iterator insIt = suspiciousList[i].second->getBB()->begin(), e = suspiciousList[i].second->getBB()->end(); insIt != e; ++insIt){
            	unsigned int line = insIt->getDebugLoc().getLine();
            	if(std::find(lineNum.begin(), lineNum.end(), line) == lineNum.end()){
            		lineNum.push_back(line);
            		MDNode *N = insIt->getMetadata("dbg");
            		StringRef File;
            		if (N){
            			DILocation Loc(N);
            			File = Loc.getFilename();
            		}
            		hueOutputFile << "File: " << File.str() <<", line at: " << line;
            		hueOutputFile << " has a hue level of " << suspiciousList[i].first << std::endl;//LLVM 4.0 can provide file information. LLVM3.4 can not.
            	}
            }
		}
	}
	hueOutputFile.close();

	std::set<const BasicBlock*> processedBB;
	for(unsigned int i = 0; i < suspiciousList.size();i++){
		const BasicBlock* parent = suspiciousList[i].second->getBB();
		if(parent->getParent() && processedBB.find(parent) == processedBB.end()){
			processedBB.insert(parent);
			std::vector<unsigned int> lineNum;
            BasicBlock::const_iterator insIt = parent->begin(), e = parent->end();
            if(insIt != e){
            	MDNode *N = insIt->getMetadata("dbg");
				StringRef File;
				if (N){
					DILocation Loc(N);
					File = Loc.getFilename();
				}
				gdbOutputFile << "break " << File.str() <<" : " << insIt->getDebugLoc().getLine() << std::endl;
            }
		}
	}
}

//FindBlock needs edit.
errPercNode* instErrPerc::find_Block_Rec(errPercNode* curr, const llvm::BasicBlock* target, int __id){
	//sleep(1);
	if(target == curr->getBB()){
		return curr;
	}
	if(curr->get_visited() == __id){
		return NULL;
	}
	curr->set_visited(__id);
	errPercNode* ret = NULL;
	const std::vector<errPercNode*> successors = curr->getSuccessor();
	for(unsigned i = 0; i < successors.size(); i++){
		if(successors[i]->get_visited()!=-1){
			//tab+="  ";
			ret = find_Block_Rec(successors[i],target,__id);
			if(ret){
				break;
			}
		}
	}
	if(!ret){
		const std::vector<errPercNode*> fcalls = curr->getFcall();
		for(unsigned j = 0; j < fcalls.size(); j++){
			if(fcalls[j]->get_visited()!=-1){
				ret = find_Block_Rec(fcalls[j],target,__id);
				if(ret){
					break;
				}
			}
		}
	}
	return ret;
}

errPercNode* instErrPerc::insertSuccNode(errPercNode* parent, const llvm::BasicBlock* succ){
	errPercNode* nextNode = find_Block(succ);//we have to use findBlock because we can not mark the llvm Basic Block directly.
	if(nextNode == NULL){
		errPercNode* succ_node = new errPercNode(succ);
		parent->insertSuccessor(succ_node);
		return succ_node;
	}
	else{//otherwise we need to point back
		parent->insertSuccessor(nextNode);
	}
	return NULL;
}

errPercNode* instErrPerc::insertFcallNode(errPercNode* parent, const llvm::BasicBlock* succ){
	errPercNode* nextNode = find_Block(succ);//we have to use findBlock because we can not mark the llvm Basic Block directly.
	if(nextNode == NULL){
		errPercNode* succ_node = new errPercNode(succ);
		parent->insertFcall(succ_node);
		return succ_node;
	}
	else{//otherwise we need to point back
		parent->insertFcall(nextNode);
	}
	return NULL;
}

const Function* instErrPerc::getTargetFunction(const Value *calledVal) {
  SmallPtrSet<const GlobalValue*, 3> Visited;

  const Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (const GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      if (!Visited.insert(gv))
        return 0;

      if (const Function *f = dyn_cast<Function>(gv))
        return f;
      else if (const GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;
    } else if (const llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
      if (ce->getOpcode()==Instruction::BitCast)
        c = ce->getOperand(0);
      else
        return 0;
    } else
      return 0;
  }
  return NULL;
}


/*
 * Assuming there is no func alias. Check executor.cpp: Executor::getTargetFunction
 */
void instErrPerc::init(){
	std::vector<errPercNode*> worklist;
	worklist.push_back(root);
	while(!worklist.empty()){
		errPercNode* current = worklist.back();
		worklist.pop_back();
		//Deal with fun Calls
		for(llvm::BasicBlock::const_iterator it = current->getBB()->begin(); it != current->getBB()->end(); it++){

			if(it->getOpcode() == llvm::Instruction::Call){
				const llvm::CallInst* callInst = cast<CallInst>(it);
				const llvm::Value* targetValue = callInst->getCalledValue();
				const llvm::Function* targetFunc = getTargetFunction(targetValue);
				if(targetFunc)
				if(targetFunc && ! targetFunc->isDeclaration()){
					if(targetFunc->begin() != targetFunc->end()){
						errPercNode* calledNode = insertFcallNode(current,&(targetFunc->getEntryBlock()));
						if(calledNode){
							worklist.push_back(calledNode);//If the called node hasn't been explored before, we need to add it to the worklist.
						}
					}
				}
			}
		}
		//Deal with terminators
		const llvm::TerminatorInst* ti = current->getBB()->getTerminator();
		if(ti->getOpcode() == llvm::Instruction::Ret){

		}
		else if(ti->getOpcode() == llvm::Instruction::Switch){
			const SwitchInst *bi = cast<SwitchInst>(ti);
			current->set_isBR();
			errPercNode* nextNode = insertSuccNode(current, bi->case_default().getCaseSuccessor());//default is zero, then cases
			if(nextNode){
				worklist.push_back(nextNode);
			}
			for(llvm::SwitchInst::ConstCaseIt it = bi->case_begin(); it != bi->case_end() ; it++ ){
				errPercNode* nextNode = insertSuccNode(current, it.getCaseSuccessor());
				if(nextNode){
					worklist.push_back(nextNode);
				}
			}
		}
		else{
			if(ti->getOpcode() == llvm::Instruction::Br){
				const BranchInst *bi = cast<BranchInst>(ti);
				if(bi->isConditional()){
					current->set_isBR();
				}
			}
			for(unsigned I = 0; I < ti->getNumSuccessors(); I++){
				llvm::BasicBlock* succ = ti->getSuccessor(I);
				errPercNode* nextNode = insertSuccNode(current,succ);
				if(nextNode){
					worklist.push_back(nextNode);
				}
			}
		}
	}
}

void instErrPerc::processTestCase(bool const pass,std::vector<unsigned char> const &concreteBranches, int const id){
	errPercNode* currNode = root;
	std::vector<errPercNode*> visitedNodes;
	std::vector<errPercNode*>::iterator fcallIt = root->getFcall().begin();
	std::vector<std::pair<errPercNode*,std::vector<errPercNode*>::iterator> > stack;
	if(pass){
		totalpassed++;
	}
	else{
		totalfailed++;
	}
	for(unsigned int i = 0; i < concreteBranches.size(); i++){
		while(!currNode->is_BR() || fcallIt != currNode->getFcall().end()){
			//std::cout<<" Currently working on node: " << currNode->getBB()->getParent()->getName().str() << " with BB: " << currNode->getBB() << " line: " << currNode->getBB()->getTerminator()->getDebugLoc().getLine() << std::endl;
			//currNode->getBB()->dump();
			if(currNode->get_visited() != id){
				currNode->set_visited(id);
				if(pass){
					currNode->set_correct(pass);
				}
				else{
					visitedNodes.push_back(currNode);
				}
			}
			if(fcallIt != currNode->getFcall().end()){
				if((*fcallIt) == NULL){
					assert(0 && "fcallIt is NULL" );
				}
				stack.push_back(std::pair<errPercNode*,std::vector<errPercNode*>::iterator> (currNode, fcallIt));
				currNode = *fcallIt;
				fcallIt = currNode->getFcall().begin();

				continue;
			}

			//Otherwise if we have a non BR terminator.
			if(currNode->is_BR()){
				break;
			}
			if(currNode->getBB()->getTerminator()->getOpcode() == llvm::Instruction::Ret){
				std::pair<errPercNode*,std::vector<errPercNode*>::iterator> retPair = stack.back();
				stack.pop_back();
				fcallIt = retPair.second;
				fcallIt++;//fcallIt only increments when we return from a call.
				currNode = retPair.first;
				continue;
			}
			std::vector<errPercNode*> successor = currNode->getSuccessor();
			if(successor.size() == 0){
				for (BasicBlock::const_iterator it = currNode->getBB()->begin(); it != currNode->getBB()->end(); it++){
					std::cout<< it->getDebugLoc().getLine() << std::endl;
				}
				assert(0&&"No successor!");
			}
			else{
				currNode = successor[0];//Gladtbx assuming none BR nodes only have one successor;
				fcallIt = currNode->getFcall().begin();
			}
			assert(currNode && "instErrPerc Error: CFG deadend!\n");
		}
		if(currNode->get_visited() != id){
			currNode->set_visited(id);
			if(pass){
				currNode->set_correct(pass);
			}
			else{
				visitedNodes.push_back(currNode);
			}
		}
		// For switch inst, we might have multiple successors.
		if(currNode->getBB()->getTerminator()->getOpcode() == llvm::Instruction::Switch){
			if(i + sizeof(int) > concreteBranches.size()){
				assert(0&&"Switch Index not recorded correctly");
			}
			//FIXME: Need to get four bytes, actually, should get sizeof int bytes.
			char switchIndex[4];
			switchIndex[0]= concreteBranches[i];
			switchIndex[1]= concreteBranches[i+1];
			switchIndex[2]= concreteBranches[i+2];
			switchIndex[3]= concreteBranches[i+3];
			int * index_ptr = (int*) switchIndex;
			int index = *index_ptr;
			if(index >= currNode->getSuccessor().size()){
				assert(0&&"Switch successor out of index!");
			}
			currNode = currNode->getSuccessor()[index];
			i += (sizeof(int) - 1);// i is incremented because we don't consider switch as real branch, however we have
			//used space in the vector, so we need to pop it off.
			fcallIt = currNode->getFcall().begin();
			continue;
		}
		if(concreteBranches[i] == '0'){//if it is 0 then we follow the false branch, which is 1.
			currNode = currNode->getSuccessor()[1];
			fcallIt = currNode->getFcall().begin();
		}
		else if (concreteBranches[i] == '1'){
			currNode = currNode->getSuccessor()[0];
			fcallIt = currNode->getFcall().begin();
		}
		else{
			assert(0 && "instErrPerc: Concrete Branches having value other than 0 or 1");
		}
	}//Gladtbx: After the for loop, the rest of code still needs to be dealt with.
	if(currNode->get_visited() != id){
		currNode->set_visited(id);
		if(pass){
			currNode->set_correct(pass);
		}
		else{
			visitedNodes.push_back(currNode);
		}
	}
	/*	Some extra work needs to be done:
	 *  Look for the cause of the error.
	 *  Mark the test case number
	 *  And create a list of suspicious variable names. */
	for(unsigned int i = 0; i < visitedNodes.size(); i++){
		visitedNodes[i]->setBlockFail(currNode->getBB());
		visitedNodes[i]->set_correct(pass);
	}
}
