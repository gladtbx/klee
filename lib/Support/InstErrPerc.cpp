#include "klee/util/InstErrPerc.h"
using namespace llvm;

void errPercNode::setBlockFail(llvm::BasicBlock* block){
	std::pair<std::map<llvm::BasicBlock*, unsigned int>::iterator,bool> it = blockFail.insert(std::pair<llvm::BasicBlock*, unsigned int> (block,1));
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
//	std::vector<>;
	std::ofstream hueOutputFile;
	hueOutputFile.open(outFileName.c_str(),std::ofstream::out);
	if(!hueOutputFile){
		klee::klee_error("Failed to open suspiciousInstList.txt");
	}
	if(totalfailed == 0){
		klee::klee_warning("No failed pass. No error percentage calculated\n");
		hueOutputFile<<"No failed pass. No error percentage calculated\n";
		hueOutputFile.close();
		return;
	}
	std::vector<errPercNode*> worklist;
	worklist.push_back(root);
	while(!worklist.empty()){
		errPercNode* current = worklist.back();
		worklist.pop_back();
		//current->set_visited();
		current->set_visited(-2);
		//Actual calculation done here.
		//std::cout<<"line: " <<current->getBB()->getFirstNonPHI()->getDebugLoc().getLine()<< " has " << current->get_correct() << " correct passes and "
		//	<< current->get_error() << " error passes" << std::endl;
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
            for (BasicBlock::iterator insIt = suspiciousList[i].second->getBB()->begin(), e = suspiciousList[i].second->getBB()->end(); insIt != e; ++insIt){
            	unsigned int line = insIt->getDebugLoc().getLine();
            	if(std::find(lineNum.begin(), lineNum.end(), line) == lineNum.end()){
            		lineNum.push_back(line);
            		hueOutputFile << "line at: " << insIt->getDebugLoc().getLine();
            		hueOutputFile << " has a hue level of " << suspiciousList[i].first << std::endl;//LLVM 4.0 can provide file information. LLVM3.4 can not.
            	}
            }
		}
	}
	hueOutputFile.close();
}

//FindBlock needs edit.
errPercNode* instErrPerc::find_Block_Rec(errPercNode* curr, llvm::BasicBlock* const target, int __id){
	//sleep(1);
	//std::cout<< tab << "Current Block: " << curr << " target block: " << target->getParent()->getName().str() << std::endl;
	if(target == curr->getBB()){
	//	std::cout<< tab << "Block: " << curr << " found target!" << std::endl;
		return curr;
	}
	if(curr->get_visited() == __id){
	//	std::cout << tab << "Block: " << curr << " visited already!" << std::endl;
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
	//curr->set_unvisited();
	//tab= tab.substr(0,tab.size()-2);
	//std::cout<< "Block: " << curr << " do not found target, return!" << std::endl;
	return ret;
}

errPercNode* instErrPerc::insertSuccNode(errPercNode* parent, llvm::BasicBlock* succ){
	errPercNode* nextNode = find_Block(succ);//we have to use findBlock because we can not mark the llvm Basic Block directly.
	if(nextNode == NULL){
		errPercNode* succ_node = new errPercNode(succ);
		parent->insertSuccessor(succ_node);
		return succ_node;
	}
	else{//otherwise we need to point back
		parent->insertSuccessor(nextNode);
		//std::cout<<" Node linked: "<<nextNode->getBB()->getFirstNonPHI()->getDebugLoc().getLine()<<std::endl;
	}
	return NULL;
}

errPercNode* instErrPerc::insertFcallNode(errPercNode* parent, llvm::BasicBlock* succ){
	errPercNode* nextNode = find_Block(succ);//we have to use findBlock because we can not mark the llvm Basic Block directly.
	if(nextNode == NULL){
		errPercNode* succ_node = new errPercNode(succ);
		parent->insertFcall(succ_node);
		return succ_node;
	}
	else{//otherwise we need to point back
		parent->insertFcall(nextNode);
		//std::cout<<" Node linked: "<<nextNode->getBB()->getFirstNonPHI()->getDebugLoc().getLine()<<std::endl;
	}
	return NULL;
}

Function* instErrPerc::getTargetFunction(Value *calledVal) {
  SmallPtrSet<const GlobalValue*, 3> Visited;

  Constant *c = dyn_cast<Constant>(calledVal);
  if (!c)
    return 0;

  while (true) {
    if (GlobalValue *gv = dyn_cast<GlobalValue>(c)) {
      if (!Visited.insert(gv))
        return 0;

      if (Function *f = dyn_cast<Function>(gv))
        return f;
      else if (GlobalAlias *ga = dyn_cast<GlobalAlias>(gv))
        c = ga->getAliasee();
      else
        return 0;
    } else if (llvm::ConstantExpr *ce = dyn_cast<llvm::ConstantExpr>(c)) {
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
		//std::cout<<" Currently working on node: " << current << " with BB: " << current->getBB() << " line: " << current->getBB()->getFirstNonPHI()->getDebugLoc().getLine() << std::endl;
		worklist.pop_back();
		//std::cout<<"Processing Func: " << current->getBB()->getParent()->getName().str() << std::endl;

		//Deal with fun Calls
		for(llvm::BasicBlock::iterator it = current->getBB()->begin(); it != current->getBB()->end(); it++){
			/*if(!current->getBB()->getParent()->getName().str().compare("start_game")){
				it->dump();
				std::cout<< it->getOpcodeName() << std::endl;
				std::cout<< it->getOpcode() << std::endl;
			}*/
			if(it->getOpcode() == llvm::Instruction::Call){
				//it->dump();
				llvm::CallInst* callInst = cast<CallInst>(it);
				llvm::Value* targetValue = callInst->getCalledValue();
				llvm::Function* targetFunc = getTargetFunction(targetValue);
				if(targetFunc)
				//std::cout<<"Find Func: " << targetFunc->getName().str() << std::endl;
				if(targetFunc && ! targetFunc->isDeclaration()){
					if(targetFunc->begin() != targetFunc->end()){
						//std::cout<<"Adding Func: " << targetFunc->getName().str() << std::endl;
						errPercNode* calledNode = insertFcallNode(current,&(targetFunc->getEntryBlock()));
						//targetFunc->getEntryBlock().dump();
						if(calledNode){
							//std::cout<<"WorkList Func: " << calledNode->getBB()->getParent()->getName().str() << std::endl;
							worklist.push_back(calledNode);//If the called node hasn't been explored before, we need to add it to the worklist.
						}
					}
				}
			}
		}
		//Deal with terminators
		const llvm::TerminatorInst* ti = current->getBB()->getTerminator();
		if(ti->getOpcode() == llvm::Instruction::Ret){
			/* I am an idiot to write this piece of code.
			 * if(root->getBB()->getParent() != current->getBB()->getParent()){
				//inserting the parent node as the only next node.
				errPercNode* parentNode = insertSuccNode(current,ti->getSuccessor(0));
				assert(parentNode && "Return cannot find parent node!");
				std::vector<errPercNode*> fCalls = parentNode->getFcall();
				std::vector<errPercNode*>::iterator fCallIt;
				for(fCallIt = fCalls.begin(); fCallIt != fCalls.end(); fCallIt++){
					if((*fCallIt) == current){
						current->setRetLoc(fCallIt);
					}
				}
				assert(fCallIt != fCalls.end() && "errPercNode Error: Child node not found in parent's call list");
			}*/
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
					//std::cout<<"Node: " << current << " is having: " << nextNode << " as child" << std::endl;
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
			//std::cout<<" Currently working on node: " << currNode << " with BB: " << currNode->getBB() << " line: " << currNode->getBB()->getFirstNonPHI()->getDebugLoc().getLine() << std::endl;
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
			//If we have fcalls, we need to do the fcalls in order.
			if(fcallIt != currNode->getFcall().end()){
				//std::cout<< currNode->getBB()->getParent()->getName().str() <<" is calling ";
				if((*fcallIt) == NULL){
					assert(0 && "fcallIt is NULL" );
				}
				//std::cout<< (*fcallIt)->getBB()->getParent()->getName().str() << std::endl;
				//Assuming we don't have recursion.
				//Gladtbx: FIXME now we only take the return node and iterator for the last calling node. Can not handle recursion of any kind.
				//(*fcallIt)->setRetLoc(std::pair<errPercNode*,std::vector<errPercNode*>::iterator> (currNode, fcallIt));
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
				//std::cout<< "Processing Ret!"<< std::endl;
				std::pair<errPercNode*,std::vector<errPercNode*>::iterator> retPair = stack.back();
				stack.pop_back();
				fcallIt = retPair.second;
				fcallIt++;//fcallIt only increments when we return from a call.
				//std::cout<< currNode->getBB()->getParent()->getName().str() << " is returning to ";
				currNode = retPair.first;
				//std::cout<< currNode->getBB()->getParent()->getName().str() << std::endl;
				/*if(fcallIt != currNode->getFcall().end()){
					std::cout<< "Next call will be: " << (*fcallIt)->getBB()->getParent()->getName().str() << std::endl;
				}
				else{
					std::cout<< "Fcall ended!" << std::endl;
				}*/
				continue;
			}
			std::vector<errPercNode*> successor = currNode->getSuccessor();
			if(successor.size() == 0){
				//std::cout<< i << " out of " << concreteBranches.size() << std::endl;
				for (BasicBlock::iterator it = currNode->getBB()->begin(); it != currNode->getBB()->end(); it++){
					std::cout<< it->getDebugLoc().getLine() << std::endl;
				}
				//currNode->getBB()->dump();
/*				currNode = root;
				for(int j = 0; j < concreteBranches.size(); j++){
					while(!currNode->is_BR()){
						successor = currNode->getSuccessor();
						if(successor.size() == 0){
							return;
						}
						else{
							currNode = successor[0];//Gladtbx assuming none BR nodes only have one successor;
						}
					}
					for (BasicBlock::iterator itt = currNode->getBB()->begin(); itt != currNode->getBB()->end(); itt++){
						std::cout<< itt->getDebugLoc().getLine() << std::endl;
					}
					std::cout<< "					successor 0 is: " << currNode->getSuccessor()[0] << std::endl;
					std::cout<< "					successor 1 is: " << currNode->getSuccessor()[1] << std::endl;
					if(concreteBranches[j] == '0'){//if it is 0 then we follow the false branch, which is 1.
						std::cout<< "Taking False branch now" << std::endl;
						currNode = currNode->getSuccessor()[1];
						std::cout<< "Next node is: " << currNode << std::endl;
					}
					else if (concreteBranches[j] == '1'){
						currNode = currNode->getSuccessor()[0];
						std::cout<< "Taking True branch now" << std::endl;
						std::cout<< "Next node is: " << currNode << std::endl;
					}
				}*/
				assert(0&&"No successor!");
				//return;
			}
			else{
				//successor[0]->setRetLoc(currNode->getRetLoc());//Need to pass on the info about return location.
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
		/*
		std::cout<< "Currently at line: " << currNode->getBB()->getTerminator()->getDebugLoc().getLine() << std::endl;
		std::cout<< "i is: " << i << " out of " << concreteBranches.size() << std::endl;
		std::cout<< "					successor 0 is: " << currNode->getSuccessor()[0] << std::endl;
		std::cout<< "					successor 1 is: " << currNode->getSuccessor()[1] << std::endl;*/
		if(concreteBranches[i] == '0'){//if it is 0 then we follow the false branch, which is 1.
			//std::cout<< "Taking False branch now" << std::endl;
			//currNode->getSuccessor()[1]->getBB()->dump();
			//currNode->getSuccessor()[0]->getBB()->dump();
			//currNode->getSuccessor()[1]->setRetLoc(currNode->getRetLoc());//Need to pass on the info about return location.
			currNode = currNode->getSuccessor()[1];
			fcallIt = currNode->getFcall().begin();
			//std::cout<< "Next node is: " << currNode << std::endl;
		}
		else if (concreteBranches[i] == '1'){
			//currNode->getSuccessor()[1]->getBB()->dump();
			//currNode->getSuccessor()[0]->getBB()->dump();
			//currNode->getSuccessor()[0]->setRetLoc(currNode->getRetLoc());//Need to pass on the info about return location.
			currNode = currNode->getSuccessor()[0];
			fcallIt = currNode->getFcall().begin();
			//std::cout<< "Taking True branch now" << std::endl;
			//std::cout<< "Next node is: " << currNode << std::endl;
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
	for(unsigned int i = 0; i < visitedNodes.size(); i++){
		visitedNodes[i]->setBlockFail(currNode->getBB());
		visitedNodes[i]->set_correct(pass);
	}
}
