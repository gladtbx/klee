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
	}
	std::sort(suspiciousList.begin(),suspiciousList.end(),suspiciousCmp);
	//Temp output procedure
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

errPercNode* instErrPerc::find_Block_Rec(errPercNode* curr, llvm::BasicBlock* const target){
	if(target == curr->getBB()){
		return curr;
	}
	curr->set_visited();
	errPercNode* ret = NULL;
	const std::vector<errPercNode*> successors = curr->getSuccessor();
	for(unsigned i = 0; i < successors.size(); i++){
		if(successors[i]->get_visited()!=-1){
			ret = find_Block_Rec(successors[i],target);
			if(ret){
				break;
			}
		}
	}
	curr->set_unvisited();
	return ret;
}

void instErrPerc::init(){
	std::vector<errPercNode*> worklist;
	worklist.push_back(root);
	while(!worklist.empty()){
		errPercNode* current = worklist.back();
		//std::cout<<" Currently working on line: " << current->getBB()->getFirstNonPHI()->getDebugLoc().getLine() << std::endl;
		worklist.pop_back();
		//current->set_visited();
		const llvm::TerminatorInst* ti = current->getBB()->getTerminator();
		if(ti->getOpcode() == llvm::Instruction::Br){
			const BranchInst *bi = cast<BranchInst>(ti);
			if(bi->isConditional()){
				current->set_isBR();
			}
		}
		for(unsigned I = 0; I < ti->getNumSuccessors(); I++){
			llvm::BasicBlock* succ = ti->getSuccessor(I);
			//std::cout<<succ->getFirstNonPHI()->getDebugLoc().getLine()<<std::endl;
			errPercNode* nextNode = find_Block(succ);//we have to use findBlock because we can not mark the llvm Basic Block directly.
			if(nextNode == NULL){
				errPercNode* succ_node = new errPercNode(succ);
				current->insertSuccessor(succ_node);
				worklist.push_back(succ_node);
				//for (llvm::BasicBlock::iterator i = succ->begin(), e = succ->end(); i != e; ++i){
				//std::cout<<" Block added to work list: "<<succ->getFirstNonPHI()->getDebugLoc().getLine()<<std::endl;
				//}
			}
			else{//otherwise we need to point back
				current->insertSuccessor(nextNode);
				//std::cout<<" Node linked: "<<nextNode->getBB()->getFirstNonPHI()->getDebugLoc().getLine()<<std::endl;
			}
		}
	}
}

void instErrPerc::processTestCase(bool const pass,std::vector<unsigned char> const &concreteBranches, int const id){
	errPercNode* currNode = root;
	std::vector<errPercNode*> visitedNodes;
	if(pass){
		totalpassed++;
	}
	else{
		totalfailed++;
	}
	for(unsigned int i = 0; i < concreteBranches.size(); i++){
		while(!currNode->is_BR()){
			if(currNode->get_visited() != id){
				currNode->set_visited(id);
				if(pass){
					currNode->set_correct(pass);
				}
				else{
					visitedNodes.push_back(currNode);
				}
			}
			std::vector<errPercNode*> successor = currNode->getSuccessor();
			currNode = successor[0];//Gladtbx assuming none BR nodes only have one successor;

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
		if(concreteBranches[i] == '0'){//if it is 0 then we follow the false branch, which is 1.
			currNode = currNode->getSuccessor()[1];
		}
		else if (concreteBranches[i] == '1'){
			currNode = currNode->getSuccessor()[0];
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
