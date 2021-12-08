#include "llvm/Pass.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.def"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Format.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"

#include <unordered_set>
#include <vector>
#include <algorithm>    // std::sort
#include <map>

using namespace llvm;

namespace {
struct stats_collector : public FunctionPass {
	static char ID;
	stats_collector() : FunctionPass(ID) {}

	void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.addRequired<LoopInfoWrapperPass>();
		AU.addRequired<PostDominatorTreeWrapperPass>();
	}
	bool runOnFunction(Function &F) override {
		LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
		PostDominatorTree& PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
		auto Traces = traceFormation(&LI, &PDT, F);

		return false;
	}

	std::vector<std::vector<BasicBlock*>> traceFormation(LoopInfo* LI, PostDominatorTree* PDT, Function& F) {
		// res is the 2d vector of traces
		std::vector<std::vector<BasicBlock*>> res;
		std::unordered_set<BasicBlock*> seen_in_trace;

		// identify basic blocks with hazardous instructions
		std::map<BasicBlock*, bool> contains_hazard;
		std::map<BasicBlock*, bool> contains_indirectbr;
		std::map<BasicBlock*, bool> contains_rt;
		// store all possible conditional branches for later use
		std::vector<Instruction*> conditional_branches;

		for (BasicBlock& BB : F) {
			contains_hazard[&BB] = false;
			contains_indirectbr[&BB] = false;
			contains_rt[&BB] = false;
			for (Instruction& I : BB) {
				unsigned cur_opcode = I.getOpcode();
				if (cur_opcode == Instruction::IndirectBr) {
					contains_indirectbr[&BB] = true;
					contains_hazard[&BB] = true;
				}
				else if (cur_opcode == Instruction::Ret) {
					contains_rt[&BB] = true;
					contains_hazard[&BB] = true;
				}
				else if (cur_opcode == Instruction::CallBr || cur_opcode == Instruction::Invoke || cur_opcode == Instruction::Store) {
					contains_hazard[&BB] = true;
				}

				// store all conditional branches for later use
				else if (cur_opcode == Instruction::Br) {
					if (BranchInst* BI = dyn_cast<BranchInst>(&I)) {
						if (BI->isConditional()) {
							conditional_branches.push_back(&I);
						}
					}
				}
			}
		}

		// make predictions for conditional branches
		std::map<Instruction*, int> hazard_predicted;
		std::map<Instruction*, int> path_predicted;

		// first pass to deal with hazard heuristic
		for (Instruction* I : conditional_branches) {
			BranchInst* BI = dyn_cast<BranchInst>(I);
			errs() << *BI << "\n";
			// check first successor
			BasicBlock* first_child = BI->getSuccessor(0);
			if (contains_hazard[first_child]) {
				hazard_predicted[I] = 1;
				continue;
			}
			// check if first successor child yield to hazardous block unconditionally
			else {
				Instruction* first_child_terminator = first_child->getTerminator();
				if (BranchInst* first_child_terminator_B = dyn_cast<BranchInst>(first_child_terminator)) {
					if (first_child_terminator_B->isUnconditional()) {
						BasicBlock* first_child_child = first_child_terminator_B->getSuccessor(0);
						if (contains_hazard[first_child_child] && !PDT->dominates(first_child_terminator, I)) {
							hazard_predicted[I] = 1;
							continue;
						}
					}
				}
			}

			// check second successor
			BasicBlock* second_child = BI->getSuccessor(1);
			if (contains_hazard[second_child]) {
				hazard_predicted[I] = 0;
			}
			// check if first successor child yield to hazardous block unconditionally
			else {
				Instruction* second_child_terminator = second_child->getTerminator();
				if (BranchInst* second_child_terminator_B = dyn_cast<BranchInst>(second_child_terminator)) {
					if (second_child_terminator_B->isUnconditional()) {
						BasicBlock* second_child_child = second_child_terminator_B->getSuccessor(0);
						if (contains_hazard[second_child_child] && !PDT->dominates(second_child_terminator, I)) {
							hazard_predicted[I] = 0;
						}
					}
				}
			}
		}

		// // second pass to deal with path selection heuristic
		// for (Instruction* I : conditional_branches) {
		// 	// only predict branches not predicted by hazard heuristic
		// 	if (hazard_predicted.find(I) == hazard_predicted.end()) {
		//
		// 	}
		// }



		// grow blocks in loops
		auto loopVec_PreOrd = LI->getLoopsInPreorder();
		sort(loopVec_PreOrd.begin(), loopVec_PreOrd.end(), LoopDepthGt);
		for (auto* loop : loopVec_PreOrd) {
			// create BFS Traversal of basic blocks in this loop
			std::unordered_set<BasicBlock*> seen;
			std::vector<BasicBlock*> BFSorder;
			std::vector<BasicBlock*> queue;
			queue.insert(queue.begin(), loop->getHeader());
			seen.insert(loop->getHeader());
			BFSorder.push_back(loop->getHeader());
			while (!queue.empty()) {
				// left side queue entry, right side queue exit
				BasicBlock* cur_node = queue.back();
				for (BasicBlock* child : successors(cur_node)) {
					if (seen.find(child) == seen.end() && loop->contains(child)) {
						seen.insert(child);
						queue.insert(queue.begin(), child);
						BFSorder.push_back(child);
					}
				}
				queue.pop_back();
			}
			// process blocks in loops
			for (BasicBlock* cur_seed : BFSorder) {
				if (seen_in_trace.find(cur_seed) == seen_in_trace.end()) {
					auto cur_trace = growTrace(cur_seed, contains_indirectbr, contains_rt, hazard_predicted, path_predicted, seen_in_trace);
					res.push_back(cur_trace);
				}
			}
		}

		// grow remaining blocks in the function
		// create BFS Traversal of basic blocks in the function
		std::unordered_set<BasicBlock*> seen;
		std::vector<BasicBlock*> BFSorder;
		std::vector<BasicBlock*> queue;
		BasicBlock& entryBlock = F.getEntryBlock();
		queue.insert(queue.begin(), &entryBlock);
		seen.insert(&entryBlock);
		BFSorder.push_back(&entryBlock);

		// BFS starts
		while (!queue.empty()) {
			// left side queue entry, right side queue exit
			BasicBlock* cur_node = queue.back();
			for (BasicBlock* child : successors(cur_node)) {
				if (seen.find(child) == seen.end()) {
					seen.insert(child);
					queue.insert(queue.begin(), child);
					if (seen_in_trace.find(child) == seen_in_trace.end()) {
						BFSorder.push_back(child);
					}
				}
			}

			// pop from the queue
			queue.pop_back();
		}

		for (BasicBlock* cur_seed : BFSorder) {
			if (seen_in_trace.find(cur_seed) == seen_in_trace.end()) {
				auto cur_trace = growTrace(cur_seed, contains_indirectbr, contains_rt, hazard_predicted, path_predicted, seen_in_trace);
				// add cur trace to res
				res.push_back(cur_trace);
			}
		}
		return res;
	}

	std::vector<BasicBlock*> growTrace(
		BasicBlock* seed,
		std::map<BasicBlock*, bool>& contains_indirectbr,
		std::map<BasicBlock*, bool>& contains_rt,
		std::map<Instruction*, int>& hazard_predicted,
		std::map<Instruction*, int>& path_predicted,
		std::unordered_set<BasicBlock*>& seen_in_trace
	) {
		std::vector<BasicBlock*> res;
		res.push_back(seed);
		BasicBlock* cur_node = seed;
		while (true) {
			seen_in_trace.insert(cur_node);
			if (contains_indirectbr[cur_node]) {
				break;
			}
			if (contains_rt[cur_node]) {
				break;
			}
			// pick likely block

		}
		return res;
	}

	static bool LoopDepthGt(Loop* i, Loop* j) {
		return i->getLoopDepth() > j->getLoopDepth();
	}

}; // end of struct Hell
}  // end of anonymous namespace

char stats_collector::ID = 0;
static RegisterPass<stats_collector> X("stats_collector", "stats collector",
                             	false /* Only looks at CFG */,
                             	false /* Analysis Pass */);
