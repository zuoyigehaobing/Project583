#include "llvm/Pass.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
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
	}

	std::vector<std::vector<BasicBlock*>> traceFormation(LoopInfo* LI, PostDominatorTree* PDT, Function& F) {
		// res is the 2d vector of traces
		std::vector<std::vector<BasicBlock*>> res;
		std::unordered_set<BasicBlock*> seen_in_trace;

		// before growing trace with seed, identify basic blocks with hazardous instructions
		std::map<BasicBlock*, bool> contains_hazard;
		std::unordered_set<unsigned> hazardous_opcodes = {
			Instruction::CallBr,
			Instruction::Invoke,
			Instruction::Ret,
			Instruction::IndirectBr,
		}
		for (BasicBlock& BB : F) {
			for (Instruction& I : BB) {
				unsigned cur_opcode = I.getOpcode();
				if (hazardous_opcodes.count(cur_opcode)) {
					contains_hazard[&BB] = true;
				}
				else if (cur_opcode == Instruction::Store) {
					//dyn_cast pointer argument to Instruction, check if it is getelementptr
				}
			}
		}


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
					auto cur_trace = growTrace(cur_seed, seen_in_trace);
					res.insert(res.begin(),cur_trace);
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
				auto cur_trace = growTrace(cur_seed, seen_in_trace);
				// add cur trace to res
				res.push_back(cur_trace);
			}
		}
		return res;
	}

	std::vector<BasicBlock*> growTrace(BasicBlock* seed, std::unordered_set<BasicBlock*> seen) {
		 std::vector<BasicBlock*> res;
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
