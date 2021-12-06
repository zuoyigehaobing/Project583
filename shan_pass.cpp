#include "llvm-c/Core.h"
#include "llvm/Pass.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.def"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Format.h"
#include "llvm/Analysis/LoopInfo.h"

#include <unordered_set>
#include <vector>
#include <algorithm>    // std::sort
using namespace llvm;

namespace {
struct HW1Pass : public FunctionPass {
	static char ID;
	HW1Pass() : FunctionPass(ID) {}

	void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.addRequired<LoopInfoWrapperPass>();
	}
	bool runOnFunction(Function &F) override {
		const char* main_name = "main";
		StringRef main_name_strRef(main_name);
		if (F.getName() == main_name_strRef){
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			auto Traces = traceFormation(&LI, F);
		}
		return false;
	}

	std::vector<std::vector<BasicBlock*>> traceFormation(LoopInfo* LI, Function& F) {
		std::vector<std::vector<BasicBlock*>> res;
		std::unordered_set<BasicBlock*> seen_in_trace;
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
          // add cur trace to res
          res.push_back(cur_trace);
				}
			}
		}
		// create BFS Traversal of basic blocks in the function
		std::unordered_set<BasicBlock*> seen;
		std::vector<BasicBlock*> BFSorder;
		std::vector<BasicBlock*> queue;

    for (Function::iterator b = F.begin(), be = F.end(); b != be; ++b) {
      BasicBlock* BB = &*b;
      if (seen_in_trace.find(BB) == seen_in_trace.end()){
        // Add the first BB into the queue
        queue.insert(queue.begin(), BB);
        seen.insert(BB);
        BFSorder.push_back(BB);
        break;
      }
    }

		// BFS starts
    while (!queue.empty()) {
      // left side queue entry, right side queue exit
      BasicBlock* cur_node = queue.back();
      for (BasicBlock* child : successors(cur_node)) {
        if (seen.find(child) == seen.end() && seen_in_trace.find(child) == seen_in_trace.end()) {
          seen.insert(child);
          queue.insert(queue.begin(), child);
          BFSorder.push_back(child);
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

char HW1Pass::ID = 0;
static RegisterPass<HW1Pass> X("HW1Pass", "stats collector",
                             	false /* Only looks at CFG */,
                             	false /* Analysis Pass */);
