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
using namespace llvm;

namespace {
struct stats_collector : public FunctionPass {
	static char ID;
	stats_collector() : FunctionPass(ID) {}

	void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.addRequired<LoopInfoWrapperPass>();
	}
	bool runOnFunction(Function &F) override {
		const char* main_name = "main";
		StringRef main_name_strRef(main_name);
		if (F.getName() == main_name_strRef){
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			auto Traces = traceFormation(&LI);
		}
		return false;
	}

	std::vector<std::vector<BasicBlock*>> traceFormation(LoopInfo* LI) {
		std::vector<std::vector<BasicBlock*>> res;
		std::unordered_set<BasicBlock*> seen;
		auto loopVec_PreOrd = LI->getLoopsInPreorder();
		return res;
	}

	std::vector<BasicBlock*> growTrace(BasicBlock* seed, std::unordered_set<BasicBlock*> seen) {
		std::vector<BasicBlock*> res;
		return res;
	}

}; // end of struct Hell
}  // end of anonymous namespace

char stats_collector::ID = 0;
static RegisterPass<stats_collector> X("stats_collector", "stats collector",
                             	false /* Only looks at CFG */,
                             	false /* Analysis Pass */);
