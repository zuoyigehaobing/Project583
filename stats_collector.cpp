#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.def"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/BranchProbability.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"

#include <unordered_set>
using namespace llvm;

namespace {
struct stats_collector : public FunctionPass {
	static char ID;
	stats_collector() : FunctionPass(ID) {}
	
	void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.addRequired<llvm::BlockFrequencyInfoWrapperPass>();
		AU.addRequired<BranchProbabilityInfoWrapperPass>();
	}
	bool runOnFunction(Function &F) override {
    		BranchProbabilityInfo &bpi = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
		BlockFrequencyInfo &bfi = getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
		uint64_t DynOpCounts = 0;
		// 0 : IALU, 1 : FALU, 2 : MEM, 3 : Biased-Branch, 4 : Unbiased-Branch, 5: Others
		uint64_t CatCounts[6] = {0};
		std::unordered_set<unsigned> IALU_set = {
			Instruction::Add,
			Instruction::Sub,
			Instruction::Mul,
			Instruction::UDiv,
			Instruction::SDiv,
			Instruction::URem,
			Instruction::Shl,
			Instruction::LShr,
			Instruction::AShr,
			Instruction::And,
			Instruction::Or,
			Instruction::Xor,
			Instruction::ICmp,
			Instruction::SRem
		};
		std::unordered_set<unsigned> FALU_set = {
			Instruction::FAdd,
			Instruction::FSub,
			Instruction::FMul,
			Instruction::FDiv,
			Instruction::FRem,
			Instruction::FCmp
		};
		std::unordered_set<unsigned> MEM_set = {
			Instruction::Alloca,
			Instruction::Load,
			Instruction::Store,
			Instruction::GetElementPtr,
			Instruction::Fence,
			Instruction::AtomicCmpXchg,
			Instruction::AtomicRMW
		};
		std::unordered_set<unsigned> BR_set = {
			Instruction::Br,
			Instruction::Switch,
			Instruction::IndirectBr,
		};
		for (BasicBlock &BB : F) {
			uint64_t blockCount = bfi.getBlockProfileCount(&BB).getValue();
			
			for (Instruction &I : BB) {
				unsigned Icode = I.getOpcode();
				if (IALU_set.count(Icode)) {
					CatCounts[0] += blockCount;
				}
				else if (FALU_set.count(Icode)) {
					CatCounts[1] += blockCount;
				}
				else if (MEM_set.count(Icode)) {
					CatCounts[2] += blockCount;
				}
				
				else if (BR_set.count(Icode)) {
					unsigned numSuccessors = I.getNumSuccessors();
					auto maxProb = BranchProbability::getZero();
					for (unsigned i = 0; i < numSuccessors; ++i) {
						auto prob = bpi.getEdgeProbability(&BB, i);
						if (prob > maxProb) {
							maxProb = prob;
						}
					}
					if (maxProb > BranchProbability(4,5)) {
						CatCounts[3] += blockCount;
					}
					else {
						CatCounts[4] += blockCount;
					}
				}
				else {
					CatCounts[5] += blockCount;
				}
				DynOpCounts += blockCount;
			}
		}
		errs() << F.getName();
		errs() << ", " << DynOpCounts;
		for (int i = 0; i < 6; ++i) {
			if (DynOpCounts == 0) errs() << ", " << format("%.3f", CatCounts[i]);
			else errs() << ", " << format("%.3f", double(CatCounts[i])/DynOpCounts);
		}
		errs() << "\n";
    	return false;
	}
}; // end of struct Hell
}  // end of anonymous namespace

char stats_collector::ID = 0;
static RegisterPass<stats_collector> X("stats_collector", "stats collector",
                             	false /* Only looks at CFG */,
                             	false /* Analysis Pass */);
