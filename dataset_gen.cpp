#include "llvm/Pass.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.def"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/BranchProbability.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include <unordered_set>
#include <vector>
#include <algorithm>    // std::sort
#include <map>
#include <stdio.h>      /* printf, scanf, puts, NULL */
#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */
#include <fstream>

using namespace llvm;

std::ofstream ofile;


namespace {
struct dataset_gen : public FunctionPass {
	static char ID;
	dataset_gen() : FunctionPass(ID) {}


	void getAnalysisUsage(AnalysisUsage &AU) const {
		AU.addRequired<LoopInfoWrapperPass>();
		AU.addRequired<PostDominatorTreeWrapperPass>();
		AU.addRequired<DominatorTreeWrapperPass>();
		AU.addRequired<BlockFrequencyInfoWrapperPass>();
		AU.addRequired<BranchProbabilityInfoWrapperPass>();
	}
	bool runOnFunction(Function &F) override {
		LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
		PostDominatorTree& PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
		DominatorTree& DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
		BranchProbabilityInfo& BPI = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
		BlockFrequencyInfo& BFI = getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();

    std::map<BasicBlock*, bool> contains_hazard;
    for (BasicBlock& BB : F) {
      contains_hazard[&BB] = false;
      for (Instruction& I : BB) {
        unsigned cur_opcode = I.getOpcode();
        if (cur_opcode == Instruction::IndirectBr) {
          contains_hazard[&BB] = true;
        }
        else if (cur_opcode == Instruction::Ret) {
          contains_hazard[&BB] = true;
        }
        else if (cur_opcode == Instruction::CallBr || cur_opcode == Instruction::Invoke || cur_opcode == Instruction::Store) {
          contains_hazard[&BB] = true;
        }
      }
    }


    std::vector<BranchInst*> conditional_branches;
    for (BasicBlock& BB : F) {
      for (Instruction& I : BB) {
        if (BranchInst* BI = dyn_cast<BranchInst>(&I)) {
          if (BI->isConditional()) {
            conditional_branches.push_back(BI);
          }
        }
      }
    }

    uint64_t total_freq = 0;
    for (BranchInst* BI : conditional_branches) {
      BasicBlock* parent = BI->getParent();
      auto freq = BFI.getBlockProfileCount(parent).getValue();
      total_freq += freq;
    }


    ofile.open(F.getParent()->getSourceFileName() + ".csv", std::ios::app);

    for (BranchInst* BI : conditional_branches) {
      BasicBlock* parent = BI->getParent();
      auto freq = BFI.getBlockProfileCount(parent).getValue();
      double weight = double(freq)/total_freq;

      // features
      // pointers
      int is_pointer_cmp = 0;
      int is_pointer_eq = 0;

      Value* condition = BI->getCondition();

			if (CmpInst* CMPI = dyn_cast<CmpInst>(condition)) {
				Value* op1 = CMPI->getOperand(0);
				Value* op2 = CMPI->getOperand(1);
				if (op1->getType()->isPointerTy() && op2->getType()->isPointerTy()) {
          is_pointer_cmp = 1;
          if (CMPI->isEquality() && CMPI->isTrueWhenEqual()) {
            is_pointer_eq = 0;
          }
        }
      }
      // loop
      int is_taken_loop = 0;
      int is_fall_through_loop = 0;

      BasicBlock* successor1 = BI->getSuccessor(0);
      BasicBlock* successor2 = BI->getSuccessor(1);

      if (LI.getLoopFor(successor1)){
        is_taken_loop = 1;
      }
      if (LI.getLoopFor(successor2)) {
        is_fall_through_loop = 1;
      }

      // opcode
      int is_ifcmp = 0;
      int is_ifcmp_lt_zero = 0;
      int is_ifcmp_gt_zero = 0;
      int is_ifcmp_eq_zero = 0;
      int is_ifcmp_ne_zero = 0;
      int is_ifcmp_le_zero = 0;
      int is_ifcmp_ge_zero = 0;

      int is_ifcmp_lt_negative = 0;
      int is_ifcmp_gt_negative = 0;
      int is_ifcmp_eq_negative = 0;
      int is_ifcmp_ne_negative = 0;
      int is_ifcmp_le_negative = 0;
      int is_ifcmp_ge_negative = 0;

      int is_fcmp_eq = 0;

      if (CmpInst* CMPI = dyn_cast<CmpInst>(condition)) {
        Value* op1 = CMPI->getOperand(0);
        Value* op2 = CMPI->getOperand(1);

        if (isa<Constant>(op1) && !isa<Constant>(op2)) {
          bool isZero = false;
          bool isNegative = false;
          if (isa<ConstantInt>(op1)) {
            ConstantInt* cop1 = cast<ConstantInt>(op1);
            isZero = cop1->isZero();
            isNegative = cop1->isNegative();
          }
          else if (isa<ConstantFP>(op1)) {
            ConstantFP* cop1 = cast<ConstantFP>(op1);
            isZero = cop1->isZero();
            isNegative = cop1->isNegative();
          }
          CmpInst::Predicate p = CMPI->getPredicate();
          if (isZero) {
            is_ifcmp_gt_zero = (p == CmpInst::FCMP_OLT || p == CmpInst::FCMP_ULT || p == CmpInst::ICMP_ULT || p == CmpInst::ICMP_SLT);
            is_ifcmp_lt_zero = (p == CmpInst::FCMP_OGT || p == CmpInst::FCMP_UGT || p == CmpInst::ICMP_UGT || p == CmpInst::ICMP_SGT);
            is_ifcmp_eq_zero = (p == CmpInst::FCMP_OEQ || p == CmpInst::FCMP_UEQ || p == CmpInst::ICMP_EQ);
            is_ifcmp_ne_zero = (p == CmpInst::FCMP_ONE || p == CmpInst::FCMP_UNE || p == CmpInst::ICMP_NE);
            is_ifcmp_ge_zero = (p == CmpInst::FCMP_OLE || p == CmpInst::FCMP_ULE || p == CmpInst::ICMP_ULE || p == CmpInst::ICMP_SLE);
            is_ifcmp_le_zero = (p == CmpInst::FCMP_OGE || p == CmpInst::FCMP_UGE || p == CmpInst::ICMP_UGE || p == CmpInst::ICMP_SGE);
          }
          if (isNegative) {
            is_ifcmp_gt_negative = (p == CmpInst::FCMP_OLT || p == CmpInst::FCMP_ULT || p == CmpInst::ICMP_ULT || p == CmpInst::ICMP_SLT);
            is_ifcmp_lt_negative = (p == CmpInst::FCMP_OGT || p == CmpInst::FCMP_UGT || p == CmpInst::ICMP_UGT || p == CmpInst::ICMP_SGT);
            is_ifcmp_eq_negative = (p == CmpInst::FCMP_OEQ || p == CmpInst::FCMP_UEQ || p == CmpInst::ICMP_EQ);
            is_ifcmp_ne_negative = (p == CmpInst::FCMP_ONE || p == CmpInst::FCMP_UNE || p == CmpInst::ICMP_NE);
            is_ifcmp_ge_negative = (p == CmpInst::FCMP_OLE || p == CmpInst::FCMP_ULE || p == CmpInst::ICMP_ULE || p == CmpInst::ICMP_SLE);
            is_ifcmp_le_negative = (p == CmpInst::FCMP_OGE || p == CmpInst::FCMP_UGE || p == CmpInst::ICMP_UGE || p == CmpInst::ICMP_SGE);
          }
        }

        else if (isa<Constant>(op2) && !isa<Constant>(op1)) {
          bool isZero = false;
          bool isNegative = false;
          if (isa<ConstantInt>(op2)) {
            ConstantInt* cop2 = cast<ConstantInt>(op2);
            isZero = cop2->isZero();
            isNegative = cop2->isNegative();
          }
          else if (isa<ConstantFP>(op2)) {
            ConstantFP* cop2 = cast<ConstantFP>(op2);
            isZero = cop2->isZero();
            isNegative = cop2->isNegative();
          }
          CmpInst::Predicate p = CMPI->getPredicate();
          if (isZero) {
            is_ifcmp_lt_zero = (p == CmpInst::FCMP_OLT || p == CmpInst::FCMP_ULT || p == CmpInst::ICMP_ULT || p == CmpInst::ICMP_SLT);
            is_ifcmp_gt_zero = (p == CmpInst::FCMP_OGT || p == CmpInst::FCMP_UGT || p == CmpInst::ICMP_UGT || p == CmpInst::ICMP_SGT);
            is_ifcmp_eq_zero = (p == CmpInst::FCMP_OEQ || p == CmpInst::FCMP_UEQ || p == CmpInst::ICMP_EQ);
            is_ifcmp_ne_zero = (p == CmpInst::FCMP_ONE || p == CmpInst::FCMP_UNE || p == CmpInst::ICMP_NE);
            is_ifcmp_le_zero = (p == CmpInst::FCMP_OLE || p == CmpInst::FCMP_ULE || p == CmpInst::ICMP_ULE || p == CmpInst::ICMP_SLE);
            is_ifcmp_ge_zero = (p == CmpInst::FCMP_OGE || p == CmpInst::FCMP_UGE || p == CmpInst::ICMP_UGE || p == CmpInst::ICMP_SGE);
          }
          if (isNegative) {
            is_ifcmp_lt_negative = (p == CmpInst::FCMP_OLT || p == CmpInst::FCMP_ULT || p == CmpInst::ICMP_ULT || p == CmpInst::ICMP_SLT);
            is_ifcmp_gt_negative = (p == CmpInst::FCMP_OGT || p == CmpInst::FCMP_UGT || p == CmpInst::ICMP_UGT || p == CmpInst::ICMP_SGT);
            is_ifcmp_eq_negative = (p == CmpInst::FCMP_OEQ || p == CmpInst::FCMP_UEQ || p == CmpInst::ICMP_EQ);
            is_ifcmp_ne_negative = (p == CmpInst::FCMP_ONE || p == CmpInst::FCMP_UNE || p == CmpInst::ICMP_NE);
            is_ifcmp_le_negative = (p == CmpInst::FCMP_OLE || p == CmpInst::FCMP_ULE || p == CmpInst::ICMP_ULE || p == CmpInst::ICMP_SLE);
            is_ifcmp_ge_negative = (p == CmpInst::FCMP_OGE || p == CmpInst::FCMP_UGE || p == CmpInst::ICMP_UGE || p == CmpInst::ICMP_SGE);
          }
        }

        CmpInst::Predicate p = CMPI->getPredicate();
        if (p == CmpInst::FCMP_OEQ || p == CmpInst::FCMP_UEQ) {
          is_fcmp_eq = 1;
        }
      }

      // guard
      int is_op1_used_taken = 0;
      int is_op1_used_fall_through = 0;
      int is_op2_used_taken = 0;
      int is_op2_used_fall_through = 0;

      if (CmpInst* CMPI = dyn_cast<CmpInst>(condition)) {
        Value* op1 = CMPI->getOperand(0);
        Value* op2 = CMPI->getOperand(1);
        for (auto U: op1->users()) {
          if (Instruction* UI = dyn_cast<Instruction>(U)) {
            if (UI->getParent() == successor1) {
              is_op1_used_taken = 1;
            }
            if (UI->getParent() == successor2) {
              is_op1_used_fall_through = 1;
            }
          }
        }

        for (auto U: op2->users()) {
          if (Instruction* UI = dyn_cast<Instruction>(U)) {
            if (UI->getParent() == successor1) {
              is_op2_used_taken = 1;
            }
            if (UI->getParent() == successor2) {
              is_op2_used_fall_through = 1;
            }
          }
        }
      }

      // direction
      int is_taken_backward = 0;
      int is_fall_through_backward = 0;

      if (DT.dominates(successor1->getTerminator(), BI)) {
        is_taken_backward = 1;
      }
      if (DT.dominates(successor2->getTerminator(), BI)) {
        is_fall_through_backward = 1;
      }

      // hazard
      int has_taken_call = 0;
      int has_taken_invoke = 0;
      int has_taken_store = 0;
      int has_taken_ret = 0;
      int has_taken_indirectbr = 0;
      // yield to hazard
      int has_taken_yield = 0;
      int is_taken_pdom = 0;

      int has_fall_through_call = 0;
      int has_fall_through_invoke = 0;
      int has_fall_through_store = 0;
      int has_fall_through_ret = 0;
      int has_fall_through_indirectbr = 0;
      // yield to hazard
      int has_fall_through_yield = 0;
      int is_fall_through_pdom = 0;

      for (Instruction& I : *successor1) {
        unsigned cur_opcode = I.getOpcode();
				has_taken_call = cur_opcode == Instruction::CallBr;
        has_taken_invoke = cur_opcode == Instruction::Invoke;
        has_taken_store = cur_opcode == Instruction::Store;
        has_taken_ret = cur_opcode == Instruction::Ret;
        has_taken_indirectbr = cur_opcode == Instruction::IndirectBr;
      }
      Instruction* successor1_terminator = successor1->getTerminator();
      if (isa<BranchInst>(successor1_terminator)) {
        BranchInst* successor1_terminator_BI = cast<BranchInst>(successor1_terminator);
        if (successor1_terminator_BI->isUnconditional()) {
          BasicBlock* temp_bb = successor1_terminator_BI->getSuccessor(0);
          if (contains_hazard[temp_bb]) {
            has_taken_yield = 1;
          }
        }
      }
      is_taken_pdom = PDT.dominates(successor1->getTerminator(), BI);

      for (Instruction& I : *successor2) {
        unsigned cur_opcode = I.getOpcode();
        has_fall_through_call = cur_opcode == Instruction::CallBr;
        has_fall_through_invoke = cur_opcode == Instruction::Invoke;
        has_fall_through_store = cur_opcode == Instruction::Store;
        has_fall_through_ret = cur_opcode == Instruction::Ret;
        has_fall_through_indirectbr = cur_opcode == Instruction::IndirectBr;
      }
      Instruction* successor2_terminator = successor2->getTerminator();
      if (isa<BranchInst>(successor2_terminator)) {
        BranchInst* successor2_terminator_BI = cast<BranchInst>(successor2_terminator);
        if (successor2_terminator_BI->isUnconditional()) {
          BasicBlock* temp_bb = successor2_terminator_BI->getSuccessor(0);
          if (contains_hazard[temp_bb]) {
            has_fall_through_yield = 1;
          }
        }
      }
      is_fall_through_pdom = PDT.dominates(successor2->getTerminator(), BI);

      int label = 0;
      auto threshold = BranchProbability::getBranchProbability(1,2);
      for (int i = 0; i < 2; i++) {
				auto prob = BPI.getEdgeProbability(parent, i);
				if (prob > threshold) {
					label = i;
					break;
				}
			}

      // for (int i = 0; i < weight*1000; i++) {
        ofile << is_pointer_cmp << ",";
        ofile << is_pointer_eq << ",";
        ofile << is_taken_loop << ",";
        ofile << is_fall_through_loop << ",";
        ofile << is_ifcmp << ",";
        ofile << is_ifcmp_lt_zero << ",";
        ofile << is_ifcmp_gt_zero << ",";
        ofile << is_ifcmp_eq_zero << ",";
        ofile << is_ifcmp_ne_zero << ",";
        ofile << is_ifcmp_le_zero << ",";
        ofile << is_ifcmp_ge_zero << ",";
        ofile << is_ifcmp_lt_negative << ",";
        ofile << is_ifcmp_gt_negative << ",";
        ofile << is_ifcmp_eq_negative << ",";
        ofile << is_ifcmp_ne_negative << ",";
        ofile << is_ifcmp_le_negative << ",";
        ofile << is_ifcmp_ge_negative << ",";
        ofile << is_fcmp_eq << ",";
        ofile << is_op1_used_taken << ",";
        ofile << is_op1_used_fall_through << ",";
        ofile << is_op2_used_taken << ",";
        ofile << is_op2_used_fall_through << ",";
        ofile << is_taken_backward << ",";
        ofile << is_fall_through_backward << ",";
        ofile << has_taken_call << ",";
        ofile << has_taken_invoke << ",";
        ofile << has_taken_store << ",";
        ofile << has_taken_ret << ",";
        ofile << has_taken_indirectbr << ",";
        ofile << has_taken_yield << ",";
        ofile << is_taken_pdom << ",";
        ofile << has_fall_through_call << ",";
        ofile << has_fall_through_invoke << ",";
        ofile << has_fall_through_store << ",";
        ofile << has_fall_through_ret << ",";
        ofile << has_fall_through_indirectbr << ",";
        ofile << has_fall_through_yield << ",";
        ofile << is_fall_through_pdom << ",";
        ofile << label << "\n";
      // }
    }

    ofile.close();
		return false;
	}


}; // end of struct Hell
}  // end of anonymous namespace

char dataset_gen::ID = 0;
static RegisterPass<dataset_gen> X("dataset_gen", "dataset generation",
                             	false /* Only looks at CFG */,
                             	false /* Analysis Pass */);
