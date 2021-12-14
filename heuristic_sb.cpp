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

using namespace llvm;

int glb_hazard_count = 0;
int glb_hazard_agree = 0;
int glb_path_count = 0;
int glb_path_agree = 0;
int glb_conditional_count = 0;


namespace {
struct heuristic_sb : public FunctionPass {
	static char ID;
	heuristic_sb() : FunctionPass(ID) {}


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
		srand(time(NULL));
		auto Traces = traceFormation(&LI, &PDT, &DT, &BPI, &BFI, F);

		// errs() << "----traces formed----" << "\n";
		// for (auto trace : Traces) {
		// 	errs() << "----start of trace----\n";
		// 	for (auto bb : trace) {
		// 		errs() << *bb << "\n";
		// 		errs() << "--------\n";
		// 	}
		// 	errs() << "----end of trace----\n";
		// }
		//
		// int count = 0;
		// std::map<BasicBlock*, int> tracemap;
		// for (auto trace : Traces) {
		// 	for (BasicBlock* bb : trace) {
		// 		tracemap[bb] = count;
		// 	}
		// 	count += 1;
		// }
		//
		// bool res = tailDuplication(Traces, tracemap, &F);
		// errs() << "modified in tail duplication: " << res << "\n";
		// return res;
		return false;
	}

	std::vector<std::vector<BasicBlock*>> traceFormation(
		LoopInfo* LI,
		PostDominatorTree* PDT,
		DominatorTree* DT,
		BranchProbabilityInfo* BPI,
		BlockFrequencyInfo* BFI,
		Function& F
		) {
		// res is the 2d vector of traces
		std::vector<std::vector<BasicBlock*>> res;
		std::unordered_set<BasicBlock*> seen_in_trace;

		// identify basic blocks with hazardous instructions
		std::map<BasicBlock*, bool> contains_hazard;
		std::map<BasicBlock*, bool> contains_indirectbr;
		std::map<BasicBlock*, bool> contains_rt;
		// store all possible conditional branches for later use
		std::vector<BranchInst*> conditional_branches;

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
							conditional_branches.push_back(BI);
						}
					}
				}
			}
		}

		// make predictions for conditional branches
		std::map<BranchInst*, int> hazard_predicted;
		std::map<BranchInst*, int> path_predicted;

		// first pass to deal with hazard heuristic
		for (BranchInst* BI : conditional_branches) {
			bool avoid_first = false;
			bool avoid_second = false;
			// check first successor
			BasicBlock* first_child = BI->getSuccessor(0);
			if (contains_hazard[first_child]) {
				avoid_first = true;
				// old version
				// hazard_predicted[BI] = 1;
				// continue;
			}
			// check if first successor child yield to hazardous block unconditionally
			else {
				Instruction* first_child_terminator = first_child->getTerminator();
				if (BranchInst* first_child_terminator_B = dyn_cast<BranchInst>(first_child_terminator)) {
					if (first_child_terminator_B->isUnconditional()) {
						BasicBlock* first_child_child = first_child_terminator_B->getSuccessor(0);
						if (contains_hazard[first_child_child] && !PDT->dominates(first_child_terminator, BI)) {
							avoid_first = true;
							// hazard_predicted[BI] = 1;
							// continue;
						}
					}
				}
			}

			// check second successor
			BasicBlock* second_child = BI->getSuccessor(1);
			if (contains_hazard[second_child]) {
				avoid_second = true;
				// hazard_predicted[BI] = 0;
			}
			// check if first successor child yield to hazardous block unconditionally
			else {
				Instruction* second_child_terminator = second_child->getTerminator();
				if (BranchInst* second_child_terminator_B = dyn_cast<BranchInst>(second_child_terminator)) {
					if (second_child_terminator_B->isUnconditional()) {
						BasicBlock* second_child_child = second_child_terminator_B->getSuccessor(0);
						if (contains_hazard[second_child_child] && !PDT->dominates(second_child_terminator, BI)) {
							avoid_second = true;
							// hazard_predicted[BI] = 0;
						}
					}
				}
			}

			// new version
			// only apply heuristic when xor is true
			if (avoid_first != avoid_second) {
				if (avoid_first) {
					hazard_predicted[BI] = 1;
				}
				else {
					hazard_predicted[BI] = 0;
				}
			}
		}

		// use a vector of vector to deal with related branches later
		std::vector<std::vector<BranchInst*>> path_heuristic_inst(5);
		std::unordered_set<BranchInst*> already_sorted_relation;
		// second pass to deal with path selection heuristic
		for (BranchInst* BI : conditional_branches) {
			// only predict branches not predicted by hazard heuristic
			if (hazard_predicted.find(BI) != hazard_predicted.end()) {
				continue;
			}

			Value* condition = BI->getCondition();
			if (CmpInst* CMPI = dyn_cast<CmpInst>(condition)) {
				Value* op1 = CMPI->getOperand(0);
				Value* op2 = CMPI->getOperand(1);

				// case 0 pointer heuristic
				// check if both operands are pointer
				if (op1->getType()->isPointerTy() && op2->getType()->isPointerTy()) {
					// pointers are not likely to be null
					// pointers are not likely to be equal
					// if not the same operand
					if (op1 != op2) {
						// eq gte lte
						if (CMPI->isTrueWhenEqual()) {
							// eq should fall through
							if (CMPI->isEquality()) {
								path_predicted[BI] = 1;
							}
							// gte, lte should be taken
							else {
								path_predicted[BI] = 0;
							}
						}
						// ne gt lt
						else {
							path_predicted[BI] = 0;
						}
						path_heuristic_inst[0].push_back(BI);
						continue;
					}
				}

				// case 1 loop heuristic
				BasicBlock* successor1 = BI->getSuccessor(0);
				BasicBlock* successor2 = BI->getSuccessor(1);
				// if one of them is in a loop
				if (!(LI->getLoopFor(successor1)) != !(LI->getLoopFor(successor2))) {
					if (LI->getLoopFor(successor1)) {
						path_predicted[BI] = 0;
					}
					else {
						path_predicted[BI] = 1;
					}
					path_heuristic_inst[1].push_back(BI);
					continue;
				}

				// case 2 opcode heuristic
				// negative numbers are unlikely
				// xor constant
				if (isa<Constant>(op1) != isa<Constant>(op2)) {
					if (isa<ConstantInt>(op1) || isa<ConstantFP>(op1)) {
						bool isNegative = false;
						bool isZero = false;
						if (isa<ConstantInt>(op1)) {
							ConstantInt* cop1 = dyn_cast<ConstantInt>(op1);
							isNegative = cop1->isNegative();
							isZero = cop1->isZero();
						}
						else {
							ConstantFP* cop1 = dyn_cast<ConstantFP>(op1);
							isNegative = cop1->isNegative();
							isZero = cop1->isZero();
						}
						if (isNegative) {
							// eq
							if (CMPI->isTrueWhenEqual() && CMPI->isEquality()) {
								path_predicted[BI] = 1;
								path_heuristic_inst[2].push_back(BI);
								continue;
							}
							// not eq nor ne
							else if (CMPI->isRelational()) {
								CmpInst::Predicate p = CMPI->getPredicate();
								if (
									p == CmpInst::FCMP_OGE ||
									p == CmpInst::FCMP_UGE ||
									p == CmpInst::ICMP_UGE ||
									p == CmpInst::ICMP_SGE ||
									p == CmpInst::FCMP_OGT ||
									p == CmpInst::FCMP_UGT ||
									p == CmpInst::ICMP_UGT ||
									p == CmpInst::ICMP_SGT
								) {
									path_predicted[BI] = 1;
									path_heuristic_inst[2].push_back(BI);
									continue;
								}
							}
						}
						if (isZero) {
							if (CMPI->isRelational()) {
								CmpInst::Predicate p = CMPI->getPredicate();
								if (
									p == CmpInst::FCMP_OGT ||
									p == CmpInst::FCMP_UGT ||
									p == CmpInst::ICMP_UGT ||
									p == CmpInst::ICMP_SGT
								) {
									path_predicted[BI] = 1;
									path_heuristic_inst[2].push_back(BI);
									continue;
								}
							}
						}
					}
					else if (isa<ConstantInt>(op2) || isa<ConstantFP>(op2)) {
						bool isNegative = false;
						bool isZero = false;
						if (isa<ConstantInt>(op2)) {
							ConstantInt* cop2 = dyn_cast<ConstantInt>(op2);
							isNegative = cop2->isNegative();
							isZero = cop2->isZero();
						}
						else {
							ConstantFP* cop2 = dyn_cast<ConstantFP>(op2);
							isNegative = cop2->isNegative();
							isZero = cop2->isZero();
						}
						if (isNegative) {
							// eq
							if (CMPI->isTrueWhenEqual() && CMPI->isEquality()) {
								path_predicted[BI] = 1;
								path_heuristic_inst[2].push_back(BI);
								continue;
							}
							// not eq nor ne
							else if (CMPI->isRelational()) {
								CmpInst::Predicate p = CMPI->getPredicate();
								if (
									p == CmpInst::FCMP_OLE ||
									p == CmpInst::FCMP_ULE ||
									p == CmpInst::ICMP_ULE ||
									p == CmpInst::ICMP_SLE ||
									p == CmpInst::FCMP_OLT ||
									p == CmpInst::FCMP_ULT ||
									p == CmpInst::ICMP_ULT ||
									p == CmpInst::ICMP_SLT
								) {
									path_predicted[BI] = 1;
									path_heuristic_inst[2].push_back(BI);
									continue;
								}
							}
						}
						if (isZero) {
							if (CMPI->isRelational()) {
								CmpInst::Predicate p = CMPI->getPredicate();
								if (
									p == CmpInst::FCMP_OLT ||
									p == CmpInst::FCMP_ULT ||
									p == CmpInst::ICMP_ULT ||
									p == CmpInst::ICMP_SLT
								) {
									path_predicted[BI] = 1;
									path_heuristic_inst[2].push_back(BI);
									continue;
								}
							}
						}
					}
				}
				// floating point comparison are unlikely to be equal
				if (isa<FCmpInst>(CMPI)) {
					FCmpInst* FCMP = dyn_cast<FCmpInst>(CMPI);
					if (FCMP->isEquality()) {
						//eq
						if (FCMP->isTrueWhenEqual()) {
							path_predicted[BI] = 1;
						}
						//ne
						else {
							path_predicted[BI] = 0;
						}
					}
					// can extend this beyound equality branches
					// else {
					// 	path_predicted[BI] = 0;
					// }
					path_heuristic_inst[2].push_back(BI);
				}

				// case 3 guard heuristic
				bool guard_op1 = false;
				int guard_op1_dir = 0;
				bool guard_op2 = false;
				int guard_op2_dir = 0;

				bool guard_first = false;
				bool guard_second = false;
				for (auto U: op1->users()) {
					if (Instruction* UI = dyn_cast<Instruction>(U)) {
						if ((UI->getParent() == successor1) && !PDT->dominates(successor1->getTerminator(), BI)) {
							guard_first = true;
						}
						if ((UI->getParent() == successor2) && !PDT->dominates(successor2->getTerminator(), BI)) {
							guard_second = true;
						}
					}
				}

				if (guard_first != guard_second) {
					guard_op1 = true;
					if (guard_first) {
						guard_op1_dir = 0;
					}
					else {
						guard_op1_dir = 1;
					}
				}

				guard_first = false;
				guard_second = false;
				for (auto U: op2->users()) {
					if (Instruction* UI = dyn_cast<Instruction>(U)) {
						if ((UI->getParent() == successor1) && !PDT->dominates(successor1->getTerminator(), BI)) {
							guard_first = true;
						}
						if ((UI->getParent() == successor2) && !PDT->dominates(successor2->getTerminator(), BI)) {
							guard_second = true;
						}
					}
				}
				if (guard_first != guard_second) {
					guard_op2 = true;
					if (guard_first) {
						guard_op2_dir = 0;
					}
					else {
						guard_op2_dir = 1;
					}
				}
				if (guard_op1 != guard_op2) {
					if (guard_op1) {
						if (guard_op1_dir == 0) {
							path_predicted[BI] = 0;
							path_heuristic_inst[3].push_back(BI);
							continue;
						}
						else {
							path_predicted[BI] = 1;
							path_heuristic_inst[3].push_back(BI);
							continue;
						}
					}
					else {
						if (guard_op2_dir == 0) {
							path_predicted[BI] = 0;
							path_heuristic_inst[3].push_back(BI);
							continue;
						}
						else {
							path_predicted[BI] = 1;
							path_heuristic_inst[3].push_back(BI);
							continue;
						}
					}
				}




				// case 4 branch direction heuristic
				if (DT->dominates(successor1->getTerminator(), BI) && !DT->dominates(successor2->getTerminator(), BI)) {
					path_predicted[BI] = 0;
					path_heuristic_inst[4].push_back(BI);
					continue;
				}
				if (DT->dominates(successor2->getTerminator(), BI) && !DT->dominates(successor1->getTerminator(), BI)) {
					path_predicted[BI] = 1;
					path_heuristic_inst[4].push_back(BI);
					continue;
				}
			}
		}

		// resolve related branches and take unresolved and the most predictive heuristic predicted branch as the standard
		// same operand order

		// if standard is =, then !=, < and > need to be flipped
		// if standard is !=, then = need to be flipped
		// if standard is > then <, <=, = need to be flipped
		// if standard is < then >, >=, = need to be flipped
		// if standard is >= then <, != need to be flipped
		// if standard is <= then >, != need to be flipped

		// flipped = take opposite direction as standard
		// the remaining cases are not flipped, but need to take the same direction as standard
		for (int i = 0; i < 5; i++) {
			for (BranchInst* standard_BI : path_heuristic_inst[i]) {
				// skip already sorted
				if (already_sorted_relation.find(standard_BI) != already_sorted_relation.end()) {
					continue;
				}
				Value* condition = standard_BI->getCondition();
				CmpInst* CMPI = cast<CmpInst>(condition);
				Value* op1 = CMPI->getOperand(0);
				Value* op2 = CMPI->getOperand(1);
				CmpInst::Predicate p = CMPI->getPredicate();

				for (int j = i + 1; j < 5; j++) {
					for (BranchInst* candidate_BI : path_heuristic_inst[j]) {
						// skip already sorted
						if (already_sorted_relation.find(candidate_BI) != already_sorted_relation.end()) {
							continue;
						}
						Value* candidate_condition = candidate_BI->getCondition();
						CmpInst* candidate_CMPI = cast<CmpInst>(candidate_condition);
						Value* candidate_op1 = candidate_CMPI->getOperand(0);
						Value* candidate_op2 = candidate_CMPI->getOperand(1);
						CmpInst::Predicate candidate_p = candidate_CMPI->getPredicate();
						if ((op1 == candidate_op1) && (op2 == candidate_op2) || (op1 == candidate_op2) && (op2 == candidate_op1) ) {
							bool flip = false;
							// if standard is =, then !=, < and > need to be flipped
							if ((p == CmpInst::FCMP_OEQ || p == CmpInst::FCMP_UEQ || p == CmpInst::ICMP_EQ)
							&& (
								candidate_p == CmpInst::FCMP_ONE ||
								candidate_p == CmpInst::FCMP_UNE ||
								candidate_p == CmpInst::ICMP_NE ||
								candidate_p == CmpInst::FCMP_OGT ||
								candidate_p == CmpInst::FCMP_UGT ||
								candidate_p == CmpInst::ICMP_UGT ||
								candidate_p == CmpInst::ICMP_SGT ||
								candidate_p == CmpInst::FCMP_OLT ||
								candidate_p == CmpInst::FCMP_ULT ||
								candidate_p == CmpInst::ICMP_ULT ||
								candidate_p == CmpInst::ICMP_SLT
							)) {
								flip = true;
							}
							// if standard is !=, then = need to be flipped
							if ((p == CmpInst::FCMP_ONE || p == CmpInst::FCMP_UNE || p == CmpInst::ICMP_NE)
							&& (
								candidate_p == CmpInst::FCMP_OEQ ||
								candidate_p == CmpInst::FCMP_UEQ ||
								candidate_p == CmpInst::ICMP_EQ
							)) {
								flip = true;
							}
							// if standard is > then <, <=, = need to be flipped
							if (p == CmpInst::FCMP_OGT || p == CmpInst::FCMP_UGT || p == CmpInst::ICMP_UGT || p == CmpInst::ICMP_SGT) {
								if (((op1 == candidate_op1) && (op2 == candidate_op2))
								&&(
									candidate_p == CmpInst::FCMP_OLT ||
									candidate_p == CmpInst::FCMP_ULT ||
									candidate_p == CmpInst::ICMP_ULT ||
									candidate_p == CmpInst::ICMP_SLT ||
									candidate_p == CmpInst::FCMP_OLE ||
									candidate_p == CmpInst::FCMP_ULE ||
									candidate_p == CmpInst::ICMP_ULE ||
									candidate_p == CmpInst::ICMP_SLE ||
									candidate_p == CmpInst::FCMP_OEQ ||
									candidate_p == CmpInst::FCMP_UEQ ||
									candidate_p == CmpInst::ICMP_EQ
								)) {
									flip = true;
								}
								if (((op1 == candidate_op2) && (op2 == candidate_op1))
								&&(
									candidate_p == CmpInst::FCMP_OGT ||
									candidate_p == CmpInst::FCMP_UGT ||
									candidate_p == CmpInst::ICMP_UGT ||
									candidate_p == CmpInst::ICMP_SGT ||
									candidate_p == CmpInst::FCMP_OGE ||
									candidate_p == CmpInst::FCMP_UGE ||
									candidate_p == CmpInst::ICMP_UGE ||
									candidate_p == CmpInst::ICMP_SGE ||
									candidate_p == CmpInst::FCMP_OEQ ||
									candidate_p == CmpInst::FCMP_UEQ ||
									candidate_p == CmpInst::ICMP_EQ
								)) {
									flip = true;
								}
							}
							// if standard is < then >, >=, = need to be flipped
							if (p == CmpInst::FCMP_OLT || p == CmpInst::FCMP_ULT || p == CmpInst::ICMP_ULT || p == CmpInst::ICMP_SLT) {
								if (((op1 == candidate_op2) && (op2 == candidate_op1))
								&&(
									candidate_p == CmpInst::FCMP_OLT ||
									candidate_p == CmpInst::FCMP_ULT ||
									candidate_p == CmpInst::ICMP_ULT ||
									candidate_p == CmpInst::ICMP_SLT ||
									candidate_p == CmpInst::FCMP_OLE ||
									candidate_p == CmpInst::FCMP_ULE ||
									candidate_p == CmpInst::ICMP_ULE ||
									candidate_p == CmpInst::ICMP_SLE ||
									candidate_p == CmpInst::FCMP_OEQ ||
									candidate_p == CmpInst::FCMP_UEQ ||
									candidate_p == CmpInst::ICMP_EQ
								)) {
									flip = true;
								}
								if (((op1 == candidate_op1) && (op2 == candidate_op2))
								&&(
									candidate_p == CmpInst::FCMP_OGT ||
									candidate_p == CmpInst::FCMP_UGT ||
									candidate_p == CmpInst::ICMP_UGT ||
									candidate_p == CmpInst::ICMP_SGT ||
									candidate_p == CmpInst::FCMP_OGE ||
									candidate_p == CmpInst::FCMP_UGE ||
									candidate_p == CmpInst::ICMP_UGE ||
									candidate_p == CmpInst::ICMP_SGE ||
									candidate_p == CmpInst::FCMP_OEQ ||
									candidate_p == CmpInst::FCMP_UEQ ||
									candidate_p == CmpInst::ICMP_EQ
								)) {
									flip = true;
								}
							}
							// if standard is >= then <, != need to be flipped
							if (p == CmpInst::FCMP_OGE || p == CmpInst::FCMP_UGE || p == CmpInst::ICMP_UGE || p == CmpInst::ICMP_SGE) {
								if (((op1 == candidate_op1) && (op2 == candidate_op2))
								&&(
									candidate_p == CmpInst::FCMP_OLT ||
									candidate_p == CmpInst::FCMP_ULT ||
									candidate_p == CmpInst::ICMP_ULT ||
									candidate_p == CmpInst::ICMP_SLT ||
									candidate_p == CmpInst::FCMP_ONE ||
									candidate_p == CmpInst::FCMP_UNE ||
									candidate_p == CmpInst::ICMP_NE
								)) {
									flip = true;
								}
								if (((op1 == candidate_op2) && (op2 == candidate_op1))
								&&(
									candidate_p == CmpInst::FCMP_OGT ||
									candidate_p == CmpInst::FCMP_UGT ||
									candidate_p == CmpInst::ICMP_UGT ||
									candidate_p == CmpInst::ICMP_SGT ||
									candidate_p == CmpInst::FCMP_ONE ||
									candidate_p == CmpInst::FCMP_UNE ||
									candidate_p == CmpInst::ICMP_NE
								)) {
									flip = true;
								}
							}
							// if standard is <= then >, != need to be flipped
							if (p == CmpInst::FCMP_OLE || p == CmpInst::FCMP_ULE || p == CmpInst::ICMP_ULE || p == CmpInst::ICMP_SLE) {
								if (((op1 == candidate_op2) && (op2 == candidate_op1))
								&&(
									candidate_p == CmpInst::FCMP_OLT ||
									candidate_p == CmpInst::FCMP_ULT ||
									candidate_p == CmpInst::ICMP_ULT ||
									candidate_p == CmpInst::ICMP_SLT ||
									candidate_p == CmpInst::FCMP_ONE ||
									candidate_p == CmpInst::FCMP_UNE ||
									candidate_p == CmpInst::ICMP_NE
								)) {
									flip = true;
								}
								if (((op1 == candidate_op1) && (op2 == candidate_op2))
								&&(
									candidate_p == CmpInst::FCMP_OGT ||
									candidate_p == CmpInst::FCMP_UGT ||
									candidate_p == CmpInst::ICMP_UGT ||
									candidate_p == CmpInst::ICMP_SGT ||
									candidate_p == CmpInst::FCMP_ONE ||
									candidate_p == CmpInst::FCMP_UNE ||
									candidate_p == CmpInst::ICMP_NE
								)) {
									flip = true;
								}
							}

							// flip if true
							if (flip) {
								if (path_predicted[standard_BI] == 0) {
									path_predicted[candidate_BI] = 1;
								}
								else {
									path_predicted[candidate_BI] = 0;
								}
							}
						}
					}
				}

			}
		}

		// collect stats
		int hazard_agree_count = 0;
		for (const auto& p: hazard_predicted) {
			BranchInst* BI = p.first;
			BasicBlock* parent = BI->getParent();
			auto threshold = BranchProbability::getBranchProbability(1,2);
			int profile_predicted = 0;
			for (int i = 0; i < 2; i++) {
				auto prob = BPI->getEdgeProbability(parent, i);
				if (prob > threshold) {
					profile_predicted = i;
					break;
				}
			}
			if (profile_predicted == p.second) {
				hazard_agree_count += 1;
			}
		}
		int path_agree_count = 0;
		for (const auto& p: path_predicted) {
			BranchInst* BI = p.first;
			BasicBlock* parent = BI->getParent();
			auto threshold = BranchProbability::getBranchProbability(1,2);
			int profile_predicted = 0;
			for (int i = 0; i < 2; i++) {
				auto prob = BPI->getEdgeProbability(parent, i);
				if (prob > threshold) {
					profile_predicted = i;
					break;
				}
			}
			if (profile_predicted == p.second) {
				path_agree_count += 1;
			}
		}

		glb_path_agree += path_agree_count;
		glb_path_count += path_predicted.size();
		glb_hazard_agree += hazard_agree_count;
		glb_hazard_count += hazard_predicted.size();
		glb_conditional_count += conditional_branches.size();

		errs() << "///////////////////////Branch Prediction Stats///////////////////////" << "\n";
		errs() << "num conditional branches =" << glb_conditional_count << "\n";
		errs() << "num covered by heuristics =" << glb_hazard_count + glb_path_count << "\n";
		errs() << "num agreeing with profiling =" << glb_hazard_agree + glb_path_agree << "\n";
		errs() << "accuracy = " << (double) (glb_hazard_agree + glb_path_agree) / (glb_hazard_count + glb_path_count) << "\n";
		errs() << "coverage = " << (double) (glb_hazard_count + glb_path_count) / glb_conditional_count << "\n";

		errs() << "----predicted by hazard----" << "\n";
		// for (const auto & p: hazard_predicted) {
		// 	errs() << *(p.first) << "\n";
		// 	errs() << "\n";
		// }
		errs() << "num predicted by hazard = " << glb_hazard_count << "\n";
		errs() << "\n";
		errs() << "num agreeing with profiling = " << glb_hazard_agree <<  "\n";
		errs() << "\n";

		errs() << "-------------------------------------------" << "\n";

		errs() << "----predicted by path selection----" << "\n";
		// for (const auto & p: path_predicted) {
		// 	errs() << *(p.first) << "\n";
		// 	errs() << "\n";
		// }
		errs() << "num predicted by path selection = " << glb_path_count << "\n";
		errs() << "\n";
		errs() << "num agreeing with profiling = " << glb_path_agree <<  "\n";
		errs() << "\n";




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
					if ((seen.find(child) == seen.end()) && loop->contains(child)) {
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
					auto cur_trace = growTrace(cur_seed, contains_indirectbr, contains_rt, hazard_predicted, path_predicted, seen_in_trace, DT);
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
					BFSorder.push_back(child);
				}
			}

			// pop from the queue
			queue.pop_back();
		}

		for (BasicBlock* cur_seed : BFSorder) {
			if (seen_in_trace.find(cur_seed) == seen_in_trace.end()) {
				auto cur_trace = growTrace(cur_seed, contains_indirectbr, contains_rt, hazard_predicted, path_predicted, seen_in_trace, DT);
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
		std::map<BranchInst*, int>& hazard_predicted,
		std::map<BranchInst*, int>& path_predicted,
		std::unordered_set<BasicBlock*>& seen_in_trace,
		DominatorTree* DT
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
			BasicBlock* likely;
			Instruction* cur_node_terminator = cur_node->getTerminator();
			if (BranchInst* BI = dyn_cast<BranchInst>(cur_node_terminator)) {
				if (BI->isConditional()) {
					if (hazard_predicted.find(BI) == hazard_predicted.end()) {
						if (path_predicted.find(BI) == path_predicted.end()) {
							// not covered, randomly choose
							int cur_choice = rand() % 2;
							likely = BI->getSuccessor(cur_choice);
						}
						else {
							likely = BI->getSuccessor(path_predicted[BI]);
						}
					}
					else {
						likely = BI->getSuccessor(hazard_predicted[BI]);
					}
				}
				else {
					likely = BI->getSuccessor(0);
				}
			}
			else {
				break;
			}
			if (seen_in_trace.find(likely) != seen_in_trace.end()) {
				break;
			}
			// loop back edge
			if (DT->dominates(likely->getTerminator(), cur_node_terminator)) {
				break;
			}
			res.push_back(likely);
			cur_node = likely;
		}
		return res;
	}

	static bool LoopDepthGt(Loop* i, Loop* j) {
		return i->getLoopDepth() > j->getLoopDepth();
	}

	bool tailDuplication(std::vector<std::vector<BasicBlock*>> traces, std::map<BasicBlock*, int> TraceMap, Function* Parent) {
		// copied BB
		std::map<BasicBlock*, BasicBlock*> copiedMap;
		ValueToValueMapTy VMap;
		bool modified = false;
		bool doCopy = false;
		BasicBlock* prevCopiedBB;
		for (auto& curTrace: traces) {
			doCopy = false;
			BasicBlock* prevBB = *curTrace.begin();
			for (auto it = next(curTrace.begin()); it != curTrace.end(); ++it) {  // Ignore first BB
				BasicBlock* originalBB = *it;
				if (!doCopy) {  // detect first side entrance
					for (auto pred : predecessors(originalBB)) {
						// if predecessor not in trace, side entrance
						if (TraceMap[pred] != TraceMap[originalBB]) {
							modified = true;
							doCopy = true;

							// copy first original block
							BasicBlock* clonedBB = CloneBasicBlock(originalBB, VMap, "", Parent);

							// find predecessor in trace, connect predecessor and copy
							Instruction* term = prevBB->getTerminator();
							// set prevBB's successor
							// find idx of origBB in trace, substitute with copiedBB
							unsigned idx = 0;
							for (auto succ : successors(prevBB)) {
								if (succ == originalBB) {
									break;
								}
								idx++;
							}
							term->setSuccessor(idx, clonedBB);

							for (Instruction &II : *clonedBB) {
								RemapInstruction(&II, VMap, RF_IgnoreMissingLocals);
							}

							// remove edge between predecessor and original
							// errs()<< "\noriginal basic block \n" << *originalBB << "\n";
							// errs()<< "\nclone basic block \n" << *clonedBB << "\n";

							prevCopiedBB = clonedBB;
							break;
						}
					}
					// No side entrace for current BB, update previously BB
					prevBB = originalBB;
				}
				// tail portion
				else {
					// Copy current BB
					BasicBlock* clonedBB = CloneBasicBlock(originalBB, VMap, "", Parent);

					// previously copied BB connects to copied BB
					// remove edge between previously copied and current copied BB
					Instruction* term = prevCopiedBB->getTerminator();
					unsigned idx = 0;
					for (auto succ : successors(prevCopiedBB)) {
						if (succ == originalBB) {
							break;
						}
						idx++;
					}
					term->setSuccessor(idx, clonedBB);

					for (Instruction &II : *clonedBB) {
						RemapInstruction(&II, VMap, RF_IgnoreMissingLocals);
					}

					// prev = cur
					prevCopiedBB = clonedBB;
				}
			}
		}

		return modified;
	}

}; // end of struct Hell
}  // end of anonymous namespace

char heuristic_sb::ID = 0;
static RegisterPass<heuristic_sb> X("heuristic_sb", "heuristic super block formation",
                             	false /* Only looks at CFG */,
                             	false /* Analysis Pass */);
