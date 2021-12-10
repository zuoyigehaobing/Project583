//===-- Frequent Path Loop Invariant Code Motion Pass ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// EECS583 F21 - This pass can be used as a template for your Frequent Path LICM
//               homework assignment. The pass gets registered as "fplicm".
//
// This pass performs loop invariant code motion, attempting to remove as much
// code from the body of a loop as possible.  It does this by either hoisting
// code into the preheader block, or by sinking code to the exit blocks if it is
// safe. 
//
////===----------------------------------------------------------------------===//
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

/* *******Implementation Starts Here******* */
#include <bits/stdc++.h>
#include "llvm/IR/Dominators.h"
/* *******Implementation Ends Here******* */

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "fplicm"


namespace SuperBlock { 
struct PSBPass : public FunctionPass {
  static char ID;
  const static int THRESHOLD = 60;
  PSBPass() : FunctionPass(ID) {}

  // Specify the vector of analysis passes that will be used inside your pass.
  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<BlockFrequencyInfoWrapperPass>(); // Analysis pass to load block execution count
    AU.addRequired<BranchProbabilityInfoWrapperPass>(); // Analysis pass to load branch probability
    AU.addRequired<DominatorTreeWrapperPass>();
  }
  
  
  ///////////////  Start   //////////////////
  void printTraces(vector<vector<BasicBlock*>> traces) {
    // TODO: delete
    for (auto& itt: traces) {
      errs() << "/////////   TRACE   ///////////\n";
      for (auto& itb: itt) {
        errs() << itb << "\n";
      }
    } 
    
    for (auto& itt: traces) {
      errs() << "/////////   TRACE   ///////////\n";
      for (auto& itb: itt) {
        errs() << *itb << "\n////////////\n";
      }
    }    
  }
  
  
  void printSucc(BasicBlock* BB) {
    errs() << "/////////////   Successors of " << BB << "   /////////////\n";
    for (auto succ : successors(BB)) {
      errs() << succ << "\n";
    } 
  }
  
  
  static bool cmpval(pair<BasicBlock*, uint64_t>& a, pair<BasicBlock*, uint64_t>& b) {
    return a.second > b.second;
  }
    
    
  vector<pair<BasicBlock*, uint64_t>> mapsort(map<BasicBlock*, uint64_t>& Map) {
    vector<pair<BasicBlock*, uint64_t>> VM;
    for (auto& it: Map) {
      VM.push_back(it);
    } 
    std::sort(VM.begin(), VM.end(), cmpval);
    return VM;
  }


  BasicBlock* best_successor(BasicBlock* CurBB, map<BasicBlock*, int> VisitMap) {
    BranchProbabilityInfo &bpi = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
    DominatorTree &dt = getAnalysis<DominatorTreeWrapperPass>().getDomTree(); 

    // errs() << "********************\n Best Sucessor \n" << *CurBB; 
    // errs() << "\nThreshold" << BranchProbability(THRESHOLD, 100) << "\n ******************************"; 

    for (BasicBlock *Succ : successors(CurBB)) {
      const BasicBlock* cCurBB = CurBB;
      const BasicBlock* cSucc = Succ;
      if (dt.dominates(cSucc, cCurBB)) {
        // errs() << "BsetSucc Found Backedge: \n" << *CurBB << "------>\n" << *Succ << "\n";
        continue; 
      }
      if (VisitMap[Succ] > 0) {  // d is visited
        continue; 
      }
      auto prob = bpi.getEdgeProbability(CurBB, Succ);
      // errs() << "------------Probability: " << prob << "\n" << *Succ << "\n\n"; 
      if (prob > BranchProbability(THRESHOLD, 100)){
        return Succ;
      }
    }
    return NULL;
  }
  
  
  BasicBlock* best_predecessor(BasicBlock* CurBB, map<BasicBlock*, int> VisitMap,
                               map<BasicBlock*, uint64_t> ProfileMap) {
    BranchProbabilityInfo &bpi = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
    DominatorTree &dt = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    // errs() << "********************\n Best Predecessor \n" << *CurBB << "\n ******************************"; 

    for (BasicBlock *Pred : predecessors(CurBB)) {
      const BasicBlock* cCurBB = CurBB;
      const BasicBlock* cPred = Pred;
      if (dt.dominates(cCurBB, cPred)) {
        // errs() << "BestPred Found Backedge: \n" << *Pred << "------>\n" << *CurBB << "\n";
        continue; 
      }
      if (VisitMap[Pred] > 0) {  // p is visited
        continue; 
      }
      auto prob = bpi.getEdgeProbability(Pred, CurBB);
      float predWeight = static_cast<float>( 
          ProfileMap[Pred]
          * static_cast<uint64_t>(prob.getNumerator()) 
          / static_cast<uint64_t>(prob.getDenominator()) );
      float predPercent = predWeight / static_cast<float>(ProfileMap[CurBB]);
      // errs() << "------------Probability: " << predPercent << "\n" << *Pred << "\n\n"; 
      if (predPercent > static_cast<float>(THRESHOLD / 100.0)){
        return Pred; 
      }
    }
    return NULL;
  }
  
  
  bool tailDuplication(vector<vector<BasicBlock*>> traces, map<BasicBlock*, int> TraceMap, Function* Parent) {
    // copied BB 
    map<BasicBlock*, BasicBlock*> copiedMap;
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


  bool runOnFunction(Function &F) override {
    map<BasicBlock*, uint64_t> ProfileMap;
    map<BasicBlock*, int> VisitMap;
    map<BasicBlock*, int> TraceMap; 
    vector<vector<BasicBlock*>> traces;
    int traceCnt = 0;

    // Create objects for each analysis pass
    BranchProbabilityInfo &bpi = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI(); 
    BlockFrequencyInfo &bfi = getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
    DominatorTree &dt = getAnalysis<DominatorTreeWrapperPass>().getDomTree();    
    
    // Mark all BBs unvisited
    for (Function::iterator it = F.begin(), e = F.end(); it != e; ++it) {
      BasicBlock& BB = *it;
      uint64_t blockCount = bfi.getBlockProfileCount(&BB).getValue();
      
      ProfileMap[&BB] = blockCount;
      VisitMap[&BB] = 0;
    }
    // Sort ProfileMap, highest freq to lowest
    vector<pair<BasicBlock*, uint64_t>> sortedBBs = mapsort(ProfileMap);
    
    // while (there are unvisited nodes) do  
    for (auto& it: sortedBBs) {   
      // seed = unvisited BB with largest execution freq
      BasicBlock* seedBB = it.first;
      // errs() << *seedBB << "\ncnt: " << it.second << "\n\n";  
      if (VisitMap[seedBB] > 0) {
        continue;
      }
      
      //trace[i] += seed
      vector<BasicBlock*> curTrace;
      curTrace.push_back(seedBB);
      TraceMap[seedBB] = traceCnt; 
      // errs() << "TRACE " << traceCnt << curTrace[0] << "\n";
      
      // mark seed visited
      VisitMap[seedBB] = 1;
      BasicBlock* curBB = seedBB;
      // Grow Trace Forward
      while(true) {
        BasicBlock* next = best_successor(curBB, VisitMap);
        if (next == NULL) {
          break;
        }
        curTrace.push_back(next);
        TraceMap[next] = traceCnt; 
        VisitMap[next] = 1;
        curBB = next;
      }
      
      // Grow trace backward analogously 
      curBB = seedBB;
      while(true) {
        BasicBlock* prev = best_predecessor(curBB, VisitMap, ProfileMap);
        if (prev == NULL) {
          break;
        }
        curTrace.insert(curTrace.begin(), prev);
         TraceMap[prev] = traceCnt; 
        VisitMap[prev] = 1;
        curBB = prev;
      }
      
      // Add current trace to traces collection
      traceCnt++;
      traces.push_back(curTrace);
    }
    
    // After TRACE FORMATION,
    // TAIL DUPLICATION
    printTraces(traces);
    return tailDuplication(traces, TraceMap, &F);

    //////////////    END    ////////////////
  }
  
}; // end of struct PSBPass


// Random Super Block
struct RSBPass : public FunctionPass {
static char ID;
  const static int THRESHOLD = 60;
  RSBPass() : FunctionPass(ID) {}

  // Specify the vector of analysis passes that will be used inside your pass.
  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<BlockFrequencyInfoWrapperPass>(); // Analysis pass to load block execution count
    AU.addRequired<BranchProbabilityInfoWrapperPass>(); // Analysis pass to load branch probability
    AU.addRequired<DominatorTreeWrapperPass>();
  }
  
  
  ///////////////  Start   //////////////////
  void printTraces(vector<vector<BasicBlock*>> traces) {
    // TODO: delete
    for (auto& itt: traces) {
      errs() << "/////////   TRACE   ///////////\n";
      for (auto& itb: itt) {
        errs() << itb << "\n";
      }
    } 
    
    for (auto& itt: traces) {
      errs() << "/////////   TRACE   ///////////\n";
      for (auto& itb: itt) {
        errs() << *itb << "\n////////////\n";
      }
    }    
  }
  
  
  void printSucc(BasicBlock* BB) {
    errs() << "/////////////   Successors of " << BB << "   /////////////\n";
    for (auto succ : successors(BB)) {
      errs() << succ << "\n";
    } 
  }
  
  
  static bool cmpval(pair<BasicBlock*, uint64_t>& a, pair<BasicBlock*, uint64_t>& b) {
    return a.second > b.second;
  }
    
    
  vector<pair<BasicBlock*, uint64_t>> mapsort(map<BasicBlock*, uint64_t>& Map) {
    vector<pair<BasicBlock*, uint64_t>> VM;
    for (auto& it: Map) {
      VM.push_back(it);
    } 
    std::sort(VM.begin(), VM.end(), cmpval);
    return VM;
  }


  BasicBlock* best_successor(BasicBlock* CurBB, map<BasicBlock*, int> VisitMap) {
    BranchProbabilityInfo &bpi = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
    DominatorTree &dt = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    if (succ_size(CurBB) == 0) {
      return NULL;
    }
    int randIdx = rand() % succ_size(CurBB);
    auto CandPtr = next(succ_begin(CurBB), randIdx);
    BasicBlock* Cand = *CandPtr;
    errs() << "********************\n Best Successor \n" << randIdx << "\n" << *Cand << "\n ******************************";
    const BasicBlock* cCurBB = CurBB;
    const BasicBlock* cSucc = Cand;
    if (dt.dominates(cSucc, cCurBB)) {
      // errs() << "BsetSucc Found Backedge: \n" << *CurBB << "------>\n" << *Succ << "\n";
      return NULL; 
    }
    if (VisitMap[Cand] > 0) {  // d is visited
      return NULL; 
    }
    return Cand;
  }
  
  
  BasicBlock* best_predecessor(BasicBlock* CurBB, map<BasicBlock*, int> VisitMap,
                               map<BasicBlock*, uint64_t> ProfileMap) {
    BranchProbabilityInfo &bpi = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI();
    DominatorTree &dt = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
    if (pred_size(CurBB) == 0) {
      return NULL;
    }
    int randIdx = rand() % pred_size(CurBB);
    auto CandPtr = next(pred_begin(CurBB), randIdx);
    BasicBlock* Cand = *CandPtr;
    errs() << "********************\n Best Predecessor \n" << randIdx << "\n" << *Cand << "\n ******************************";
    const BasicBlock* cCurBB = CurBB;
    const BasicBlock* cPred = Cand;
    if (dt.dominates(cCurBB, cPred)) {
      // errs() << "BestPred Found Backedge: \n" << *Pred << "------>\n" << *CurBB << "\n";
      return NULL;; 
    }
    if (VisitMap[Cand] > 0) {  // p is visited
      return NULL;; 
    }
    return Cand;
  }
  
  
  bool tailDuplication(vector<vector<BasicBlock*>> traces, map<BasicBlock*, int> TraceMap, Function* Parent) {
    // copied BB 
    map<BasicBlock*, BasicBlock*> copiedMap;
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


  bool runOnFunction(Function &F) override {
    map<BasicBlock*, uint64_t> ProfileMap;
    map<BasicBlock*, int> VisitMap;
    map<BasicBlock*, int> TraceMap; 
    vector<vector<BasicBlock*>> traces;
    int traceCnt = 0;

    // Create objects for each analysis pass
    BranchProbabilityInfo &bpi = getAnalysis<BranchProbabilityInfoWrapperPass>().getBPI(); 
    BlockFrequencyInfo &bfi = getAnalysis<BlockFrequencyInfoWrapperPass>().getBFI();
    DominatorTree &dt = getAnalysis<DominatorTreeWrapperPass>().getDomTree();    
    
    // Mark all BBs unvisited
    for (Function::iterator it = F.begin(), e = F.end(); it != e; ++it) {
      BasicBlock& BB = *it;
      uint64_t blockCount = bfi.getBlockProfileCount(&BB).getValue();
      
      ProfileMap[&BB] = blockCount;
      VisitMap[&BB] = 0;
    }
    // Sort ProfileMap, highest freq to lowest
    vector<pair<BasicBlock*, uint64_t>> sortedBBs = mapsort(ProfileMap);
    
    // while (there are unvisited nodes) do  
    for (auto& it: sortedBBs) {   
      // seed = unvisited BB with largest execution freq
      BasicBlock* seedBB = it.first;
      // errs() << *seedBB << "\ncnt: " << it.second << "\n\n";  
      if (VisitMap[seedBB] > 0) {
        continue;
      }
      
      //trace[i] += seed
      vector<BasicBlock*> curTrace;
      curTrace.push_back(seedBB);
      TraceMap[seedBB] = traceCnt; 
      // errs() << "TRACE " << traceCnt << curTrace[0] << "\n";
      
      // mark seed visited
      VisitMap[seedBB] = 1;
      BasicBlock* curBB = seedBB;
      // Grow Trace Forward
      while(true) {
        BasicBlock* next = best_successor(curBB, VisitMap);
        if (next == NULL) {
          break;
        }
        curTrace.push_back(next);
        TraceMap[next] = traceCnt; 
        VisitMap[next] = 1;
        curBB = next;
      }
      
      // Grow trace backward analogously 
      curBB = seedBB;
      while(true) {
        BasicBlock* prev = best_predecessor(curBB, VisitMap, ProfileMap);
        if (prev == NULL) {
          break;
        }
        curTrace.insert(curTrace.begin(), prev);
         TraceMap[prev] = traceCnt; 
        VisitMap[prev] = 1;
        curBB = prev;
      }
      
      // Add current trace to traces collection
      traceCnt++;
      traces.push_back(curTrace);
    }
    
    // After TRACE FORMATION,
    // TAIL DUPLICATION
    printTraces(traces);
    return tailDuplication(traces, TraceMap, &F);

    //////////////    END    ////////////////
  }
  
}; // end of struct RSBPass


} // end of namespace Correctness

//char Correctness::FPLICMPass::ID = 0;
//static RegisterPass<Correctness::FPLICMPass> X("fplicm-correctness", "Frequent Loop Invariant Code Motion for correctness test", false, false);

char SuperBlock::PSBPass::ID = 0;
static RegisterPass<SuperBlock::PSBPass> X("psbpass", "Profile Super Block Pass");

char SuperBlock::RSBPass::ID = 1;
static RegisterPass<SuperBlock::RSBPass> Y("rsbpass", "Random Super Block Pass");
