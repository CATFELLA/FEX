#include <FEXCore/Core/X86Enums.h>
#include <FEXCore/IR/IR.h>
#include <FEXCore/IR/IREmitter.h>
#include <FEXCore/IR/IntrusiveIRList.h>

#include <array>
#include <iostream>

#include "Interface/Core/OpcodeDispatcher.h"
#include "Interface/IR/PassManager.h"

// TODO remove autos
namespace FEXCore::IR {

enum RBP_STATE {  // maybe not?
  NOT_CHANGED = (0b000 << 0),
  STACK       = (0b001 << 0),
  NOT_STACK   = (0b010 << 0),
};

struct BlockInfo {
  int State = NOT_CHANGED;
  std::set<OrderedNode*> StackNodes;
  std::set<OrderedNode*> UnStackNodes;
  std::vector<OrderedNode*> Predecessors;
  // std::vector<OrderedNode*> Successors;
  bool Visited = false;
};

class StackAccessTSORemovalPass final : public Pass {
 public:
  bool Run(IREmitter* IREmit) override;

 private:
  void CalculateControlFlowInfo(IREmitter *IREmit);
  int CalculateComplexState(const OrderedNode* TargetNode,
                            const IRListView& CurrentIR);
  std::unordered_map<NodeID, BlockInfo> OffsetToBlockMap;
};

void StackAccessTSORemovalPass::CalculateControlFlowInfo(IREmitter *IREmit) {
    auto CurrentIR = IREmit->ViewIR();

    for (auto [BlockNode, BlockHeader] : CurrentIR.GetBlocks()) {
    BlockInfo* CurrentBlock =
        &OffsetToBlockMap.try_emplace(CurrentIR.GetID(BlockNode)).first->second;
    for (auto [CodeNode, IROp] : CurrentIR.GetCode(BlockNode)) {
      switch (IROp->Op) {
        case IR::OP_CONDJUMP: {
          auto Op = IROp->CW<IR::IROp_CondJump>();

          // OrderedNode* TrueTargetNode = CurrentIR.GetNode(Op->TrueBlock);
          // OrderedNode* FalseTargetNode = CurrentIR.GetNode(Op->FalseBlock);

          // CurrentBlock->Successors.emplace_back(TrueTargetNode);
          // CurrentBlock->Successors.emplace_back(FalseTargetNode);

          {
            auto Block =
                &OffsetToBlockMap.try_emplace(Op->TrueBlock.ID()).first->second;
            Block->Predecessors.emplace_back(BlockNode);
          }

          {
            auto Block = &OffsetToBlockMap.try_emplace(Op->FalseBlock.ID())
                              .first->second;
            Block->Predecessors.emplace_back(BlockNode);
          }

          break;
        }
        case IR::OP_JUMP: {
          auto Op = IROp->CW<IR::IROp_Jump>();
          // OrderedNode* TargetNode = CurrentIR.GetNode(Op->Header.Args[0]);
          // CurrentBlock->Successors.emplace_back(TargetNode);

          {
            auto Block =
                OffsetToBlockMap.try_emplace(Op->Header.Args[0].ID()).first;
            Block->second.Predecessors.emplace_back(BlockNode);
          }
          break;
        }
        case IR::OP_STOREREGISTER: {
          IROp_StoreRegister* Op = IROp->CW<IR::IROp_StoreRegister>();

          // other registers as well
          if (Op->Offset == offsetof(FEXCore::Core::CPUState,
                                     gregs[FEXCore::X86State::REG_RBP]) &&
              Op->Class == GPRClass) {
            std::queue<IROp_Header*> values{};
            values.push(IREmit->GetOpHeader(Op->Value));

            while (!values.empty()) {
              IROp_Header* ValOp = values.front();
              values.pop();

              switch (ValOp->Op) {
                // single arg inst?
                // dubious at the very least
                case IR::OP_NEG: {
                  values.push(IREmit->GetOpHeader(ValOp->Args[0]));

                  break;
                }
                case IR::OP_ADD:
                case IR::OP_SUB:
                // all two arg instructions can be handled here
                // OP_OR, AND, XOR and all that
                // although i'm not sure this is even needed
                // and since it's not explicit it can easily break later.. :/
                case IR::OP_OR:
                case IR::OP_AND:
                case IR::OP_XOR: {
                  values.push(IREmit->GetOpHeader(ValOp->Args[0]));
                  values.push(IREmit->GetOpHeader(ValOp->Args[1]));

                  break;
                }
                case IR::OP_LOADREGISTER: {
                  auto* LocalOp = ValOp->CW<IR::IROp_LoadRegister>();

                  if (LocalOp->Offset ==
                          offsetof(FEXCore::Core::CPUState,
                                   gregs[FEXCore::X86State::REG_RSP]) &&
                      LocalOp->Class == GPRClass) {
                    CurrentBlock->State = STACK;
                    CurrentBlock->StackNodes.insert(CodeNode);
                    // could save the pointer? just to identify it later, like
                    // ssa id would be preferable since ITS 4BYTES
                  }

                  break;
                }
                // consider these operations as not related to stack
                // so everything else really, no need to check
                case IR::OP_CONSTANT:
                case IR::OP_INLINECONSTANT:
                case IR::OP_LOADMEM:
                case IR::OP_LOADMEMTSO:
                case IR::OP_LSHL:
                case IR::OP_SELECT:
                case IR::OP_LSHR:              // not confirmed
                case IR::OP_ASHR:              // not confirmed
                case IR::OP_ENTRYPOINTOFFSET:  // this might be important?
                case IR::OP_ROR:               // not confirmed
                case IR::OP_VEXTRACTTOGPR:
                case IR::OP_BFE:  // probably not used to calculate offset
                case IR::OP_SBFE:
                case IR::OP_MUL:  // this one could be btw
                {
                  // std::cout << "end of walk " << std::endl;
                  break;
                }
                default: {
                  std::cout << static_cast<uint16_t>(ValOp->Op)
                            << " - not handled during a register crawl"
                            << std::endl;
                  break;
                }
              }
            }

            /* never hit the RSP register, so it's not a stack value being
             * loaded. */
            if (CurrentBlock->State != STACK) {
              CurrentBlock->State = NOT_STACK;
              CurrentBlock->UnStackNodes.insert(CodeNode);
            }
          }
          break;
        }
        default:
          break;
      }
    }
  }
}

// returns the combined state of all the predecessors and the block itself
int StackAccessTSORemovalPass::CalculateComplexState(
    const OrderedNode* TargetNode, const IRListView& CurrentIR) {
  // std::cout << "Calculating Complex State for " << (void*)TargetNode
  //           << std::endl;
  //  and yeah recursive is a bad idea
  int ResultingState = STACK;

  auto TargetPair = OffsetToBlockMap.find(CurrentIR.GetID(TargetNode));
  if (TargetPair == OffsetToBlockMap.end()) {
    std::cout << "TargetPair not found in offsets !!!! a problem" << std::endl;
    return NOT_STACK;  // means there is a problem actually
                       // safer to assume it's not stack (and visited?)
                       // but it actually should never happen
  }

  BlockInfo* TargetBlock = &TargetPair->second;

  if (TargetBlock->Visited || TargetBlock->Predecessors.size() == 0 ||
      TargetBlock->State != NOT_CHANGED) {
    return TargetBlock->State;
  }

  TargetBlock->Visited = true;

  for (auto i : TargetBlock->Predecessors) {
    // a bit of an optimization here, only call if predecessor is not visited
    // very important actually and don't have to check the next if
    // OR not; have to think about it
    if (i ==
        TargetNode) {  // ok so this is not ideal, but it will do for now
                       // like sure, a node can start with stack and then change
                       // the value to not stack and jump to it's beggining, but
                       // that's very unconventional and weird
      continue;
    }
    int PredecessorState = CalculateComplexState(i, CurrentIR);

    if (PredecessorState == NOT_CHANGED) {  // this actually shouldn't happen at
                                            // all only in IR that doesn't use
                                            // RBP.
                                            // so it could and should happen
      ResultingState = NOT_CHANGED;
    } else if (PredecessorState == NOT_STACK) {
      ResultingState = NOT_STACK;
      break;
    }
  }

  TargetBlock->State = ResultingState;

  return TargetBlock->State;
}

bool StackAccessTSORemovalPass::Run(IREmitter* IREmit) {
  CalculateControlFlowInfo(IREmit);

  auto CurrentIR = IREmit->ViewIR();
  bool Changed = false;

  int i = 0;
  for (auto [BlockNode, BlockHeader] : CurrentIR.GetBlocks()) {
    int StackStatus = NOT_CHANGED;
    auto CurrentBlockPair = OffsetToBlockMap.find(CurrentIR.GetID(BlockNode));

    if (CurrentBlockPair == OffsetToBlockMap.end()) {
      std::cout << "Block not found in offsets" << std::endl;
      continue;
    }

    BlockInfo* CurrentBlock = &CurrentBlockPair->second;

    for (auto CodeNode : CurrentBlock->Predecessors) {
      int PredecessorState = CalculateComplexState(CodeNode, CurrentIR);

      if (PredecessorState == NOT_STACK) {
        StackStatus = NOT_STACK;
        break;
      } else if (PredecessorState == STACK) {
        StackStatus = STACK;
      }
    }

    for (auto [CodeNode, IROp] : CurrentIR.GetCode(BlockNode)) {
      if (CurrentBlock->StackNodes.contains(CodeNode)) {
        StackStatus = STACK;
      }
      if (CurrentBlock->UnStackNodes.contains(CodeNode)) {
        StackStatus = NOT_STACK;
      }
      if (IROp->Op == IR::OP_LOADMEMTSO && StackStatus == STACK) {
        IROp->Op = IR::OP_LOADMEM;
        Changed = true;
      }

      if (IROp->Op == IR::OP_STOREMEMTSO && StackStatus == STACK) {
        IROp->Op = IR::OP_STOREMEM;
        Changed = true;
      }
    }

    // now we can update the block state??? like in the
    // CalculateComplexState
    CurrentBlock->Visited = true;
    if (CurrentBlock->State == NOT_CHANGED) {
      CurrentBlock->State = StackStatus;
    }

    i++;
  }

  return Changed;
}

std::unique_ptr<Pass> CreateStackAccessTSORemovalPass() {
  return std::make_unique<StackAccessTSORemovalPass>();
}
}  // namespace FEXCore::IR
