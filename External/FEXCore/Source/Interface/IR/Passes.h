#pragma once

#include <memory>

namespace FEXCore::IR {
class Pass;
class RegisterAllocationPass;
class RegisterAllocationData;

std::unique_ptr<FEXCore::IR::Pass> CreateConstProp(bool InlineConstants);
std::unique_ptr<FEXCore::IR::Pass> CreateContextLoadStoreElimination();
std::unique_ptr<FEXCore::IR::Pass> CreateSyscallOptimization();
std::unique_ptr<FEXCore::IR::Pass> CreateDeadFlagCalculationEliminination();
std::unique_ptr<FEXCore::IR::Pass> CreateDeadStoreElimination();
std::unique_ptr<FEXCore::IR::Pass> CreatePassDeadCodeElimination();
std::unique_ptr<FEXCore::IR::Pass> CreateIRCompaction();
std::unique_ptr<FEXCore::IR::RegisterAllocationPass> CreateRegisterAllocationPass(FEXCore::IR::Pass* CompactionPass, bool OptimizeSRA);
std::unique_ptr<FEXCore::IR::Pass> CreateStaticRegisterAllocationPass();
std::unique_ptr<FEXCore::IR::Pass> CreateLongDivideEliminationPass();
std::unique_ptr<FEXCore::IR::Pass> CreateStackAccessTSORemovalPass();

namespace Validation {
std::unique_ptr<FEXCore::IR::Pass> CreateIRValidation();
std::unique_ptr<FEXCore::IR::Pass> CreateRAValidation();
std::unique_ptr<FEXCore::IR::Pass> CreatePhiValidation();
std::unique_ptr<FEXCore::IR::Pass> CreateValueDominanceValidation();
}
}

