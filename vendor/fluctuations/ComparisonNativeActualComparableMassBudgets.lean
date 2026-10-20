module

public import ComparisonNativeActualMinimumLocalDiameterBudgets
public import ComparisonNativeOuterComparableTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def canonicalComparableBroadMassBudgetAtDiameter
    (a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Lside cut v width diameter : ℝ) : ℝ :=
  nativeConditionalLedgerBudget 1 width cut diameter
    (108*nativeOuterComparableTraceConstant cl cu*(Real.log a.context.N)^2/
      (a.canonicalMassPower v*(v/4))*Real.log (width/cut))
    (54*nativeOuterComparableTraceConstant cl cu*(Real.log a.context.N)^2*width/
      (a.canonicalMassPower v*(v/4)^2))
    (a.canonicalMassReverseAtDiameter ell Q v diameter) Lside

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
