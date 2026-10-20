module

public import SKProof.Port.ComparisonActualOriginalQCanonicalMassBudgets
public import ComparisonNativeOuterComparableTrace

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def canonicalMassReverseAtDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q v diameter : ℝ) : ℝ :=
  diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*(a.canonicalMassHeight v)^ell)^(1/((ell:ℝ)-1))

def canonicalOrdinaryMassBudgetAtDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Lside cut v diameter : ℝ) : ℝ :=
  nativeBinScaleLoss Lside (108*32^2*(Real.log a.data.N)^2)
    (54*32^2*(Real.log a.data.N)^2) (16*v) (v/4)*(16*v)*
      (2*((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)+
        3/(a.canonicalMassPower v*(16*v)^2)+diameter^2+
          a.canonicalMassReverseAtDiameter ell Q v diameter)+
    18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut

def canonicalBroadMassBudgetAtDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Lside cut v width diameter : ℝ) : ℝ :=
  let loss := (32:ℝ)^2+25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)+1
  nativeConditionalLedgerBudget 1 width cut diameter
    (108*loss*(Real.log a.data.N)^2/(a.canonicalMassPower v*(v/4))*Real.log (width/cut))
    (54*loss*(Real.log a.data.N)^2*width/(a.canonicalMassPower v*(v/4)^2))
    (a.canonicalMassReverseAtDiameter ell Q v diameter) Lside

def canonicalLocalMassDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  9*Real.log a.data.N*32*a.data.E/
    (a.data.N^delta*a.data.d^3*(v/2+a.data.U))

def canonicalOuterBroadMassDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  9*Real.log a.data.N*
    min a.cavityCapTravel ((32*cu^3/cl^3)*a.data.E/(a.data.N^delta*a.data.d^3*v))

def canonicalComparableBroadMassBudgetAtDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Lside cut v width diameter : ℝ) : ℝ :=
  nativeConditionalLedgerBudget 1 width cut diameter
    (108*nativeOuterComparableTraceConstant cl cu*(Real.log a.data.N)^2/
      (a.canonicalMassPower v*(v/4))*Real.log (width/cut))
    (54*nativeOuterComparableTraceConstant cl cu*(Real.log a.data.N)^2*width/
      (a.canonicalMassPower v*(v/4)^2))
    (a.canonicalMassReverseAtDiameter ell Q v diameter) Lside

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
