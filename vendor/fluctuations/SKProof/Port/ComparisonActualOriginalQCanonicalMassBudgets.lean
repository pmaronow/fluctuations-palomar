module

public import SKProof.Port.ComparisonActualOriginalQAllCapMismatch
public import ComparisonNativeLocalMassBandAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def canonicalMassPower
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  a.data.N*laplaceComparisonStrength a.data.d a.lam (a.sweepRadius (min (16*v) 1))

def canonicalMassHeight
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  a.xs+min (16*v) 1

def canonicalMassDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) : ℝ :=
  9*Real.log a.data.N*a.cavityCapTravel

def canonicalMassReverse
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q v : ℝ) : ℝ :=
  a.canonicalMassDiameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*(a.canonicalMassHeight v)^ell)^(1/((ell:ℝ)-1))

def canonicalOrdinaryMassBudget
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Lside cut v : ℝ) : ℝ :=
  nativeBinScaleLoss Lside (108*32^2*(Real.log a.data.N)^2)
    (54*32^2*(Real.log a.data.N)^2) (16*v) (v/4)*(16*v)*
      (2*((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)+
        3/(a.canonicalMassPower v*(16*v)^2)+a.canonicalMassDiameter^2+a.canonicalMassReverse ell Q v)+
    18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut

def canonicalBroadMassBudget
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Lside cut v width : ℝ) : ℝ :=
  let loss := (32:ℝ)^2+25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)+1
  nativeConditionalLedgerBudget 1 width cut a.canonicalMassDiameter
    (108*loss*(Real.log a.data.N)^2/(a.canonicalMassPower v*(v/4))*Real.log (width/cut))
    (54*loss*(Real.log a.data.N)^2*width/(a.canonicalMassPower v*(v/4)^2))
    (a.canonicalMassReverse ell Q v) Lside

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
