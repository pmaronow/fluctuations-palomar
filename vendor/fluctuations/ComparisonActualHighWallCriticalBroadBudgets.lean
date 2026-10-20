module

public import ComparisonActualHighWallAllCapMismatch
public import ComparisonNativeLocalMassBandAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def criticalBroadMassPower
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  a.data.N*laplaceComparisonStrength a.data.d (a.data.d^2) (a.shiftedNativeModel.R (min (16*v) 1))

def criticalBroadMassHeight
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  a.xs+min (16*v) 1

def criticalBroadMassDiameter
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) : ℝ :=
  9*Real.log a.data.N*(a.data.rmin+a.cavityCapTravel)

def criticalBroadMassReverse
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q v : ℝ) : ℝ :=
  a.criticalBroadMassDiameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*(a.criticalBroadMassHeight v)^ell)^(1/((ell:ℝ)-1))

def criticalBroadTraceLoss
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (K v V : ℝ) : ℝ :=
  (K+1)^2*(1+v/(comparisonSmallMass a.data.N a.data.E))*Real.log ((1+comparisonSmallMass a.data.N a.data.E)/(comparisonSmallMass a.data.N a.data.E))+
    a.data.M V*a.data.rmin/v

def criticalBroadMassBudget
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Lside cut v width : ℝ) : ℝ :=
  let loss := (32:ℝ)^2+a.criticalBroadTraceLoss 4 v (min (4*v) 1)+1
  nativeConditionalLedgerBudget 1 width cut a.criticalBroadMassDiameter
    (108*loss*(Real.log a.data.N)^2/(a.criticalBroadMassPower v*(v/4))*Real.log (width/cut))
    (54*loss*(Real.log a.data.N)^2*width/(a.criticalBroadMassPower v*(v/4)^2))
    (a.criticalBroadMassReverse ell Q v) Lside

theorem criticalBroad_constraint_length_calibration
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    a.data.d^3*(comparisonConstraintLength a.data.N a.data.E a.data.d)*(comparisonSmallMass a.data.N a.data.E) ≤ a.data.E := by
  have hN := a.data.hN
  have hd := a.data.hd
  have hE := a.data.hE
  have hs : (Real.sqrt a.data.N)^2 = a.data.N := Real.sq_sqrt hN.le
  have hs3 : (Real.sqrt a.data.N)^3 = a.data.N*Real.sqrt a.data.N := by
    calc
      _ = (Real.sqrt a.data.N)^2*Real.sqrt a.data.N := by ring
      _ = _ := by rw [hs]
  have hL : (comparisonConstraintLength a.data.N a.data.E a.data.d) ≤ (comparisonLowerScale a.data.N a.data.E a.data.d)^3/a.data.d^2 := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ a.data.d^3)) a.data.hU.le
  have he : a.data.d^3*((comparisonLowerScale a.data.N a.data.E a.data.d)^3/a.data.d^2)*comparisonSmallMass a.data.N a.data.E = Real.sqrt a.data.N*a.data.E^2/a.data.d^2 := by
    unfold comparisonLowerScale comparisonSmallMass
    rw [div_pow,mul_pow,hs3]
    field_simp
  rw [he] at hmul
  have hr : Real.sqrt a.data.N*a.data.E^2/a.data.d^2 ≤ a.data.E := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [a.hupper]
  exact hmul.trans hr

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
