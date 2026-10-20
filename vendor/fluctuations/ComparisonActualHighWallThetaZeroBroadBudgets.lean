module

public import ComparisonActualHighWallThetaZeroCapTravelCore
public import ComparisonActualHighWallThetaZeroPositiveAmplitude
public import ComparisonActualHighWallCriticalBroadBudgets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

theorem cavityCapTravel_nonneg
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    0 ≤ M.cavityCapTravel := by
  unfold cavityCapTravel
  exact mul_nonneg (div_nonneg M.data.hL.le (Real.rpow_nonneg M.data.hN.le _))
    (Real.log_nonneg ((one_le_div M.data.hU).mpr (by linarith)))

theorem radius_le_smallMass
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    M.data.rmin ≤ comparisonSmallMass M.data.N M.data.E :=
  M.data.theta_zero_radius_le_smallMass

def criticalBroadMassPower
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  M.data.N*laplaceComparisonStrength M.data.d M.lam (M.shiftedNativeModel.R (min (16*v) 1))

def criticalBroadMassHeight
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  M.xs+min (16*v) 1

theorem criticalBroadMassHeight_nonneg
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    {v : ℝ} (hv : 0 ≤ v) : 0 ≤ M.criticalBroadMassHeight v :=
  add_nonneg M.hxs.le (le_min (mul_nonneg (by norm_num) hv) zero_le_one)

def criticalBroadMassDiameter
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) : ℝ :=
  9*Real.log M.data.N*(M.data.rmin+M.cavityCapTravel)

def criticalBroadMassReverse
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Craw v : ℝ) : ℝ :=
  M.criticalBroadMassDiameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Craw)^(2*ell)*(M.criticalBroadMassHeight v)^ell)^(1/((ell:ℝ)-1))

def criticalBroadTraceLoss
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (K v V : ℝ) : ℝ :=
  (K+1)^2*(1+v/(comparisonSmallMass M.data.N M.data.E))*Real.log ((1+comparisonSmallMass M.data.N M.data.E)/(comparisonSmallMass M.data.N M.data.E))+
    M.data.M V*M.data.rmin/v

def criticalBroadMassBudget
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Craw Lside cut v width : ℝ) : ℝ :=
  let loss := (32:ℝ)^2+M.criticalBroadTraceLoss 4 v (min (4*v) 1)+1
  nativeConditionalLedgerBudget 1 width cut M.criticalBroadMassDiameter
    (108*loss*(Real.log M.data.N)^2/(M.criticalBroadMassPower v*(v/4))*Real.log (width/cut))
    (54*loss*(Real.log M.data.N)^2*width/(M.criticalBroadMassPower v*(v/4)^2))
    (M.criticalBroadMassReverse ell Craw v) Lside

theorem criticalBroad_constraint_length_calibration
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    M.data.d^3*(comparisonConstraintLength M.data.N M.data.E M.data.d)*(comparisonSmallMass M.data.N M.data.E) ≤ M.data.E := by
  have hN := M.data.hN
  have hd := M.data.hd
  have hE := M.data.hE
  have hs : (Real.sqrt M.data.N)^2 = M.data.N := Real.sq_sqrt hN.le
  have hs3 : (Real.sqrt M.data.N)^3 = M.data.N*Real.sqrt M.data.N := by
    calc
      _ = (Real.sqrt M.data.N)^2*Real.sqrt M.data.N := by ring
      _ = _ := by rw [hs]
  have hL : (comparisonConstraintLength M.data.N M.data.E M.data.d) ≤ (comparisonLowerScale M.data.N M.data.E M.data.d)^3/M.data.d^2 := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ M.data.d^3)) M.data.hU.le
  have he : M.data.d^3*((comparisonLowerScale M.data.N M.data.E M.data.d)^3/M.data.d^2)*comparisonSmallMass M.data.N M.data.E = Real.sqrt M.data.N*M.data.E^2/M.data.d^2 := by
    unfold comparisonLowerScale comparisonSmallMass
    rw [div_pow,mul_pow,hs3]
    field_simp
  rw [he] at hmul
  have hr : Real.sqrt M.data.N*M.data.E^2/M.data.d^2 ≤ M.data.E := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [M.hupper]
  exact hmul.trans hr
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
