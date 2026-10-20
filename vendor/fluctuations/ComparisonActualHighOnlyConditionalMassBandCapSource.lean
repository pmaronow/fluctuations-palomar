module

public import ComparisonActualHighOnlyConditionalArbitraryWidthCapSource
public import ComparisonActualHighOnlyConditionalBroadPrice

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 38000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
open ActualHighOnlyOverlapMinimum
theorem eventually_actual_high_only_mass_band_cap_source_budget
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Q : ℝ,1 ≤ Q ∧ ∀ᶠn in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs → ∀P : a.Potential,
      ∀cap : ShiftedCapInterval a P,∀l z v V Lside cut : ℝ,
      (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      0 < l → l < z → cap.left ≤ l → z ≤ cap.right →
      0 < v → v ≤ 1 → v/4 ≤ a.alpha.val.val l → a.alpha.val.val z ≤ min (16*v) 1 →
      V∈Icc (0:ℝ) 1 → (∀r∈Ioo l z,a.alpha.val.val r ≤ V) →
      a.data.M V*(cap.right-cap.left) ≤ 512*(∫r in Ioo l z,deriv a.alpha.val.val r) →
      0 ≤ Lside → 0 < cut → 2*cut < (∫r in Ioo l z,deriv a.alpha.val.val r) →
      Real.log (1/cut) ≤ Lside →
      (∫r in Ioo l z,deriv a.alpha.val.val r*a.shiftedNativeModel.thermal (a.alpha.val.val r)) ≤
        a.canonicalBroadMassBudget ell Q Lside cut v (∫r in Ioo l z,deriv a.alpha.val.val r) := by
  obtain ⟨Q,hQ,HS⟩:=eventually_actual_high_only_arbitrary_width_cap_source_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [HS] with n hn
  intro a hs hsxs P cap l z v V Lside cut hcontacts hl0 hlz hclL hzcap hv hv1 hRho hzmass
    hV hAV hDensity hLside hcut hcutWidth hlogcut
  let zg:=a.R (min (16*v) 1)
  have hzg : zg ≤ 1:=(a.shiftedNativeModel.R_bounds _).2
  have hzG : z ≤ zg:=by
    calc
      z=a.shiftedNativeModel.R (a.alpha.val.val z):=(a.shiftedNativeModel.R_inverse
        ⟨hl0.le.trans hlz.le,hzcap.trans cap.hright⟩).symm
      _ ≤ a.R (min (16*v) 1):=a.shiftedNativeModel.R_monotone hzmass
  have hY : a.xs+a.alpha.val.val z ≤ a.canonicalMassHeight v:=by
    dsimp only [canonicalMassHeight]
    linarith only [hzmass]
  have HH:=hn a hs hsxs P cap l z zg V 512 (a.canonicalMassHeight v) Lside cut
    hcontacts hl0 hlz hclL hzcap hzG hzg hV hAV (by norm_num) hDensity
    hY hLside hcut hcutWidth hlogcut
  let width:=∫r in Ioo l z,deriv a.alpha.val.val r
  let power:=a.canonicalMassPower v
  let F:=(512:ℝ)
  let loss:=(32:ℝ)^2+25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U)+1
  have hP : 0 < power:=a.canonical_mass_power_pos v
  have hrho : 0 < a.alpha.val.val l:=(show 0 < v/4 by positivity).trans_le hRho
  have hV4 : 0 < v/4:=by positivity
  have hF : 0 ≤ F:=by norm_num [F]
  have hloss : 0 ≤ loss:=by
    have HL : 0 ≤ Real.log ((1+a.data.U)/a.data.U):=
      Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    have HU:=a.data.hU
    dsimp only [loss]
    positivity
  have hFloss : F ≤ loss:=by
    have HL : 0 ≤ Real.log ((1+a.data.U)/a.data.U):=
      Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    have HU:=a.data.hU
    have HH:0 ≤ 25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U):=by positivity
    dsimp only [F,loss]
    nlinarith only [HH]
  have hwidth0 : 0 ≤ width:=by dsimp only [width];linarith only [hcutWidth,hcut]
  have hlog0 : 0 ≤ Real.log (width/cut):=Real.log_nonneg
    ((one_le_div hcut).mpr (by dsimp only [width];linarith only [hcutWidth,hcut]))
  have HVS : 108*F*(Real.log a.data.N)^2/(power*a.alpha.val.val l)*Real.log (width/cut)≤
      108*loss*(Real.log a.data.N)^2/(power*(v/4))*Real.log (width/cut):=by
    apply mul_le_mul_of_nonneg_right _ hlog0
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      hFloss (by norm_num : (0:ℝ)≤108)) (sq_nonneg _))
      (mul_nonneg hP.le hrho.le)).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hP hV4)
      (mul_le_mul_of_nonneg_left hRho hP.le)
  have HTC : 54*F*(Real.log a.data.N)^2*width/(power*(a.alpha.val.val l)^2)≤
      54*loss*(Real.log a.data.N)^2*width/(power*(v/4)^2):=by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFloss
        (by norm_num : (0:ℝ)≤54)) (sq_nonneg _)) hwidth0) (mul_nonneg hP.le (sq_nonneg _))).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hP (sq_pos_of_pos hV4))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV4.le hRho 2) hP.le)
  have Hbcoeff : 0≤66+64*Lside+65536*(1+Lside)^2:=by positivity
  have HV:=mul_le_mul_of_nonneg_left HVS (by norm_num : (0:ℝ)≤48)
  have HT:=mul_le_mul_of_nonneg_left HTC Hbcoeff
  dsimp only at HH
  change (∫r in Ioo l z,deriv a.alpha.val.val r*a.shiftedNativeModel.thermal (a.alpha.val.val r)) ≤
    nativeConditionalLedgerBudget 1 width cut a.canonicalMassDiameter
      (108*F*(Real.log a.data.N)^2/(power*a.alpha.val.val l)*Real.log (width/cut))
      (54*F*(Real.log a.data.N)^2*width/(power*(a.alpha.val.val l)^2))
      (a.canonicalMassReverse ell Q v) Lside at HH
  unfold canonicalBroadMassBudget
  unfold nativeConditionalLedgerBudget at HH ⊢
  dsimp only [F,loss,power,width] at HV HT HH ⊢
  norm_num only [Nat.cast_one,mul_one] at HH ⊢
  nlinarith only [HH,HV,HT]

end OAI.SKFluctuations.LaplaceWindowFormalization
