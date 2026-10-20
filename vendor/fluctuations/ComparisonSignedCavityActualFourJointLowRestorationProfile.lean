module

public import ComparisonSignedCavityActualFourJointLowRestorationReadout
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

def nativeActualOriginalFourJointLowRestorationError
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  (1/(chi*K star))*((W⁻¹)^st.generation*nativeActualOriginalFourOtherCategoryContrast M U st .jointLowRestoration)

theorem actual_minimum_four_joint_LOW_restoration_error_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U ≤ as.length)
    {W cK B : ℝ} (hW : 0 < W) (hcK : 0 < cK) (hB : 0 ≤ B)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration M U st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration M U (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourJointLowRestorationError M U W st| ≤
      |st.term.coefficient| *(2/(Real.exp (-4*(Temp+2*Cf))*cK))*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  obtain ⟨hden,_,hdenlo⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks M
    hCf HS hxs hW hcK ho hs hU hstarK
  have hterm : 0 ≤ |st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration M U st.term) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration M U (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration M U (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by linarith
  unfold nativeActualOriginalFourJointLowRestorationError
  dsimp only
  rw [native_actual_four_joint_LOW_restoration_contrast_eq_resources M U st ho,mul_neg,mul_neg,abs_neg,mul_sub]
  have Hring : (W⁻¹)^st.generation*((1/2:ℝ)*nativeActualOriginalFreshResourceJointLowRestoration M U (st.term.retarget 0))=
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualOriginalFreshResourceJointLowRestoration M U (st.term.retarget 0)):=by ring
  rw [Hring,abs_mul,abs_of_pos (div_pos zero_lt_one hden)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (div_nonneg zero_le_one hden.le)).trans
  have Hfrac : 1/(chi*K star) ≤ 1/(Cd*W):=div_le_div_of_nonneg_left zero_le_one (mul_pos hCd hW) hdenlo
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  dsimp only [Cd]
  field_simp

end OAI.SKFluctuations.Cavity
