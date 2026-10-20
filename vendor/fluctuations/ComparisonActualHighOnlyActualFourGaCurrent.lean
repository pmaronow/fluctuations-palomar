module

public import ComparisonActualHighOnlyActualResourceGaReadout
public import ComparisonSignedCavityActualFourGaCurrent
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyActualFourGaSource

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

def nativeActualOriginalFourGaCurrentError_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  -((M.bf (partitionPoint 0 as star):ℝ)/(2*nativeContinuumMixedClock n M.bf M.hf as star))*
    ((W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U (st.term.retarget 0)))

theorem actual_minimum_four_Ga_error_eq_current_add_restoration_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star<U) (ho : MassOrdered 0 as) (W : ℝ) :
    nativeActualOriginalFourGaError_high_only M U W st=
      nativeActualOriginalFourGaCurrentError_high_only M U W st+
      nativeActualOriginalFourGaRestorationError_high_only M U W st := by
  rw [actual_minimum_four_Ga_error_eq_resources_high_only M st hP hi hs ho W,
    actual_minimum_resource_Ga_eq_current_add_restoration_high_only M hP hi hs ho,
    actual_minimum_resource_Ga_eq_current_add_restoration_high_only M hP.retarget hi hs ho]
  unfold nativeActualOriginalFourGaCurrentError_high_only nativeActualOriginalFourGaRestorationError_high_only
  ring

theorem actual_minimum_four_Ga_current_error_abs_le_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {W cK B Temp : ℝ} (hW : 0<W) (hcK : 0<cK) (hB : 0≤B) (hTemp : 0≤Temp)
    (hb : (M.bf (partitionPoint 0 as star):ℝ) ≤ Temp)
    (hK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (H0 : |(W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourGaCurrentError_high_only M U W st| ≤
      |st.term.coefficient| *(Temp/cK)*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as star
  have hK0 : 0<K:=(mul_pos hcK hW).trans_le hK
  have hterm : 0≤|st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U st.term)
    0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceGaCurrent_high_only M U (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by
    rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at Hdiff
    linarith
  unfold nativeActualOriginalFourGaCurrentError_high_only
  rw [abs_mul,abs_neg,abs_of_nonneg (show 0≤(M.bf (partitionPoint 0 as star):ℝ)/(2*K) by positivity)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (by positivity)).trans
  have Hfrac : (M.bf (partitionPoint 0 as star):ℝ)/(2*K) ≤ Temp/(2*(cK*W)):=
    div_le_div₀ hTemp hb (mul_pos (by norm_num) (mul_pos hcK hW))
      (mul_le_mul_of_nonneg_left hK (by norm_num))
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  field_simp

end OAI.SKFluctuations.Cavity
