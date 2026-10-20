module

public import ComparisonSignedCavityActualResourceRetainedGammaNorm
public import ComparisonSignedCavityActualFourGaSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

def nativeActualOriginalFourRetainedGammaError
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0;
  -((W⁻¹)^st.generation/(chi*K star))*nativeActualOriginalFourOtherCategoryContrast M U st .gammaRetained

theorem actual_minimum_four_retained_gamma_error_eq_rows
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {i U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) i (pre.length+mid.length))
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed st.generation st.tree st.term)
    (hi : i ≤ (pre.length+mid.length)) (hs : (pre.length+mid.length) < U) (ho : MassOrdered 0 (pre++(mid++tail))) (W V : ℝ) (hV : V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) U)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail))
    nativeActualOriginalFourRetainedGammaError M U W st=
      ((M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)/(2*K (pre.length+mid.length)))*
        ((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V st.term-
          (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0))) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail))
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks (pre++(mid++tail)) (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone (pre++(mid++tail)) ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone (pre++(mid++tail)) ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K (pre++(mid++tail)).length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hc : chi≠0:=ne_of_gt ((Real.exp_pos _).trans_le Hchi.1)
  unfold nativeActualOriginalFourRetainedGammaError
  rw [actual_minimum_four_retained_gamma_category_eq_projected_rows M st hP hi hs ho V hV]
  dsimp only
  let b : ℝ:=(M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)
  change -((W⁻¹)^st.generation/(chi*K (pre.length+mid.length)))*
    ((-chi*b/2)*(nativeActualResourceRetainedGammaRow M U V st.term-
        (1/2:ℝ)*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0))) =
    (b/(2*K (pre.length+mid.length)))*
      ((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V st.term-
        (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0)))
  by_cases hk : K (pre.length+mid.length)=0
  · simp only [hk,mul_zero,div_zero,neg_zero,zero_mul]
  · field_simp [hc,hk]

theorem actual_minimum_four_retained_gamma_error_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {pre mid tail : List PositiveMass} {i U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) i (pre.length+mid.length))
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed st.generation st.tree st.term)
    (hi : i ≤ pre.length+mid.length) (hs : pre.length+mid.length < U)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ)
    (hV : V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) U))
    {W cK B Temp : ℝ} (hW : 0<W) (hcK : 0<cK) (hB : 0≤B) (hTemp : 0≤Temp)
    (hb : (M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ) ≤ Temp)
    (hK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail)) (pre.length+mid.length))
    (H0 : |(W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V st.term| ≤
      |st.term.coefficient| *W*B)
    (H1 : |(W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0)| ≤
      |st.term.coefficient| *W*B) :
    |nativeActualOriginalFourRetainedGammaError M U W st| ≤
      |st.term.coefficient| *(Temp/cK)*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf (pre++(mid++tail)) (pre.length+mid.length)
  have hK0 : 0<K:=(mul_pos hcK hW).trans_le hK
  have hterm : 0≤|st.term.coefficient| *W*B:=by positivity
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V st.term)
    0
    ((1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg] at Hdiff
  have Hdiff' : |(W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*nativeActualResourceRetainedGammaRow M U V (st.term.retarget 0))| ≤
      2*(|st.term.coefficient| *W*B):=by
    rw [abs_mul (1/2:ℝ),abs_of_pos (show (0:ℝ)<1/2 by norm_num)] at Hdiff
    linarith
  rw [actual_minimum_four_retained_gamma_error_eq_rows M st hP hi hs ho W V hV]
  rw [abs_mul,abs_of_nonneg (show 0≤(M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)/(2*K) by positivity)]
  apply (mul_le_mul_of_nonneg_left Hdiff' (by positivity)).trans
  have Hfrac : (M.bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)/(2*K) ≤ Temp/(2*(cK*W)):=
    div_le_div₀ hTemp hb (mul_pos (by norm_num) (mul_pos hcK hW))
      (mul_le_mul_of_nonneg_left hK (by norm_num))
  apply (mul_le_mul_of_nonneg_right Hfrac (by positivity)).trans_eq
  field_simp

end OAI.SKFluctuations.Cavity
