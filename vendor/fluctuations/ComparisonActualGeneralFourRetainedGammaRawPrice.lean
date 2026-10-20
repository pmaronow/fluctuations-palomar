module

public import ComparisonActualGeneralFourRetainedGammaNorm

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000

theorem actual_general_four_retained_gamma_raw_abs_le
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (radius : ℝ→ℝ) (hRadius : Monotone radius)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {pre mid tail : List PositiveMass} {i U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) i (pre.length+mid.length))
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i (pre.length+mid.length) U seed st.generation st.tree st.term)
    (hi : i  ≤  pre.length+mid.length) (hs : pre.length+mid.length < U)
    (ho : MassOrdered 0 (pre++(mid++tail))) (V : ℝ) (hV : V  ≤  radius (partitionPoint 0 (pre++(mid++tail)) U))
    {W B Temp : ℝ} (hB : 0  ≤  B) (hTemp : 0  ≤  Temp)
    (hb : (bf (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)):ℝ)  ≤  Temp)
    (H0 : |(W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V st.term|  ≤  |st.term.coefficient| *B)
    (H1 : |(W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V (st.term.retarget 0)|  ≤  |st.term.coefficient| *B) :
    |(W⁻¹)^st.generation*actualGeneralFourCategoryContrast bf hf U st .gammaRetained|  ≤  
      |st.term.coefficient| *Temp*B := by
  let as:=pre++(mid++tail)
  let star:=pre.length+mid.length
  let K:=nativeContinuumMixedClock n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  have hKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hChi : |chi|  ≤  1:=by
    rw [abs_of_pos ((Real.exp_pos _).trans_le Hchi.1)]
    exact Hchi.2
  have Hdiff:=abs_sub_le
    ((W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V st.term) 0
    ((1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V (st.term.retarget 0)))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_pos (show (0:ℝ) < 1/2 by norm_num)] at Hdiff
  have HD : |(W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V (st.term.retarget 0))|  ≤  
      2*(|st.term.coefficient| *B):=by
    have hCo : 0  ≤  |st.term.coefficient| *B:=mul_nonneg (abs_nonneg _) hB
    have H0' := H0
    have H1' := H1
    simp only [abs_mul] at H0' H1'
    linarith
  rw [actual_general_four_retained_gamma_category_eq_projected_rows bf hf radius hRadius st hP hi hs ho V hV]
  have HE : (W⁻¹)^st.generation*((-chi*(bf (partitionPoint 0 as star):ℝ)/2)*
      (actualGeneralResourceRetainedGammaRow bf hf radius U V st.term-
      (1/2:ℝ)*actualGeneralResourceRetainedGammaRow bf hf radius U V (st.term.retarget 0)))=
      (-chi*(bf (partitionPoint 0 as star):ℝ)/2)*
      ((W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceRetainedGammaRow bf hf radius U V (st.term.retarget 0))):=by ring
  rw [HE,abs_mul]
  have HB : |-chi*(bf (partitionPoint 0 as star):ℝ)/2|  ≤  Temp/2:=by
    rw [abs_div,abs_mul,abs_neg,abs_of_nonneg (NNReal.coe_nonneg _),abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have H:=(mul_le_mul_of_nonneg_right hChi (NNReal.coe_nonneg (bf (partitionPoint 0 as star)))).trans (by simpa only [one_mul] using hb)
    exact div_le_div_of_nonneg_right H (by norm_num)
  apply (mul_le_mul HB HD (abs_nonneg _) (by positivity)).trans_eq
  ring

end OAI.SKFluctuations.Cavity
