module

public import ComparisonActualGeneralFourFirstHighSource
public import ComparisonActualGeneralFourFirstHighIteration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

theorem actual_general_four_first_high_error_eq_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (W : ℝ) :
    let K:=nativeContinuumMixedClock n bf hf as
    actualGeneralFourFirstHighError bf hf U W st=
      -((bf (partitionPoint 0 as star):ℝ)/K star)*
        ((W⁻¹)^st.generation*actualGeneralResourceFirstHigh bf hf U st.term-
          (1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceFirstHigh bf hf U (st.term.retarget 0))) := by
  let K:=nativeContinuumMixedClock n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  have hKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  have Hchi:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hP.highCut_le_length K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  rw [native_full_gamma_row_hessian n st.tree ho 0 ho U (by omega) K] at Hchi
  have hc : chi≠0:=ne_of_gt ((Real.exp_pos _).trans_le Hchi.1)
  unfold actualGeneralFourFirstHighError
  rw [actual_general_four_first_high_contrast_eq_resources bf hf hbf hhf st hP hi hs ho]
  dsimp only
  change -((W⁻¹)^st.generation/(chi*K star))*
    (chi*(bf (partitionPoint 0 as star):ℝ)*
      (actualGeneralResourceFirstHigh bf hf U st.term-
        (1/2:ℝ)*actualGeneralResourceFirstHigh bf hf U (st.term.retarget 0))) =
    -((bf (partitionPoint 0 as star):ℝ)/K star)*
      ((W⁻¹)^st.generation*actualGeneralResourceFirstHigh bf hf U st.term-
        (1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceFirstHigh bf hf U (st.term.retarget 0)))
  by_cases hk : K star=0
  · simp only [hk,mul_zero,div_zero,neg_zero,zero_mul]
  · field_simp [hc,hk]

end OAI.SKFluctuations.Cavity
