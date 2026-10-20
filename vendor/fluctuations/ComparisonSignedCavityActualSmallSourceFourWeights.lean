module

public import ComparisonSignedCavityActualFourGContinuumWeights
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 10000000

theorem actual_continuum_four_G_weight_bound_of_small_source_clocks
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf W cK : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (hsource : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (hW : 0<W) (hcK : 0<cK) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {i star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)| ≤
      (Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterminal : K as.length ≤ Temp+2*Cf:=by
    apply (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans
    have HH:=hsource 1 (by norm_num)
    have HF:=mul_le_mul_of_nonneg_left (show M.xs+1 ≤ 2 by linarith) hCf
    linarith
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro t
  have hbeta : |nativeOriginalClockGBranchBeta U K b st t| ≤ Temp+2*Cf:=by
    let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
    obtain ⟨hlo,hhi⟩:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
      hU K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
    have hchi : 0 ≤ chi:=(Real.exp_pos _).le.trans hlo
    have hb : b star ≤ Temp+2*Cf:=by
      have H:=(hsource _ (partitionPoint_mem as ho star)).1
      dsimp only [b] at H ⊢
      linarith
    have hb0 : 0 ≤ b star:=NNReal.coe_nonneg _
    unfold nativeOriginalClockGBranchBeta
    change |(if t=0 then chi else 1)*b star| ≤ Temp+2*Cf
    split_ifs
    · rw [abs_of_nonneg (mul_nonneg hchi hb0)]
      exact (mul_le_mul_of_nonneg_right hhi hb0).trans (by simpa only [one_mul] using hb)
    · simpa only [one_mul,abs_of_nonneg hb0] using hb
  have H:=native_full_gamma_recursion_coefficient_bound n st.tree ho 0 ho U (by omega)
    hU K hKm hK hterminal st.term.live.test.target hW hcK hstarK hbeta
  unfold nativeOriginalClockParentWeight
  rw [abs_mul,abs_of_pos hW]
  apply (mul_le_mul_of_nonneg_left H hW.le).trans
  apply le_of_eq
  field_simp

end OAI.SKFluctuations.Cavity
