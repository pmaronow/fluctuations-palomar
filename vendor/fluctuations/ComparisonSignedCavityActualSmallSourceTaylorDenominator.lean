module

public import ComparisonSignedCavityActualSmallSourceFourWeights
public import ComparisonSignedCavityActualFourResidualDecomposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem actual_minimum_four_denominator_bounds_of_small_source_clocks
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp Cf W cK : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCf : 0 ≤ Cf) (HS : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
    (hW : 0 < W) (hcK : 0 < cK) {as : List PositiveMass} (ho : MassOrdered 0 as)
    {star U : ℕ} (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    0<chi*K star ∧ chi ≤ 1 ∧ Real.exp (-4*(Temp+2*Cf))*cK*W ≤ chi*K star := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hterminal : K as.length ≤ Temp+2*Cf:=by
    apply (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans
    have HH:=HS 1 (by norm_num)
    have HF:=mul_le_mul_of_nonneg_left (show M.xs+1 ≤ 2 by linarith) hCf
    linarith
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK)
    (by simp [relocatedClock,show 0<U by omega])
    (B:=Temp+2*Cf) (by simpa [relocatedClock,not_lt.mpr hU] using hterminal)
  have hchi:=(Real.exp_pos (-4*(Temp+2*Cf))).trans_le HH.1
  have hp : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  refine ⟨mul_pos hchi hp,HH.2,?_⟩
  simpa only [mul_assoc] using mul_le_mul HH.1 hstarK (mul_pos hcK hW).le hchi.le

end OAI.SKFluctuations.Cavity
