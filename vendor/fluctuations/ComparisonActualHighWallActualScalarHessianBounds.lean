module

public import ComparisonActualHighWallSourceIdentification
public import ComparisonSignedCavityActualFourForestNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData (n+1) delta)

theorem actual_scalar_boundary_chi_abs_le_one (alpha : a.Profile)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (U : ℕ) (hUp : 0<U) (hU : U≤as.length) :
    let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
    |(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0|≤1 := by
  let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hKm:=native_continuum_mixed_clock_monotone n (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) as ho
  have hK0:=native_continuum_mixed_clock_nonneg n (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) as ho
  have hterm : K as.length≤a.T:=
    (native_continuum_mixed_clock_terminal_le n (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha) as ho).trans
      (a.total_clock_le alpha 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,hUp])
    (B:=a.T) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  have hchi0 : 0≤chi:=(Real.exp_pos (-4*a.T)).le.trans HH.1
  change |chi|≤1
  rw [abs_of_nonneg hchi0]
  exact HH.2

end ActualHighWallData
end OAI.SKFluctuations.Cavity
