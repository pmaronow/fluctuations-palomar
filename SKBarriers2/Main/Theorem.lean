module

public import SKBarriers2.Main.Leaves4
public import SKBarriers2.Corner.PathEnergyClose
public import SKBarriers2.Corner.FrozenRowsMixedClose
public import SKBarriers2.Corner.FrozenRowsNoise7
public import SKBarriers2.Corner.FrozenRowsPotential11

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace SKBarriers2

theorem scalarData_openLeaves4 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    Corner.OpenLeaves4 β (cdf (D.μ : Measure ℝ)) (Icc l u) :=
  ⟨Corner.scalarData_frozenPartitionKDerivativeWeak_of_parts D hl hu
      (Corner.scalarData_frozenRowsMixedStep D hl hu)
      (Corner.scalarData_frozenRowsNoiseRegularity D hl hu)
      (Corner.scalarData_frozenRowsPotentialKBounds D hl hu),
    Corner.scalarData_pathEnergyC2 D hl hu⟩

private theorem scalarData_openLeaves4_windows :
    ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        Corner.OpenLeaves4 β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u) := by
  intro β hβ
  refine ⟨(scalarData β hβ).q, (scalarData β hβ).q_mem.1, le_rfl, ?_⟩
  intro l u hl _ hu
  exact scalarData_openLeaves4 (scalarData β hβ) hl hu

theorem mainStatement : OAI.SK.Strengthened.MainStatement :=
  mainStatement_of_leaves4 scalarData_openLeaves4_windows

theorem subcriticalStatement : OAI.SK.Strengthened.SubcriticalStatement :=
  subcriticalStatement_of_leaves4 scalarData_openLeaves4_windows

end SKBarriers2
