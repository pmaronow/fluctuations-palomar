module

public import SKBarriers2.Corner.GapAssembly2
public import SKBarriers2.Main.FinalCorner

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace SKBarriers2

theorem cornerInputs_of_crude_value_windows {β : ℝ} (D : ScalarData β)
    (h : ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ D.q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
        CoreValue β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    CornerInputs β D := by
  obtain ⟨l₀, hl₀, hl₀q, H⟩ := h
  refine ⟨l₀, hl₀, hl₀q, ?_⟩
  intro l u hl hlu hu
  obtain ⟨hc, hv⟩ := H l u hl hlu hu
  exact cornerInputs_of_crude_value D hl hlu (hu.trans_le hl₀q) hc hv

theorem mainStatement_of_crude_value
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        CrudeC1 β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u) ∧
        CoreValue β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.MainStatement := by
  apply mainStatement_of_cornerInputs'
  intro β hβ
  exact cornerInputs_of_crude_value_windows (scalarData β hβ) (h β hβ)

theorem subcriticalStatement_of_crude_value
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        CrudeC1 β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u) ∧
        CoreValue β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.SubcriticalStatement := by
  apply subcriticalStatement_of_cornerInputs'
  intro β hβ
  exact cornerInputs_of_crude_value_windows (scalarData β hβ) (h β hβ)

end SKBarriers2
