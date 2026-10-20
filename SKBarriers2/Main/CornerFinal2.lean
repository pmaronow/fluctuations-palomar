module

public import SKBarriers2.Corner.CoreValueAssembly
public import SKBarriers2.Main.CornerFinal

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace SKBarriers2

private theorem crude_value_windows_of_crude_terminal_massVariation {β : ℝ} (D : ScalarData β)
    (h : ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ D.q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
        Corner.TerminalFrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
        Corner.MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ D.q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
        CoreValue β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨l₀, hl₀, hl₀q, H⟩ := h
  refine ⟨l₀, hl₀, hl₀q, ?_⟩
  intro l u hl hlu hu
  obtain ⟨hcrude, hterminal, hmv⟩ := H l u hl hlu hu
  exact ⟨hcrude, Corner.scalarData_coreValue_of_terminal_massVariation D hl
    (hu.trans_le hl₀q) hterminal hmv⟩

theorem mainStatement_of_crude_terminal_massVariation
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        CrudeC1 β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u) ∧
        Corner.TerminalFrozenRemainderBound β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u) ∧
        Corner.MassVariationBound β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.MainStatement := by
  apply mainStatement_of_crude_value
  intro β hβ
  exact crude_value_windows_of_crude_terminal_massVariation (scalarData β hβ) (h β hβ)

theorem subcriticalStatement_of_crude_terminal_massVariation
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        CrudeC1 β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u) ∧
        Corner.TerminalFrozenRemainderBound β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u) ∧
        Corner.MassVariationBound β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.SubcriticalStatement := by
  apply subcriticalStatement_of_crude_value
  intro β hβ
  exact crude_value_windows_of_crude_terminal_massVariation (scalarData β hβ) (h β hβ)

end SKBarriers2
