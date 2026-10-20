module

public import SKBarriers2.Corner.FrozenCoef10
public import SKBarriers2.Corner.FrozenRowsWeak
public import SKBarriers2.Corner.MassVariationNoEntropy

@[expose] public section

noncomputable section
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def OpenLeaves4 (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  FrozenPartitionKDerivativeWeak β α I ∧ PathEnergyC2 β α I

theorem scalarData_terminalFrozenRemainderBound_of_leaves4 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (HK : FrozenPartitionKDerivativeWeak β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    TerminalFrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨C, hC, hC₀, hhC, HC⟩ := scalarData_terminalSplitDerivativeControl D hl hu
  obtain ⟨K, hT, κ, hK, hhT, hκ, hκ₄, HT⟩ :=
    scalarData_terminalMixedThirdControl_of_kDerivatives_weak D hl hu HK
  obtain ⟨hD, hhD, HD⟩ := scalarData_terminalChainDifferentiation D hl hu
  have HJ := scalarData_frozenJetHypotheses_window D hl hu
  obtain ⟨hδ, Hcover⟩ := frozen_window_cover hl hu
  let η := min hD (min hC hT)
  have hη : 0 < η := lt_min hhD (lt_min hhC hhT)
  have hκhalf : κ ≤ 1 / 2 := hκ₄.trans (by norm_num)
  apply terminalFrozenRemainderBound_of_derivative_controls (C := C) (D := K)
    (h₀ := η) (κ := κ) HJ hC₀ hK hη hκ hκhalf hδ Hcover
    (HD.restrict (min_le_left _ _) hκhalf)
  · intro r hr h hh hhη z
    obtain ⟨hR, hF, hW⟩ := HC r hr h hh
      (hhη.trans ((min_le_right _ _).trans (min_le_left _ _))) z
    exact ⟨hR.restrict_radius hκ₄, hF.restrict_radius hκ₄, hW.restrict_radius hκ₄⟩
  · exact HT.restrict ((min_le_right _ _).trans (min_le_right _ _)) le_rfl

theorem scalarData_crude_terminal_massVariation_of_leaves4 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (H : OpenLeaves4 β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    CrudeC1 β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
      TerminalFrozenRemainderBound β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
      MassVariationBound β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  obtain ⟨hweak, hpath⟩ := H
  exact ⟨scalarData_crudeC1 D hl hu,
    scalarData_terminalFrozenRemainderBound_of_leaves4 D hl hu hweak,
    massVariationBound_of_scalarData_pathEnergyC2 D hl hu hpath⟩

end SKBarriers2.Corner

namespace SKBarriers2

theorem mainStatement_of_leaves4
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        Corner.OpenLeaves4 β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.MainStatement := by
  apply mainStatement_of_crude_terminal_massVariation
  intro β hβ
  obtain ⟨l₀, hl₀, hl₀q, H⟩ := h β hβ
  refine ⟨l₀, hl₀, hl₀q, ?_⟩
  intro l u hl hlu hu
  exact Corner.scalarData_crude_terminal_massVariation_of_leaves4 (scalarData β hβ)
    hl (hu.trans_le hl₀q) (H l u hl hlu hu)

theorem subcriticalStatement_of_leaves4
    (h : ∀ β (hβ : 1 < β), ∃ l₀ : ℝ, 0 < l₀ ∧ l₀ ≤ (scalarData β hβ).q ∧
      ∀ l u : ℝ, 0 < l → l ≤ u → u < l₀ →
        Corner.OpenLeaves4 β (cdf ((scalarData β hβ).μ : Measure ℝ)) (Icc l u)) :
    OAI.SK.Strengthened.SubcriticalStatement := by
  apply subcriticalStatement_of_crude_terminal_massVariation
  intro β hβ
  obtain ⟨l₀, hl₀, hl₀q, H⟩ := h β hβ
  refine ⟨l₀, hl₀, hl₀q, ?_⟩
  intro l u hl hlu hu
  exact Corner.scalarData_crude_terminal_massVariation_of_leaves4 (scalarData β hβ)
    hl (hu.trans_le hl₀q) (H l u hl hlu hu)

end SKBarriers2
