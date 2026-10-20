module

public import SKBarriers2.Main.Theorem
public import SKBarriers2.StatementAt

@[expose] public section
noncomputable section
open scoped Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2

theorem conditionalRateData_of_cornerInputs_parametric {β γ v : ℝ}
    (hβ : 1 < β) (D : ScalarData β)
    (hγ : 0 < γ) (hγ' : γ < 3 / 4)
    (hmean : ∃ Cb, 0 < Cb ∧ MeanRate β γ Cb)
    (hvar : ∃ Cv, 0 < Cv ∧ VarianceCap β v Cv)
    (hv : v < 2 - 2 * γ)
    (hcorner : CornerInputs β D) : Nonempty (ConditionalRateData β γ) := by
  obtain ⟨Cb, _hCb, hmean⟩ := hmean
  obtain ⟨Cv, _hCv, hvar⟩ := hvar
  apply exists_conditionalRateData hβ hγ hγ' hmean hvar hv D.μ D.unique
  intro qs hqs _hqs1 cuts
  obtain ⟨l₀, hl₀, hl₀q, hcorner⟩ := hcorner
  let t : ℝ := min l₀ (min cuts.b' (min (cuts.b ^ 2 / 2) qs))
  have ht : 0 < t := lt_min hl₀ (lt_min cuts.b'_pos
    (lt_min (div_pos (sq_pos_of_pos cuts.b_pos) (by norm_num)) hqs))
  let l : ℝ := t / 4
  let r : ℝ := t / 2
  have hl : 0 < l := by dsimp only [l]; positivity
  have hlr : l < r := by dsimp only [l, r]; linarith
  have hrt : r < t := by dsimp only [r]; linarith
  have hrl₀ : r < l₀ := hrt.trans_le (min_le_left _ _)
  have hrq : r < D.q := hrl₀.trans_le hl₀q
  let d : ConditionalScalarData β D.μ := D.conditionalScalarData hl hlr.le hrq
  obtain ⟨hcubic, hboundary⟩ := hcorner l r hl hlr.le hrl₀
  obtain ⟨E₀, hE₀, hEs⟩ := localFractionalGap_of_cubicGap_uniform'
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) (cdf (D.μ : Measure ℝ)).mono
    D.minimizer hcubic D.floorTrial (D.localWindowGeometry hl hlr.le hrq) hboundary
  obtain ⟨g₀, hg₀, hgs⟩ := hEs E₀ ⟨hE₀, le_rfl⟩
  obtain ⟨S₀, hS₀, hSs⟩ := hgs (g₀ / 2) ⟨half_pos hg₀, by linarith⟩
  refine ⟨d, hlr, ?_, ?_, ?_, S₀, E₀, g₀ / 2, hS₀, hE₀, half_pos hg₀, ?_⟩
  · exact (show l < t by dsimp only [l]; linarith).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  · exact (show l < t by dsimp only [l]; linarith).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  · exact (show l < t by dsimp only [l]; linarith).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  · intro R hR
    obtain ⟨θ, hθ⟩ := exists_rateExponents hγ hγ'
    apply hSs S₀ ⟨hS₀, le_rfl⟩ (rateRho R γ) (rate_scales_tendsto_zero hθ R).1
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact mul_pos hR (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _)

theorem scalarData_cornerInputs_closed (β : ℝ) (hβ : 1 < β) :
    CornerInputs β (scalarData β hβ) := by
  let D := scalarData β hβ
  apply cornerInputs_of_crude_value_windows D
  refine ⟨D.q, D.q_mem.1, le_rfl, ?_⟩
  intro l u hl _hlu hu
  obtain ⟨hc, ht, hm⟩ := Corner.scalarData_crude_terminal_massVariation_of_leaves4
    D hl hu (scalarData_openLeaves4 D hl hu)
  exact ⟨hc, Corner.scalarData_coreValue_of_terminal_massVariation D hl hu ht hm⟩

theorem mainStatementAt_of_rate_data {γ : ℝ}
    (h : ∀ β : ℝ, 1 < β → Nonempty (ConditionalRateData β γ)) :
    OAI.SK.Strengthened.MainStatementAt (γ / 3) := by
  intro β hβ
  obtain ⟨d⟩ := h β hβ
  exact barrier_of_rate hβ d

theorem subcriticalStatementBelow_of_rate_data {γ : ℝ}
    (h : ∀ β : ℝ, 1 < β → Nonempty (ConditionalRateData β γ)) :
    OAI.SK.Strengthened.SubcriticalStatementBelow (γ / 3) := by
  intro β κ hβ hκ hκ' τ hτ hτ'
  obtain ⟨d⟩ := h β hβ
  exact subcritical_of_rate hβ d κ hκ hκ' τ hτ hτ'

end SKBarriers2
