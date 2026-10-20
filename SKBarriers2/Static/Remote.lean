module

public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Locking.NarrowContinuumTrial
public import OAI.Probability.SKBarriers.Locking.NarrowNegativeCoefficient
public import OAI.Probability.SKBarriers.Locking.NarrowScaleAlgebra
public import OAI.Probability.SKBarriers.Locking.TripleNegativeCoefficient
public import OAI.Probability.SKBarriers.Parisi.CommonMinimizer

@[expose] public section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set OAI.SK OAI.SK.Analytic

namespace SKBarriers2

private theorem lipschitz_window_oscillation {α : ℝ → ℝ} {K : ℝ≥0}
    {a b H r h : ℝ} (hLip : LipschitzOnWith K α (Icc (a - H) (b + H)))
    (hr : r ∈ Icc a b) (hh : 0 ≤ h) (hhH : h ≤ H) :
    α (r + h) - α (r - h) ≤ 2 * (K : ℝ) * h := by
  have hp : r + h ∈ Icc (a - H) (b + H) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hm : r - h ∈ Icc (a - H) (b + H) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hd := hLip.dist_le_mul (r + h) hp (r - h) hm
  rw [Real.dist_eq, Real.dist_eq, show r + h - (r - h) = 2 * h by ring,
    abs_of_nonneg (by linarith : 0 ≤ 2 * h)] at hd
  exact (le_abs_self _).trans (by nlinarith only [hd])

theorem remote_pressure_gap {β a b u H d₀ m : ℝ} (hβ : β ≠ 0)
    (ha : 0 < a) (hab : a ≤ b) (hbu : b < u) (hu : u ≤ 1)
    (hH : 0 < H) (hd₀ : 0 < d₀) (hm : 0 < m)
    (α : StieltjesFunction ℝ) (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hα1 : α 1 = 1)
    (hmα : m ≤ α a) (K : ℝ≥0)
    (hLip : LipschitzOnWith K α (Icc (a - H) (b + H)))
    (hΓ : ∀ t ∈ Icc a u, scalarCDFOverlap β α t = t)
    (hS : ∀ q ∈ Icc (0 : ℝ) 1, scalarCDFSusceptibilityAverage β α q =
      (∫ x in q..1, α x) + α q * (q - scalarCDFOverlap β α q)) :
    ∃ ν δ₀ c : ℝ, 0 < ν ∧ 0 < δ₀ ∧ 0 < c ∧
      ∀ N : ℕ, 0 < N → ∀ r ∈ Icc a b, ∀ q δ : ℝ,
        d₀ ≤ q - r → q ≤ 1 → |q - scalarCDFOverlap β α q| ≤ ν → |δ| ≤ δ₀ →
        Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
        matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤ 3 * scalarCDFParisi β α - c * δ ^ 2 := by
  let C := narrowCDFErrorConstant β
  let k := β ^ 2 * m * scalarJointLossConstant β m
  have hC : 0 ≤ C := narrowCDFErrorConstant_nonneg β
  have hk : 0 < k := mul_pos (mul_pos (sq_pos_of_ne_zero hβ) hm)
    (scalarJointLossConstant_pos hβ hm)
  obtain ⟨θ, hθ, hθsmall⟩ := continuousAt_small_interval
    (show ContinuousAt (fun x : ℝ => C * x) 0 by fun_prop)
    (show C * 0 < k * d₀ / 8 by nlinarith only [mul_pos hk hd₀])
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hθC : C * θ ^ 2 ≤ k * θ * d₀ / 8 := by
    have ht := (hθsmall θ ⟨hθ.1.le, le_rfl⟩).le
    nlinarith only [mul_le_mul_of_nonneg_right ht hθ.1.le]
  let B := k * θ * d₀
  have hB : 0 < B := mul_pos (mul_pos hk hθ.1) hd₀
  have hcap : 0 < min a (min d₀ (min H 1)) := by positivity
  obtain ⟨h, hh, hhsmall⟩ := continuousAt_small_interval
    (show ContinuousAt (fun x : ℝ => C * (2 * (K : ℝ) * x)) 0 by fun_prop)
    (show C * (2 * (K : ℝ) * 0) < B / 8 by nlinarith only [hB]) hcap
  have hCa : C * (2 * (K : ℝ) * h) ≤ B / 8 := (hhsmall h ⟨hh.1.le, le_rfl⟩).le
  have hha : h ≤ a := hh.2.le.trans (min_le_left _ _)
  have hhd : h ≤ d₀ := hh.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhH : h ≤ H := hh.2.le.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hh1 : h ≤ 1 := hh.2.le.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨ν, hν, hνsmall⟩ := continuousAt_small_interval
    (show ContinuousAt (fun x : ℝ => 3 * β ^ 2 * x / h) 0 by fun_prop)
    (show 3 * β ^ 2 * 0 / h < B / 8 by simpa only [mul_zero, zero_div] using (div_pos hB (by norm_num : (0 : ℝ) < 8)))
    zero_lt_one
  let ε := h / narrowExpansionDenominator β
  have hε : 0 < ε := div_pos hh.1
    (lt_of_lt_of_le zero_lt_one (narrowExpansionDenominator_ge_one β))
  obtain ⟨d, hd, hdsmall⟩ := continuousAt_small_interval
    (show ContinuousAt (fun x : ℝ => 4 * x ^ 2) 0 by fun_prop)
    (show 4 * (0 : ℝ) ^ 2 < ε by simpa using hε) zero_lt_one
  let Q := (2 * (1 - θ) ^ 2 + θ ^ 2) / h
  obtain ⟨δ₀, hδ₀, hrem⟩ := continuousAt_small_interval
    (show ContinuousAt (fun x : ℝ => tripleExpansionConstant ε * x + β ^ 2 * Q ^ 2 * x ^ 2) 0 by fun_prop)
    (show tripleExpansionConstant ε * 0 + β ^ 2 * Q ^ 2 * 0 ^ 2 < B / 4 by simpa using (div_pos hB (by norm_num : (0 : ℝ) < 4))) hd.1
  refine ⟨ν, δ₀, B / 4, hν.1, hδ₀.1, div_pos hB (by norm_num), ?_⟩
  intro N hN r hr q δ hdist hq hdev hδ hD
  have hr0 : 0 ≤ r := ha.le.trans hr.1
  have hrq : r ≤ q := by linarith
  have hru : r < u := hr.2.trans_lt hbu
  have hcontact : ∀ t ∈ Icc r u, scalarCDFOverlap β α t = t := by
    intro t ht
    exact hΓ t ⟨hr.1.trans ht.1, ht.2⟩
  have hcoef := narrowCDFTrialCoefficient_quantitative hβ α hα hα1 hh.1 hr0 hrq hq hru hu
    hcontact hm (hmα.trans (α.mono hr.1))
    (show 1 / 2 ≤ 1 - θ by linarith [hθ.2]) hθ.1.le (by ring : (1 - θ) + θ = 1)
    (hS q ⟨hr0.trans hrq, hq⟩) hdev
  have hosc := mul_le_mul_of_nonneg_left (lipschitz_window_oscillation hLip hr hh.1.le hhH) hC
  have hνC : 3 * β ^ 2 * ν / h ≤ B / 8 := (hνsmall ν ⟨hν.1.le, le_rfl⟩).le
  have hloss := mul_le_mul_of_nonneg_left hdist (mul_nonneg hk.le hθ.1.le)
  have hcoef' : narrowCDFTrialCoefficient β α r h q (1 - θ) θ ≤ -B / 2 := by
    change _ ≤ _ + C * (_ + θ ^ 2) - k * θ * (q - r) at hcoef
    change C * θ ^ 2 ≤ B / 8 at hθC
    change B ≤ k * θ * (q - r) at hloss
    nlinarith only [hcoef, hosc, hCa, hνC, hθC, hloss, hB]
  have hδd : |δ| ≤ d := hδ.trans hδ₀.2.le
  have hδsmall : 4 * δ ^ 2 ≤ ε := by
    simpa only [sq_abs] using (hdsmall |δ| ⟨abs_nonneg _, hδd⟩).le
  have hp := narrowConstrainedPressure_continuum_trial hN β δ α hα hα1 hh.1
    (hha.trans hr.1) (by linarith) hq (show 0 < 1 - θ by linarith [hθ.2]) hθ.1.le
    (by ring : (1 - θ) + θ = 1) hD hε hδsmall (hδd.trans hd.2.le)
    (narrowExpansion_smallness β hh.1 hh1 (by linarith [hθ.2]) hθ.1.le (by ring))
  have hrem' := mul_le_mul_of_nonneg_left (hrem |δ| ⟨abs_nonneg _, hδ⟩).le (sq_nonneg δ)
  have heq : δ ^ 2 * (tripleExpansionConstant ε * |δ| + β ^ 2 * Q ^ 2 * |δ| ^ 2) =
      tripleExpansionConstant ε * |δ| ^ 3 + β ^ 2 * δ ^ 4 * Q ^ 2 := by
    rw [show |δ| ^ 3 = |δ| ^ 2 * |δ| by ring, sq_abs]
    ring
  rw [heq] at hrem'
  have hcδ := mul_le_mul_of_nonneg_left hcoef' (sq_nonneg δ)
  change _ ≤ 3 * scalarCDFParisi β α + δ ^ 2 * _ + tripleExpansionConstant ε * |δ| ^ 3 + β ^ 2 * δ ^ 4 * Q ^ 2 at hp
  nlinarith only [hp, hrem', hcδ]

theorem susceptibility_identity_of_unique_minimizer {β : ℝ} (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ)
    (hunique : ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ) :
    ∀ q ∈ Icc (0 : ℝ) 1, scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) q =
      (∫ x in q..1, cdf (μ : Measure ℝ) x) + cdf (μ : Measure ℝ) q *
        (q - scalarCDFOverlap β (cdf (μ : Measure ℝ)) q) := by
  obtain ⟨ν, hν, hmin, _, _, _, _, hS⟩ := exists_scalarCDFParisi_minimizer_locking_data hβ
  exact hunique ν hν hmin ▸ hS

theorem remote_pressure_gap_of_unique_minimizer {β a b u H d₀ m : ℝ} (hβ : β ≠ 0)
    (ha : 0 < a) (hab : a ≤ b) (hbu : b < u) (hu : u ≤ 1)
    (hH : 0 < H) (hd₀ : 0 < d₀) (hm : 0 < m)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hunique : ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0 : ℝ) 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β → ν = μ)
    (hmα : m ≤ cdf (μ : Measure ℝ) a) (K : ℝ≥0)
    (hLip : LipschitzOnWith K (cdf (μ : Measure ℝ)) (Icc (a - H) (b + H)))
    (hΓ : ∀ t ∈ Icc a u, scalarCDFOverlap β (cdf (μ : Measure ℝ)) t = t) :
    ∃ ν δ₀ c : ℝ, 0 < ν ∧ 0 < δ₀ ∧ 0 < c ∧
      ∀ N : ℕ, 0 < N → ∀ r ∈ Icc a b, ∀ q δ : ℝ,
        d₀ ≤ q - r → q ≤ 1 → |q - scalarCDFOverlap β (cdf (μ : Measure ℝ)) q| ≤ ν → |δ| ≤ δ₀ →
        Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
        matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤ 3 * finiteParisiInf β - c * δ ^ 2 := by
  simpa only [hmin] using remote_pressure_gap hβ ha hab hbu hu hH hd₀ hm
    (cdf (μ : Measure ℝ)) (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (supported_probability_cdf_one μ hμ) hmα K hLip hΓ
    (susceptibility_identity_of_unique_minimizer hβ μ hunique)

end SKBarriers2
