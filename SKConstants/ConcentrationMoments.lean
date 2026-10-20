module

public import SKConstants.ConcentrationMGF
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Tactic

public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace SKConstants.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem localQuadraticMGF_of_factorial_moments [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {v B : ℝ} (hMeas : Measurable X) (hv : 0 ≤ v) (hB : 0 < B)
    (hPowers : ∀ p : ℕ, Integrable (fun ω ↦ (X ω) ^ p) μ)
    (hMean : ∫ ω, X ω ∂μ = 0)
    (hMoments : ∀ p : ℕ, 2 ≤ p →
      (∫ ω, |X ω| ^ p ∂μ) ≤ (p.factorial : ℝ) * v * B ^ (p - 2)) :
    LocalQuadraticMGF X μ (2 * v) (1 / (2 * B)) := by
  have hAt (t : ℝ) (ht : |t| ≤ 1 / (2 * B)) :
      Integrable (fun ω ↦ Real.exp (t * X ω)) μ ∧
        mgf X μ t ≤ Real.exp ((2 * v) * t ^ 2) := by
    let F : ℕ → Ω → ℝ := fun p ω ↦ (t * X ω) ^ p / (p.factorial : ℝ)
    let q : ℝ := |t| * B
    have hq0 : 0 ≤ q := by positivity
    have hq : q ≤ 1 / 2 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2 * B)).mp ht
      dsimp [q]
      nlinarith
    have hq1 : q < 1 := by linarith
    have hFInt (p : ℕ) : Integrable (F p) μ := by
      convert (hPowers p).const_mul (t ^ p / (p.factorial : ℝ)) using 1
      ext ω
      simp only [F, mul_pow]
      ring
    have hNormF (p : ℕ) : (fun ω ↦ ‖F p ω‖) =
        fun ω ↦ (|t| ^ p / (p.factorial : ℝ)) * |X ω| ^ p := by
      ext ω
      simp only [F, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
        abs_of_nonneg (show (0 : ℝ) ≤ (p.factorial : ℝ) by positivity)]
      ring
    have hTail (k : ℕ) : (∫ ω, ‖F (k + 2) ω‖ ∂μ) ≤ v * t ^ 2 * q ^ k := by
      rw [hNormF, integral_const_mul]
      have hm := hMoments (k + 2) (by omega)
      simp only [Nat.add_sub_cancel_right] at hm
      calc
        _ ≤ (|t| ^ (k + 2) / ((k + 2).factorial : ℝ)) *
            (((k + 2).factorial : ℝ) * v * B ^ k) := by
          exact mul_le_mul_of_nonneg_left hm (by positivity)
        _ = v * t ^ 2 * q ^ k := by
          have hfac : ((k + 2).factorial : ℝ) ≠ 0 := by positivity
          dsimp [q]
          rw [pow_add, mul_pow]
          field_simp
          rw [sq_abs]
          ring
    have hGeom : Summable (fun k : ℕ ↦ q ^ k) := summable_geometric_of_lt_one hq0 hq1
    have hGeomScaled : Summable (fun k : ℕ ↦ v * t ^ 2 * q ^ k) :=
      hGeom.mul_left (v * t ^ 2)
    have hTailSummable : Summable (fun k : ℕ ↦ ∫ ω, ‖F (k + 2) ω‖ ∂μ) :=
      hGeomScaled.of_nonneg_of_le (fun k ↦ integral_nonneg (fun ω ↦ norm_nonneg _)) hTail
    have hNormSummable : Summable (fun p : ℕ ↦ ∫ ω, ‖F p ω‖ ∂μ) :=
      (summable_nat_add_iff 2).mp hTailSummable
    have hENsum : (∑' p : ℕ, ∫⁻ ω, ‖F p ω‖ₑ ∂μ) < ⊤ := by
      calc
        _ = ∑' p : ℕ, ENNReal.ofReal (∫ ω, ‖F p ω‖ ∂μ) := by
          exact tsum_congr (fun p ↦ (ofReal_integral_norm_eq_lintegral_enorm (hFInt p)).symm)
        _ < ⊤ := hNormSummable.tsum_ofReal_lt_top
    have hSeries (ω : Ω) : HasSum (fun p : ℕ ↦ F p ω) (Real.exp (t * X ω)) := by
      simpa only [F, Real.exp_eq_exp_ℝ] using
        NormedSpace.expSeries_div_hasSum_exp (t * X ω)
    have hExpInt : Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
      refine ⟨by fun_prop, ?_⟩
      change (∫⁻ ω, ‖Real.exp (t * X ω)‖ₑ ∂μ) < ⊤
      calc
        _ ≤ ∫⁻ ω, ∑' p : ℕ, ‖F p ω‖ₑ ∂μ := by
          apply lintegral_mono
          intro ω
          change ‖Real.exp (t * X ω)‖ₑ ≤ ∑' p : ℕ, ‖F p ω‖ₑ
          rw [← (hSeries ω).tsum_eq]
          exact enorm_tsum_le_tsum_enorm
        _ = ∑' p : ℕ, ∫⁻ ω, ‖F p ω‖ₑ ∂μ :=
          lintegral_tsum (fun p ↦ (hFInt p).aestronglyMeasurable.enorm)
        _ < ⊤ := hENsum
    have hSumIntegral := hasSum_integral_of_summable_integral_norm hFInt hNormSummable
    have hMGF : mgf X μ t = ∑' p : ℕ, ∫ ω, F p ω ∂μ := by
      rw [hSumIntegral.tsum_eq]
      unfold mgf
      apply integral_congr_ae
      filter_upwards with ω
      exact (hSeries ω).tsum_eq.symm
    have hFirst : (∑ p ∈ Finset.range 2, ∫ ω, F p ω ∂μ) = 1 := by
      simp [Finset.sum_range_succ, F, integral_const_mul, hMean]
    have hMGFSplit : mgf X μ t = 1 + ∑' k : ℕ, ∫ ω, F (k + 2) ω ∂μ := by
      rw [hMGF, ← hSumIntegral.summable.sum_add_tsum_nat_add 2, hFirst]
    have hInv : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div]
      apply (div_le_iff₀ (by linarith : 0 < 1 - q)).mpr
      linarith
    have hMGFBound : mgf X μ t ≤ Real.exp ((2 * v) * t ^ 2) := by
      calc
        _ = 1 + ∑' k : ℕ, ∫ ω, F (k + 2) ω ∂μ := hMGFSplit
        _ ≤ 1 + ∑' k : ℕ, v * t ^ 2 * q ^ k := by
          apply add_le_add le_rfl
          apply Summable.tsum_le_tsum _
            ((summable_nat_add_iff 2).mpr hSumIntegral.summable) hGeomScaled
          intro k
          have hn := norm_integral_le_integral_norm (μ := μ) (F (k + 2))
          rw [Real.norm_eq_abs] at hn
          exact ((le_abs_self _).trans hn).trans (hTail k)
        _ = 1 + (v * t ^ 2) * (1 - q)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
        _ ≤ 1 + 2 * v * t ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hInv (mul_nonneg hv (sq_nonneg t))]
        _ ≤ Real.exp ((2 * v) * t ^ 2) := by
          simpa only [add_comm] using Real.add_one_le_exp ((2 * v) * t ^ 2)
    exact ⟨hExpInt, hMGFBound⟩
  exact ⟨fun t ht ↦ (hAt t ht).1, fun t ht ↦ (hAt t ht).2⟩

end SKConstants.Concentration
