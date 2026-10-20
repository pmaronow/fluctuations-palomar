module

public import SKConstants.Completion.N7.ScalarMean
public import SKConstants.Completion.N7.Quadrature
public import SKConstants.BrownianMartingaleIdentification

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology InnerProductSpace

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK LC4a LM4 LM4b
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

theorem integral_mul_tendsto_of_meanSquare {U : Type*} [MeasurableSpace U]
    {μ : Measure U} {S : ℕ → U → ℝ} {J L : U → ℝ}
    (hS : ∀ l, MemLp (S l) 2 μ) (hJ : MemLp J 2 μ) (hL : MemLp L 2 μ)
    (hlim : Tendsto (fun l => ∫ u, (S l u - J u) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun l => ∫ u, L u * S l u ∂μ) atTop (𝓝 (∫ u, L u * J u ∂μ)) := by
  have h := (tendsto_const_nhds (x := hL.toLp L)).inner (𝕜 := ℝ)
    (tendsto_toLp_of_meanSquare hS hJ hlim)
  have he (f : U → ℝ) (hf : MemLp f 2 μ) :
      ⟪hL.toLp L, hf.toLp f⟫_ℝ = ∫ u, L u * f u ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hL.coeFn_toLp, hf.coeFn_toLp] with u hu hv
    rw [hu, hv]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  simpa only [he] using h

theorem actualRowDLeftSum_mean_tendsto
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    Tendsto (fun l => ∫ u, actualRowDLeftSum W Z β hβ V l u
      ∂actualParisiFullQuerySpinLaw W Z β V) atTop
      (𝓝 (∫ r in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β r) ^ 2 *
        actualParisiFullSusceptibilityExpected W β r)) := by
  simp_rw [actualRowDLeftSum_mean W Z β hβ V]
  have h := left_integrated_quadrature_tendsto
    (actualParisiQuerySigma W β)
    (fun r => actualParisiQuerySigma W β r * actualParisiFullSusceptibilityExpected W β r)
    (continuous_actualParisiQuerySigma W β)
    ((continuous_actualParisiQuerySigma W β).mul
      (continuous_actualParisiFullSusceptibilityExpected W β))
    (fun r => by
      rw [abs_mul, abs_of_nonneg (actualParisiQuerySigma_bounds W β hβ r).1]
      have hp : |actualParisiFullSusceptibilityExpected W β r| ≤ 1 := by
        rw [← Real.norm_eq_abs]
        simpa only [actualParisiFullSusceptibilityExpected, probReal_univ, mul_one] using
          norm_integral_le_of_norm_le_const (μ := W.law) (C := 1)
            (f := fun w => actualParisiFullCurvature β r
              (actualParisiFullScalarProcess W β r.toNNReal w))
            (ae_of_all _ (fun w => by
              rw [Real.norm_eq_abs]
              exact actualParisiFullCurvature_abs_le_one β r _))
      exact (mul_le_mul (actualParisiQuerySigma_bounds W β hβ r).2 hp
        (abs_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l i _ => brownianDyadicGrid_width_le V l i)
  simpa only [one_mul, brownianDyadicGrid_horizon, pow_two, mul_assoc] using h

theorem actualRowDIntegral_mean
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0)
    (J : (Bool × Ω) × A → ℝ) (hJ : IsActualRowDIntegral W Z β hβ V J) :
    (∫ u, J u ∂actualParisiFullQuerySpinLaw W Z β V) =
      ∫ r in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β r) ^ 2 *
        actualParisiFullSusceptibilityExpected W β r := by
  let μ := actualRowBaseLaw W Z
  let L : (Bool × Ω) × A → ℝ := fun u => actualParisiFullTerminalSpinDensity β W V u.1
  have hLm : Measurable L := (measurable_actualParisiFullTerminalSpinDensity β W V).comp measurable_fst
  have hL : MemLp L 2 μ := (memLp_const (2 : ℝ)).mono' hLm.aestronglyMeasurable
    (ae_of_all _ (fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (actualParisiFullTerminalSpinDensity_pos β W V u.1)]
      exact actualParisiSpinLinkDensity_le_two β u.1.1 V _))
  have hS (l : ℕ) : MemLp (actualRowDLeftSum W Z β hβ V l) 2 μ := by
    have he : MemLp (fun u => actualRowDLeftSum W Z β hβ V l u - J u) 2 μ :=
      (memLp_two_iff_integrable_sq
        (((measurable_actualRowDLeftSum W Z β hβ V l).aemeasurable.sub
          hJ.1.aemeasurable).aestronglyMeasurable)).mpr (hJ.2.1 l)
    convert he.add hJ.1 using 1
    funext u
    simp only [Pi.add_apply, sub_add_cancel]
  have hlink : actualParisiFullQuerySpinLaw W Z β V =
      μ.withDensity (fun u => ENNReal.ofReal (L u)) := by
    unfold actualParisiFullQuerySpinLaw actualParisiFullTerminalSpinLaw
    rw [prod_withDensity_left (measurable_actualParisiFullTerminalSpinDensity β W V).ennreal_ofReal]
    rfl
  have hmean (F : (Bool × Ω) × A → ℝ) :
      (∫ u, F u ∂actualParisiFullQuerySpinLaw W Z β V) = ∫ u, L u * F u ∂μ := by
    rw [hlink, integral_withDensity_eq_integral_toReal_smul hLm.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (actualParisiFullTerminalSpinDensity_pos β W V _).le,
      smul_eq_mul, L]
  have hlim := integral_mul_tendsto_of_meanSquare hS hJ.1 hL hJ.2.2
  simp_rw [← hmean] at hlim
  exact tendsto_nhds_unique hlim (actualRowDLeftSum_mean_tendsto W Z β hβ V)

end SKConstants.Completion.N7
