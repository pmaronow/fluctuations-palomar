module
public import SKConstants.BrownianContinuousReference
public import SKConstants.ScalarProcessVarianceBalance

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

theorem brownianContinuousLeftSum_secondMoment_tendsto {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod Q, Continuous (fun s => brownianContinuousCoefficient D H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    Tendsto (fun l => ∫ u, brownianContinuousLeftSum D H G k l u^2 ∂P.prod Q) atTop
      (𝓝 (∫ u, brownianContinuousQuadraticVariation D H (G.time 0 k) u ∂P.prod Q)) := by
  let V := C^2*(G.time 0 k : ℝ)
  let F : ℕ → A × Ω → ℝ := fun l => brownianStaticPredictableVariation D (G.time l)
    (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l)
  have hm (l : ℕ) : AEStronglyMeasurable (F l) (P.prod Q) :=
    (aemeasurable_predictableGaussianVariation (P.prod Q) _ _
      (aemeasurable_brownianStaticCoefficient P Q D hD hmD _ _ (fun i => hH _)) _).aestronglyMeasurable
  have hb (l : ℕ) (u : A × Ω) : ‖F l u‖ ≤ V := by
    have hF0 : 0 ≤ F l u := predictableGaussianVariation_nonneg _ _ _ _
    rw [Real.norm_eq_abs,abs_of_nonneg hF0]
    exact brownianContinuousVariation_le D H C hC G k l u
  have hpath : ∀ᵐ u ∂P.prod Q,Tendsto (fun l => F l u) atTop
      (𝓝 (brownianContinuousQuadraticVariation D H (G.time 0 k) u)) := by
    filter_upwards [hc] with u hu
    exact brownianContinuousVariation_tendsto_path D H G k δ hδ hwidth u hu
  have ht := tendsto_integral_of_dominated_convergence (μ := P.prod Q) (bound := fun _ => V)
    hm (integrable_const _) (fun l => ae_of_all _ (hb l)) hpath
  have he (l : ℕ) : (∫ u, brownianContinuousLeftSum D H G k l u^2 ∂P.prod Q) =
      ∫ u, F l u ∂P.prod Q :=
    (brownianStaticPredictableSum_L2_isometry P Q D hD hmD _ (G.monotone l) _
      (fun i => hH _) (integrable_brownianStaticCoefficient_sq_of_bounded P Q D hD hmD
        _ _ (fun i => hH _) C (fun i u => hC _ _)) _).2.2
  simp_rw [he]
  exact ht

theorem brownianContinuousIntegral_secondMoment {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod Q, Continuous (fun s => brownianContinuousCoefficient D H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l)
    (I : A × Ω → ℝ) (hI : MemLp I 2 (P.prod Q))
    (hIlim : Tendsto (fun l => ∫ u, (brownianContinuousLeftSum D H G k l u-I u)^2 ∂P.prod Q)
      atTop (𝓝 0)) :
    (∫ u, I u^2 ∂P.prod Q) =
      ∫ u, brownianContinuousQuadraticVariation D H (G.time 0 k) u ∂P.prod Q := by
  exact tendsto_nhds_unique
    (integral_sq_tendsto_of_meanSquare (fun l => memLp_brownianStaticPredictableSum P Q D hD hmD
      _ (G.monotone l) _ (fun i => hH _) C (fun i u => hC _ _) _) hI hIlim)
    (brownianContinuousLeftSum_secondMoment_tendsto P Q D hD hmD H hH C hC hc G k δ hδ hwidth)

end SKConstants
