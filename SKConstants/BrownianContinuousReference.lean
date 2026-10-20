module
public import SKConstants.BrownianFullPastLikelihood
public import SKConstants.BrownianQuadraticVariation
public import SKConstants.ScalarProcessRowMGFLimit

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianContinuousExponential {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianContinuousPastCoefficient A) (T : ℝ≥0) (I : A × Ω → ℝ) (u : A × Ω) : ℝ :=
  Real.exp (I u-brownianContinuousQuadraticVariation D H T u/2)

theorem brownianContinuousReference_exists {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianContinuousPastCoefficient A) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u, ‖H s u‖ ≤ C)
    (hc : ∀ᵐ u ∂P.prod Q, Continuous (fun s => brownianContinuousCoefficient D H s u))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l)
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    ∃ I : A × Ω → ℝ, MemLp I 2 (P.prod Q) ∧
      Tendsto (fun l => ∫ u, (brownianContinuousLeftSum D H G k l u-I u)^2 ∂P.prod Q)
        atTop (𝓝 0) ∧
      Integrable (brownianContinuousExponential D H (G.time 0 k) I) (P.prod Q) ∧
      (∫ u, brownianContinuousExponential D H (G.time 0 k) I u ∂P.prod Q) = 1 ∧
      IsProbabilityMeasure ((P.prod Q).withDensity (fun u => ENNReal.ofReal
        (brownianContinuousExponential D H (G.time 0 k) I u))) ∧
      (((P.prod Q).withDensity (fun u => ENNReal.ofReal
        (brownianContinuousExponential D H (G.time 0 k) I u))).map Prod.fst = P) ∧
      Tendsto (fun l => eLpNorm (brownianFullPastExponential D (G.time l)
        (brownianContinuousMeshCoefficient H (G.time l)) 1 (k*2^l)-
          brownianContinuousExponential D H (G.time 0 k) I) 1 (P.prod Q)) atTop (𝓝 0) := by
  obtain ⟨I,hI,hIi,hIlim⟩ := brownianContinuousLeftSum_exists_L2_limit P Q D hD hmD H hH C hC hc
    G k δ hδ hleft
  obtain ⟨hVm,hVi,hVlim⟩ := brownianContinuousVariation_tendsto_L2 P Q D hD hmD H hH C hC hc
    G k δ hδ hwidth
  have hIm := tendstoInMeasure_of_tendsto_integral_sq hIi hIlim
  have hVmprob := tendstoInMeasure_of_tendsto_integral_sq hVi hVlim
  have hsm (l : ℕ) : AEStronglyMeasurable (brownianContinuousLeftSum D H G k l) (P.prod Q) :=
    (memLp_brownianStaticPredictableSum P Q D hD hmD _ (G.monotone l) _
      (fun i => hH _) C (fun i u => hC _ _) _).aestronglyMeasurable
  have hbrm (l : ℕ) : AEStronglyMeasurable (brownianStaticPredictableVariation D (G.time l)
      (brownianContinuousMeshCoefficient H (G.time l)) (k*2^l)) (P.prod Q) :=
    (aemeasurable_predictableGaussianVariation (P.prod Q) _ _
      (aemeasurable_brownianStaticCoefficient P Q D hD hmD _ _ (fun i => hH _)) _).aestronglyMeasurable
  have hExp := tendstoInMeasure_continuous_two_real hsm hbrm hIm hVmprob
    (fun p : ℝ×ℝ => Real.exp (p.1-p.2/2)) (by fun_prop)
  have hlim : TendstoInMeasure (P.prod Q)
      (fun l => brownianFullPastExponential D (G.time l)
        (brownianContinuousMeshCoefficient H (G.time l)) 1 (k*2^l)) atTop
      (brownianContinuousExponential D H (G.time 0 k) I) := by
    convert hExp using 1
    · funext l u
      simp only [brownianFullPastExponential,one_mul,one_pow,brownianContinuousLeftSum]
    · rfl
  obtain ⟨hEint,hEpos,hEmean,hEprob,hEmarg,hEL1⟩ := brownianFullPast_density_limit P Q D hD hmD
    G.time G.monotone (fun l => k*2^l) (fun l => brownianContinuousMeshCoefficient H (G.time l))
    (fun l i => hH _) (C^2*(G.time 0 k : ℝ))
    (fun l u => brownianContinuousVariation_le D H C hC G k l u) _ hlim
  exact ⟨I,hI,hIlim,hEint,hEmean,hEprob,hEmarg,hEL1⟩

end SKConstants
