module
public import SKConstants.BrownianVectorPredictableLikelihood
public import SKConstants.BrownianVectorQuadraticVariation
public import SKConstants.ScalarProcessRowMGFLimit

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def brownianVectorContinuousExponential {A ι Ω : Type*} [Fintype ι] (D : ℝ≥0 → Ω → ℝ)
    (H : BrownianVectorContinuousPastCoefficient A ι) (T : ℝ≥0) (I : A × (ι → Ω) → ℝ) (u : A × (ι → Ω)) : ℝ :=
  Real.exp (I u-brownianVectorContinuousQuadraticVariation D H T u/2)

theorem brownianVectorContinuousReference_exists {A ι Ω : Type*} [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (H : BrownianVectorContinuousPastCoefficient A ι) (hH : ∀ s, Measurable (H s))
    (C : ℝ) (hC : ∀ s u i, ‖H s u i‖ ≤ C)
    (hc : ∀ i, ∀ᵐ u ∂P.prod (Measure.pi (fun _ : ι => Q)), Continuous (fun s => brownianVectorContinuousCoefficient D H s u i))
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hleft : ∀ l d i, i < k*2^(l+d) →
      |(G.time (l+d) i : ℝ)-G.time l (i/2^d)| ≤ δ l)
    (hwidth : ∀ l i, i < k*2^l → (G.time l (i+1) : ℝ)-G.time l i ≤ δ l) :
    ∃ I : A × (ι → Ω) → ℝ, MemLp I 2 (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      Tendsto (fun l => ∫ u, (brownianVectorContinuousLeftSum D H G k l u-I u)^2 ∂P.prod (Measure.pi (fun _ : ι => Q)))
        atTop (𝓝 0) ∧
      Integrable (brownianVectorContinuousExponential D H (G.time 0 k) I) (P.prod (Measure.pi (fun _ : ι => Q))) ∧
      (∫ u, brownianVectorContinuousExponential D H (G.time 0 k) I u ∂P.prod (Measure.pi (fun _ : ι => Q))) = 1 ∧
      IsProbabilityMeasure ((P.prod (Measure.pi (fun _ : ι => Q))).withDensity (fun u => ENNReal.ofReal
        (brownianVectorContinuousExponential D H (G.time 0 k) I u))) ∧
      (((P.prod (Measure.pi (fun _ : ι => Q))).withDensity (fun u => ENNReal.ofReal
        (brownianVectorContinuousExponential D H (G.time 0 k) I u))).map Prod.fst = P) ∧
      Tendsto (fun l => eLpNorm (brownianVectorFullPastExponential D (G.time l)
        (brownianVectorContinuousMeshCoefficient H (G.time l)) 1 (k*2^l)-
          brownianVectorContinuousExponential D H (G.time 0 k) I) 1 (P.prod (Measure.pi (fun _ : ι => Q)))) atTop (𝓝 0) := by
  obtain ⟨I,hI,hIi,hIlim⟩ := brownianVectorContinuousLeftSum_exists_L2_limit P Q D hD hmD H hH C hC hc
    G k δ hδ hleft
  obtain ⟨hVm,hVi,hVlim⟩ := brownianVectorContinuousVariation_tendsto_L2 P Q D hD hmD H hH C hC hc
    G k δ hδ hwidth
  have hIm := tendstoInMeasure_of_tendsto_integral_sq hIi hIlim
  have hVmprob := tendstoInMeasure_of_tendsto_integral_sq hVi hVlim
  have hsm (l : ℕ) : AEStronglyMeasurable (brownianVectorContinuousLeftSum D H G k l)
      (P.prod (Measure.pi (fun _ : ι => Q))) :=
    (memLp_brownianVectorContinuousLeftSum P Q D hD hmD H hH C hC G k l).aestronglyMeasurable
  have hbrm (l : ℕ) : AEStronglyMeasurable (brownianVectorPredictableVariation D (G.time l)
      (brownianVectorContinuousMeshCoefficient H (G.time l)) (k*2^l)) (P.prod (Measure.pi (fun _ : ι => Q))) :=
    (aemeasurable_predictableGaussianVectorVariation (P.prod (Measure.pi (fun _ : ι => Q))) _ _
      ((fun i => (measurable_brownianVectorStaticCoefficient D hmD _ _ (fun i => hH _) i).aemeasurable)) _).aestronglyMeasurable
  have hExp := tendstoInMeasure_continuous_two_real hsm hbrm hIm hVmprob
    (fun p : ℝ×ℝ => Real.exp (p.1-p.2/2)) (by fun_prop)
  have hlim : TendstoInMeasure (P.prod (Measure.pi (fun _ : ι => Q)))
      (fun l => brownianVectorFullPastExponential D (G.time l)
        (brownianVectorContinuousMeshCoefficient H (G.time l)) 1 (k*2^l)) atTop
      (brownianVectorContinuousExponential D H (G.time 0 k) I) := by
    convert hExp using 1
    · funext l u
      simp only [brownianVectorFullPastExponential,one_mul,one_pow,brownianVectorContinuousLeftSum]
    · rfl
  obtain ⟨hEint,hEpos,hEmean,hEprob,hEmarg,hEL1⟩ := brownianVectorFullPast_density_limit P Q D hD hmD
    G.time G.monotone (fun l => k*2^l) (fun l => brownianVectorContinuousMeshCoefficient H (G.time l))
    (fun l i => hH _) ((Fintype.card ι : ℝ)*C^2*(G.time 0 k : ℝ))
    (fun l u => brownianVectorContinuousVariation_le D H C hC G k l u) _ hlim
  exact ⟨I,hI,hIlim,hEint,hEmean,hEprob,hEmarg,hEL1⟩

end SKConstants
