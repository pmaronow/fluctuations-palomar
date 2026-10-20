module

public import SKConstants.Completion.SJ7.MGFLimit
public import SKConstants.Completion.LJ3.DyadicOriginalLag

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ7
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem measurable_actualGrowingOriginalLag (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℕ → ℝ≥0) (weight : ℝ≥0 → ℝ) (N : ℕ → ℕ) (K : ℕ) :
    Measurable (LJ3.actualGrowingOriginalLag W β t weight N K) := by
  apply Finset.measurable_fun_sum
  intro j _
  exact LJ.measurable_originalLagSum W β (t j) _ (N j)

theorem actualGrowingOriginalLag_limit_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1)
    (K : ℕ) (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1)
    (I : Ω → ℝ) (hIm : Measurable I) (hI : MemLp I 2 W.law)
    (hi : ∀ l, Integrable (fun w =>
      (LJ3.actualGrowingOriginalLag W β (LJ3.growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K w - I w) ^ 2) W.law)
    (hlim : Tendsto (fun l => ∫ w,
      (LJ3.actualGrowingOriginalLag W β (LJ3.growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K w - I w) ^ 2
      ∂W.law) atTop (𝓝 0)) :
    (∫ w, I w ∂W.law) = 0 ∧
      Concentration.LocalQuadraticMGF I W.law
        (256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ))
        (1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) := by
  let := W.isProbability
  let X := fun l => LJ3.actualGrowingOriginalLag W β (LJ3.growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K
  have hXm (l : ℕ) : Measurable (X l) := measurable_actualGrowingOriginalLag W β _ weight _ K
  have hmean := integral_tendsto_of_L2 W.law X I hXm hIm hI hi hlim
  have hzero (l : ℕ) : (∫ w, X l w ∂W.law) = 0 :=
    LJ3.actualGrowingOriginalLag_mean_zero W β _ (LJ3.growingLagDyadicTime_monotone δ l)
      weight hweight _ K
  simp_rw [hzero] at hmean
  refine ⟨tendsto_nhds_unique hmean tendsto_const_nhds, ?_⟩
  exact localQuadraticMGF_of_L2
    (fun l => LJ3.actualGrowingOriginalLag_dyadic_mgf W β hβ δ hδ weight hweight K l hsmall)
    hXm hi hlim

theorem actualQuerySpinLaw_growingOriginalLag_limit_mgf
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (weight : ℝ≥0 → ℝ) (hweight : ∀ s, |weight s| ≤ 1)
    (K : ℕ) (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1)
    (I : Ω → ℝ) (hIm : Measurable I) (hI : MemLp I 2 W.law)
    (hi : ∀ l, Integrable (fun w =>
      (LJ3.actualGrowingOriginalLag W β (LJ3.growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K w - I w) ^ 2) W.law)
    (hlim : Tendsto (fun l => ∫ w,
      (LJ3.actualGrowingOriginalLag W β (LJ3.growingLagDyadicTime δ l) weight (fun _ => 2 ^ l) K w - I w) ^ 2
      ∂W.law) atTop (𝓝 0)) (V : ℝ≥0) :
    (∫ u : (Bool × Ω) × A, I u.1.2 ∂actualParisiFullQuerySpinLaw W Z β V) = 0 ∧
      Concentration.LocalQuadraticMGF (fun u : (Bool × Ω) × A => I u.1.2)
        (actualParisiFullQuerySpinLaw W Z β V)
        (256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ))
        (1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) := by
  have h := actualGrowingOriginalLag_limit_mgf W β hβ δ hδ weight hweight K hsmall I hIm hI hi hlim
  exact ⟨((actualParisiFullQuerySpinLaw_path_hasLaw W Z β V).integral_comp hIm.aestronglyMeasurable).trans h.1,
    h.2.comp_hasLaw (actualParisiFullQuerySpinLaw_path_hasLaw W Z β V)⟩

end SKConstants.Completion.SJ7
