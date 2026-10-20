module

public import SKConstants.Completion.J3B.TimeTransport
public import SKConstants.Completion.SJ3.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.J3B
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def VanishingMeanSquare {U : Type*} [MeasurableSpace U]
    (μ : Measure U) (E : ℕ → U → ℝ) : Prop :=
  (∀ l, Integrable (fun u => E l u ^ 2) μ) ∧
    Tendsto (fun l => ∫ u, E l u ^ 2 ∂μ) atTop (𝓝 0)

theorem vanishingMeanSquare_comp_hasLaw {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    {μ : Measure U} {ν : Measure T} {f : U → T} (hf : HasLaw f ν μ)
    {E : ℕ → T → ℝ} (hE : VanishingMeanSquare ν E) :
    VanishingMeanSquare μ (fun l u => E l (f u)) := by
  refine ⟨fun l => hf.integrable_fun_comp (hE.1 l), ?_⟩
  have he (l : ℕ) : (∫ u, E l (f u) ^ 2 ∂μ) = ∫ t, E l t ^ 2 ∂ν := by
    simpa only [Function.comp_def] using hf.integral_comp (hE.1 l).aestronglyMeasurable
  simp_rw [he]
  exact hE.2

theorem potentialTaylorExpansion_holds (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) :
    VanishingMeanSquare W.law (potentialTaylorError W β V) :=
  potentialTaylorError_tendsto_L2 W β hβ V hV

theorem rowBase_original_hasLaw (W : BrownianSystem Ω) (Z : BrownianSystem A) :
    HasLaw (fun u : (Bool × Ω) × A => u.1.2) W.law (LM4.actualRowBaseLaw W Z) := by
  let := W.isProbability
  let := Z.isProbability
  exact ((measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law))).hasLaw

theorem rowBasePotentialTaylorExpansion_holds (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : β ≠ 0) (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) :
    VanishingMeanSquare (LM4.actualRowBaseLaw W Z)
      (fun l u => potentialTaylorError W β V l u.1.2) :=
  vanishingMeanSquare_comp_hasLaw (rowBase_original_hasLaw W Z)
    (potentialTaylorExpansion_holds W β hβ V hV)

theorem rowLinkedPotentialTaylorExpansion_holds (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : β ≠ 0) (V H : ℝ≥0) (hV : (V : ℝ) < β ^ 2) :
    VanishingMeanSquare (actualParisiFullQuerySpinLaw W Z β H)
      (fun l u => potentialTaylorError W β V l u.1.2) :=
  vanishingMeanSquare_comp_hasLaw (actualParisiFullQuerySpinLaw_path_hasLaw W Z β H)
    (potentialTaylorExpansion_holds W β hβ V hV)

theorem supportPotentialTaylorExpansion_holds (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) :
    VanishingMeanSquare (LM4.actualRowBaseLaw W Z)
      (fun l u => potentialTaylorError W β (parisiEquilibriumPhysicalEndpoint β) l u.1.2) ∧
    VanishingMeanSquare (actualParisiFullQuerySpinLaw W Z β (parisiEquilibriumPhysicalEndpoint β))
      (fun l u => potentialTaylorError W β (parisiEquilibriumPhysicalEndpoint β) l u.1.2) := by
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have hS : (parisiEquilibriumPhysicalEndpoint β : ℝ) < β ^ 2 := by
    rw [parisiEquilibriumPhysicalEndpoint_coe β hβ]
    have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1.2
    nlinarith [mul_lt_mul_of_pos_left hQ (sq_pos_of_ne_zero hb)]
  exact ⟨rowBasePotentialTaylorExpansion_holds W Z β hb _ hS,
    rowLinkedPotentialTaylorExpansion_holds W Z β hb _ _ hS⟩

end SKConstants.Completion.J3B
