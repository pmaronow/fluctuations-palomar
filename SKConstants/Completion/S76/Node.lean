module

public import SKConstants.Completion.S76.GrowingLag

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.S76
open SKConstantsOAI.ZeroTemperatureSK LJ LJ3
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem lagGroup_eq_growingQueryLag (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) :
    Blueprint5a.lagGroup W Z β hβ δ K l =
      (fun u : (Bool × Ω) × A => growingQueryLag W Z β hβ δ K l (u.1.2, u.2)) := by
  funext u
  unfold Blueprint5a.lagGroup LJ.refinedResidualLag growingQueryLag queryLagSum
  simp only [Blueprint5a.refinedGrid, Blueprint5a.mesh, growingLagDyadicTime_zero]
  rfl

theorem lagGroup_measurable_integrable_mean_zero (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) :
    Measurable (Blueprint5a.lagGroup W Z β hβ δ K l) ∧
      Integrable (Blueprint5a.lagGroup W Z β hβ δ K l) (Blueprint5a.meshLaw W Z β δ K) ∧
      (∫ u, Blueprint5a.lagGroup W Z β hβ δ K l u ∂Blueprint5a.meshLaw W Z β δ K) = 0 := by
  rw [lagGroup_eq_growingQueryLag]
  have h := growingQueryLag_integrable_mean_zero W Z β hβ δ K l
  have hlaw := actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β (growingQueryTime δ (K + 1))
  exact ⟨(measurable_growingQueryLag W Z β hβ δ K l).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd),
    hlaw.integrable_fun_comp h.1, (hlaw.integral_comp h.1.aestronglyMeasurable).trans h.2⟩

theorem lagGroup_mgf (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K l : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) :
    Concentration.LocalQuadraticMGF (Blueprint5a.lagGroup W Z β hβ δ K l)
      (Blueprint5a.meshLaw W Z β δ K)
      (256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ))
      (1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ))) := by
  rw [lagGroup_eq_growingQueryLag]
  exact (growingQueryLag_mgf W Z β hβ δ hδ K l hsmall).comp_hasLaw
    (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β (growingQueryTime δ (K + 1)))

theorem lagGroupMGF_holds : Blueprint5a.LagGroupMGFStatement := by
  intro Ω A _ _ W Z β hβ
  refine ⟨256 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2),
    1 / (4 * Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2))),
    by positivity, by positivity, ?_⟩
  intro δ K hmesh l
  obtain ⟨hm, hi, hz⟩ := lagGroup_measurable_integrable_mean_zero W Z β hβ δ K l
  refine ⟨hm, hi, ?_⟩
  simpa only [hz, sub_zero, div_div] using
    lagGroup_mgf W Z β hβ δ hmesh.1 K l (fun j hj => hmesh.2.2.1 j (by omega))

end SKConstants.Completion.S76
