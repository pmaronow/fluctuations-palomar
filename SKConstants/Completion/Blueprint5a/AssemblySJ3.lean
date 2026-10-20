module

public import SKConstants.Completion.Blueprint5a.Statements

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Blueprint5a
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint SKConstants.Blueprint4 SKConstants.Completion

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem brownianDyadicGrid_time_le (T : ℝ≥0) (l k : ℕ) (hk : k ≤ 2 ^ l) :
    (brownianDyadicGrid T).time l k ≤ T := by
  rw [← NNReal.coe_le_coe, brownianDyadicGrid_time_coe, div_le_iff₀ (by positivity)]
  have : (k : ℝ) ≤ 2 ^ l := by exact_mod_cast hk
  nlinarith [T.coe_nonneg]

theorem queryRowLeftSum_support_ae (h2a : PreSupportQueryDriverStatement)
    {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (l : ℕ) :
    (fun u => SJ3.queryRowLeftSum W Z β hβ (parisiEquilibriumPhysicalEndpoint β) l u) =ᵐ[
      LM4.actualRowBaseLaw W Z] fun u => β⁻¹ * supportFieldLeftSum W β l u := by
  set S := parisiEquilibriumPhysicalEndpoint β
  have hall : ∀ᵐ u ∂LM4.actualRowBaseLaw W Z, ∀ k : ℕ, k ≤ 2 ^ l →
      (actualParisiQueryBrownianSystem W Z β hβ).B ((brownianDyadicGrid S).time l k)
        (u.1.2, u.2) = W.B ((brownianDyadicGrid S).time l k) u.1.2 := by
    refine ae_all_iff.2 (fun k => ?_)
    by_cases hk : k ≤ 2 ^ l
    · filter_upwards [h2a W Z β hβ _ (brownianDyadicGrid_time_le S l k hk)] with u hu _
      exact hu
    · exact ae_of_all _ (fun u h => absurd h hk)
  have hb : 0 < β := zero_lt_one.trans hβ
  have hsq : Real.sqrt (1 / β ^ 2) = β⁻¹ := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_sq hb.le]
  filter_upwards [hall] with u hu
  simp only [SJ3.queryRowLeftSum, supportFieldLeftSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.1 hk
  rw [hu k hk'.le, hu (k + 1) hk',
    actualParisiFullSusceptibilitySquareExpected_pre W β hβ _
      (brownianDyadicGrid_time_le S l k hk'.le), hsq]
  ring

theorem supportQuery_eq_ae (h2a : PreSupportQueryDriverStatement) (h2b : SupportFieldItoStatement)
    (h2m : SupportFieldTargetMeasurableStatement)
    {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] (W : BrownianSystem Ω)
    (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) {Qs : (Bool × Ω) × A → ℝ}
    (hQs : SJ3.IsQueryRowIntegral W Z β hβ (parisiEquilibriumPhysicalEndpoint β) Qs) :
    Qs =ᵐ[LM4.actualRowBaseLaw W Z] fun u => β⁻¹ * supportFieldTarget W β hβ u := by
  set μ := LM4.actualRowBaseLaw W Z
  set S := parisiEquilibriumPhysicalEndpoint β
  obtain ⟨hFi, hFlim⟩ := h2b W Z β hβ
  have hFm := h2m W Z β hβ
  set q := fun l u => SJ3.queryRowLeftSum W Z β hβ S l u
  set F := supportFieldTarget (A := A) W β hβ
  have hb : 0 < β := zero_lt_one.trans hβ
  have herr (l : ℕ) : (fun u => (q l u - β⁻¹ * F u) ^ 2) =ᵐ[μ]
      fun u => β⁻¹ ^ 2 * (supportFieldLeftSum W β l u - F u) ^ 2 := by
    filter_upwards [queryRowLeftSum_support_ae h2a W Z β hβ l] with u hu
    simp only [q] at hu ⊢
    rw [hu]
    ring
  have hi (l : ℕ) : Integrable (fun u => (q l u - β⁻¹ * F u) ^ 2) μ :=
    (((hFi l).const_mul (β⁻¹ ^ 2))).congr (herr l).symm
  have hlim : Tendsto (fun l => ∫ u, (q l u - β⁻¹ * F u) ^ 2 ∂μ) atTop (𝓝 0) := by
    have := hFlim.const_mul (β⁻¹ ^ 2)
    rw [mul_zero] at this
    refine this.congr (fun l => ?_)
    rw [integral_congr_ae (herr l), integral_const_mul]
  have hqm (l : ℕ) : Measurable (q l) := SJ3.measurable_queryRowLeftSum W Z β hβ S l
  have hq0 : MemLp (q 0) 2 μ := by
    have he : MemLp (fun u => q 0 u - Qs u) 2 μ :=
      (memLp_two_iff_integrable_sq ((hqm 0).aestronglyMeasurable.sub
        hQs.2.1.aestronglyMeasurable)).2 (hQs.2.2.1 0)
    convert he.add hQs.2.1 using 1
    funext u
    simp only [Pi.add_apply]
    ring
  have hFmem : MemLp (fun u => β⁻¹ * F u) 2 μ := by
    have he : MemLp (fun u => q 0 u - β⁻¹ * F u) 2 μ :=
      (memLp_two_iff_integrable_sq ((hqm 0).aestronglyMeasurable.sub
        (hFm.const_mul _).aestronglyMeasurable)).2 (hi 0)
    convert hq0.sub he using 1
    funext u
    simp only [Pi.sub_apply]
    ring
  exact SJ3.meanSquare_limit_unique hqm hQs.2.1 hFmem hQs.2.2.1 hQs.2.2.2 hlim

theorem jointEndpointIdentity_of_subnodes (h1 : QueryRowIntegralExistsStatement)
    (h2a : PreSupportQueryDriverStatement) (h2b : SupportFieldItoStatement)
    (h2m : SupportFieldTargetMeasurableStatement)
    (h3a : PostSupportInformationItoStatement) (h3b : PostSupportPotentialStatement)
    (h3p : PostSupportProfileStatement) :
    JointEndpointIdentityStatement := by
  intro Ω A _ _ W Z β hβ V hV
  set S := parisiEquilibriumPhysicalEndpoint β with hSdef
  refine ⟨?_, ?_⟩
  · obtain ⟨Q, hQ⟩ := h1 W Z β hβ V
    exact ⟨_, SJ3.jointRowIntegral_of_query W Z β hβ V hQ⟩
  intro J Zv hJ hZv
  obtain ⟨Qs, hQs⟩ := h1 W Z β hβ S
  have hQ := SJ3.queryRowIntegral_of_joint W Z β hβ V hZv
  have E1 := supportQuery_eq_ae h2a h2b h2m W Z β hβ hQs
  have E2 := h3a W Z β hβ V hV J _ Qs hJ hQ hQs
  obtain ⟨E3, hr_int, hAr⟩ := h3p W β hβ V hV
  have E4 := h3b W β hβ V hV
  have hVr : (S : ℝ) ≤ V := hV
  have E6 := LJ.energy_pressure_normalization W β hβ V hVr
  have E6' := LJ.energy_pressure_normalization_support W β hβ
  have hb : 0 < β := zero_lt_one.trans hβ
  refine (SJ3.rowLinked_absolutelyContinuous W Z β V).ae_le ?_
  filter_upwards [E1, E2] with u e1 e2
  have hAr_int := hAr u.1
  have e4 := E4 u.1
  have e5 := LJ.supportPotential_pressure_matching W β hβ u.1
  have e7S := LJ.actualRowPotential_eq_error W β S u.1
  have e7V := LJ.actualRowPotential_eq_error W β V u.1
  have e3 : (∫ t in (S : ℝ)..(V : ℝ), actualParisiFullSusceptibilitySquareExpected W β t *
        actualParisiPinningError W β t.toNNReal u.1) =
      (∫ t in (S : ℝ)..(V : ℝ), actualParisiFullSusceptibilitySquareExpected W β t) -
        2 * ∫ t in (S : ℝ)..(V : ℝ), LJ.actualRowPotential W β t.toNNReal u.1 *
          actualParisiFullSusceptibilitySquareExpected W β t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hr_int
      (hAr_int.const_mul 2)]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [LJ.actualRowPotential_eq_error W β t.toNNReal u.1]
    ring
  simp only [supportFieldTarget] at e1
  have e1' : β * Qs u = LJ.supportPotentialPrimitive W β u.1 -
      β ^ 2 * SJ3.potentialIntegral W β hβ S u.1 := by
    rw [e1, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul]
  rw [e3, ← E3] at e2
  have e4' := congrArg (fun z => β ^ 2 * z) e4
  have e7S' := congrArg (fun z => β ^ 2 * actualParisiFullSusceptibilityExpected W β S * z) e7S
  have e7V' := congrArg (fun z => β ^ 2 * actualParisiFullSusceptibilityExpected W β V * z) e7V
  rw [hSdef] at *
  linarith [e2, e1', e4', e5, e7S', e7V', E6, E6']

end SKConstants.Blueprint5a
