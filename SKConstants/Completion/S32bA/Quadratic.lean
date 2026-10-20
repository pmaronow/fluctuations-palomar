module

public import SKConstants.Completion.LJ.PosteriorIntegral
public import SKConstants.GaussianCenteredSquareIsometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S32bA
open SKConstantsOAI.ZeroTemperatureSK LC1 LJ
variable {Ω : Type*} [MeasurableSpace Ω]

def originalFieldCenteredSquareSum (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) : ℕ → Ω → ℝ :=
  predictableGaussianCenteredSquareSum (brownianMeshIncrement W.B t)
    (originalFieldCoefficient W b t H) (brownianMeshVariance t)

def originalFieldPastCenteredSquareSum (b : BoundedLipschitzDrift) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (H : OriginalFieldCoefficient t) (n : ℕ)
    (p : ScalarContinuousPath (t n)) : ℝ :=
  ∑ i : Fin n, H i (scalarContinuousPathRestrict (t i) (t n) (ht (by omega)) p) *
    ((boundedDriftRecoverBrownianPast b (t n) p ⟨t (i + 1), ht (by omega)⟩ -
      boundedDriftRecoverBrownianPast b (t n) p ⟨t i, ht (by omega)⟩) ^ 2 -
      (brownianMeshVariance t i : ℝ))

theorem measurable_originalFieldPastCenteredSquareSum (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (originalFieldPastCenteredSquareSum b t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact ((hH i).comp (measurable_scalarContinuousPathRestrict _ _ _)).mul
    (((((measurable_pi_apply _).comp (measurable_boundedDriftRecoverBrownianPast b _)).sub
      ((measurable_pi_apply _).comp (measurable_boundedDriftRecoverBrownianPast b _))).pow_const 2).sub_const _)

theorem originalFieldPastCenteredSquareSum_actual (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (n : ℕ) :
    (fun w => originalFieldPastCenteredSquareSum b t ht H n
      (boundedDriftPastPath W b (t n) w)) =ᵐ[W.law]
      originalFieldCenteredSquareSum W b t H n := by
  have hrestrict : ∀ᵐ w ∂W.law, ∀ i : Fin n,
      scalarContinuousPathRestrict (t i) (t n) (ht (by omega))
        (boundedDriftPastPath W b (t n) w) = boundedDriftPastPath W b (t i) w :=
    ae_all_iff.mpr (fun i => boundedDriftPastPath_restrict W b _ _ (ht (by omega)))
  filter_upwards [hrestrict, boundedDriftRecoverBrownianPast_actual W b (t n)] with w hr hb
  rw [originalFieldCenteredSquareSum, predictableGaussianCenteredSquareSum,
    predictableGaussianSum_eq_fin_sum]
  unfold originalFieldPastCenteredSquareSum
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i, hb]
  rfl

theorem originalFieldCenteredSquare_state_indep_increment (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    IndepFun (fun w => (originalFieldCenteredSquareSum W b t H n w,
      originalFieldCoefficient W b t H n w)) (brownianMeshIncrement W.B t n) W.law := by
  let Φ := fun p : ScalarContinuousPath (t n) =>
    (originalFieldPastCenteredSquareSum b t ht H n p, H n p)
  have hΦ : Measurable Φ := (measurable_originalFieldPastCenteredSquareSum b t ht H hH n).prodMk
    (hH n)
  have he : t n + brownianMeshVariance t n = t (n + 1) := add_tsub_cancel_of_le (ht (by omega))
  have hEval : Measurable (fun f : ℝ≥0 → ℝ => f (brownianMeshVariance t n)) :=
    measurable_pi_apply _
  have hi := (brownian_future_indep_boundedDriftPastPath W b (t n)).comp
    (φ := fun f : ℝ≥0 → ℝ => f (brownianMeshVariance t n)) (ψ := Φ)
    hEval hΦ
  have hi' : IndepFun (brownianMeshIncrement W.B t n)
      (Φ ∘ boundedDriftPastPath W b (t n)) W.law := by
    change IndepFun (fun w => W.B (t (n + 1)) w - W.B (t n) w)
      (Φ ∘ boundedDriftPastPath W b (t n)) W.law
    simpa only [Function.comp_def, he] using hi
  apply hi'.symm.congr _ (ae_of_all _ (fun _ => rfl))
  filter_upwards [originalFieldPastCenteredSquareSum_actual W b t ht H n] with w hw
  dsimp only [Φ, Function.comp_def]
  rw [hw]
  rfl

theorem originalFieldCenteredSquareSum_isometry (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun w => originalFieldCoefficient W b t H k w ^ 2) W.law) (n : ℕ) :
    Integrable (fun w => originalFieldCenteredSquareSum W b t H n w ^ 2) W.law ∧
      (∫ w, originalFieldCenteredSquareSum W b t H n w ^ 2 ∂W.law) =
        ∑ k ∈ Finset.range n, 2 * (brownianMeshVariance t k : ℝ) ^ 2 *
          (∫ w, originalFieldCoefficient W b t H k w ^ 2 ∂W.law) := by
  let := W.isProbability
  exact predictableGaussianCenteredSquareSum_L2_isometry W.law (brownianMeshIncrement W.B t)
    (originalFieldCoefficient W b t H) (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw W.brownian.toIsPreBrownianReal t ht)
    (fun k => (measurable_originalFieldCoefficient W b t H hH k).aemeasurable) hHsq
    (originalFieldCenteredSquare_state_indep_increment W b t ht H hH) n

def curvatureCenteredSquareSum (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (n : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, actualCurvature W β (t k) w *
    ((W.B (t (k + 1)) w - W.B (t k) w) ^ 2 - (brownianMeshVariance t k : ℝ))

theorem curvatureCenteredSquareSum_originalField (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (n : ℕ) :
    originalFieldCenteredSquareSum W (actualParisiFullScalarDrift β) t (curvatureFieldCoefficient β t) n
      =ᵐ[W.law] curvatureCenteredSquareSum W β t n := by
  have hc : ∀ᵐ w ∂W.law, ∀ k : ℕ,
      originalFieldCoefficient W (actualParisiFullScalarDrift β) t (curvatureFieldCoefficient β t) k w =
        actualCurvature W β (t k) w := ae_all_iff.mpr (curvatureFieldCoefficient_actual W β t)
  filter_upwards [hc] with w hw
  rw [originalFieldCenteredSquareSum, predictableGaussianCenteredSquareSum,
    predictableGaussianSum_eq_range_sum]
  simp only [hw, brownianMeshIncrement, curvatureCenteredSquareSum]

theorem curvatureCenteredSquareSum_isometry (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    Integrable (fun w => curvatureCenteredSquareSum W β t n w ^ 2) W.law ∧
      (∫ w, curvatureCenteredSquareSum W β t n w ^ 2 ∂W.law) =
        ∑ k ∈ Finset.range n, 2 * (brownianMeshVariance t k : ℝ) ^ 2 *
          actualParisiFullSusceptibilitySquareExpected W β (t k) := by
  let := W.isProbability
  have hi (k : ℕ) : Integrable (fun w => originalFieldCoefficient W (actualParisiFullScalarDrift β)
      t (curvatureFieldCoefficient β t) k w ^ 2) W.law := by
    apply Integrable.of_bound
      ((measurable_originalFieldCoefficient W _ t _ (measurable_curvatureFieldCoefficient β t) k).pow_const 2).aestronglyMeasurable 1
    apply ae_of_all
    intro w
    rw [Real.norm_eq_abs, abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) (actualParisiFullCurvature_abs_le_one β _ _) 2).trans_eq
      (by norm_num)
  have h := originalFieldCenteredSquareSum_isometry W (actualParisiFullScalarDrift β) t ht
    (curvatureFieldCoefficient β t) (measurable_curvatureFieldCoefficient β t) hi n
  have he := curvatureCenteredSquareSum_originalField W β t n
  refine ⟨h.1.congr (he.mono (fun _ hw => congrArg (fun x : ℝ => x ^ 2) hw)), ?_⟩
  rw [← integral_congr_ae (he.mono (fun _ hw => congrArg (fun x : ℝ => x ^ 2) hw)), h.2]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  refine (integral_congr_ae ((curvatureFieldCoefficient_actual W β t k).mono
    (fun _ hw => congrArg (fun x : ℝ => x ^ 2) hw))).trans ?_
  simp only [actualParisiFullSusceptibilitySquareExpected, actualCurvature, Real.toNNReal_coe]

theorem curvatureCenteredSquareSum_pre_dyadic_secondMoment (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) (hT : T ≤ parisiEquilibriumPhysicalEndpoint β) (l : ℕ) :
    Integrable (fun w => curvatureCenteredSquareSum W β ((brownianDyadicGrid T).time l) (2 ^ l) w ^ 2)
      W.law ∧
    (∫ w, curvatureCenteredSquareSum W β ((brownianDyadicGrid T).time l) (2 ^ l) w ^ 2 ∂W.law) =
      (2 / β ^ 2) * (T : ℝ) * brownianDyadicWidth T l := by
  obtain ⟨hi, he⟩ := curvatureCenteredSquareSum_isometry W β
    ((brownianDyadicGrid T).time l) ((brownianDyadicGrid T).monotone l) (2 ^ l)
  refine ⟨hi, he.trans ?_⟩
  have hv (k : ℕ) : (brownianMeshVariance ((brownianDyadicGrid T).time l) k : ℝ) =
      brownianDyadicWidth T l := by
    rw [brownianMeshVariance, NNReal.coe_sub ((brownianDyadicGrid T).monotone l (Nat.le_succ k))]
    simp only [brownianDyadicGrid_time_coe, brownianDyadicWidth, Nat.cast_succ]
    ring
  calc
    _ = ∑ k ∈ Finset.range (2 ^ l),
        (2 / β ^ 2) * brownianDyadicWidth T l *
          (brownianMeshVariance ((brownianDyadicGrid T).time l) k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkT : (brownianDyadicGrid T).time l k ≤ parisiEquilibriumPhysicalEndpoint β :=
        ((brownianDyadicGrid T).le_duration (k := 1)
          (by simpa only [one_mul] using (Finset.mem_range.mp hk).le)).trans
          (by simpa only [one_mul, brownianDyadicGrid_horizon] using hT)
      rw [actualParisiFullSusceptibilitySquareExpected_pre W β hβ _ hkT, hv]
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      have hh := (brownianDyadicGrid T).variance_sum 1 l
      simp only [one_mul, brownianDyadicGrid_horizon] at hh
      rw [hh]
      ring

theorem curvatureCenteredSquareSum_pre_dyadic_tendsto_L2 (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (T : ℝ≥0) (hT : T ≤ parisiEquilibriumPhysicalEndpoint β) :
    Tendsto (fun l => ∫ w,
      curvatureCenteredSquareSum W β ((brownianDyadicGrid T).time l) (2 ^ l) w ^ 2 ∂W.law)
      atTop (𝓝 0) := by
  simp_rw [(curvatureCenteredSquareSum_pre_dyadic_secondMoment W β hβ T hT _).2]
  simpa using (brownianDyadicWidth_tendsto T).const_mul ((2 / β ^ 2) * (T : ℝ))

end SKConstants.Completion.S32bA
