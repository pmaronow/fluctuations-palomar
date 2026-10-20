module

public import SKConstants.Completion.LC1.All
public import SKConstants.PredictableGaussianSums
public import SKConstants.ScalarProcessRowMGFLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK LC1
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev OriginalFieldCoefficient (t : ℕ → ℝ≥0) :=
  (k : ℕ) → ScalarContinuousPath (t k) → ℝ

def originalFieldCoefficient (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) (k : ℕ) (w : Ω) : ℝ :=
  H k (boundedDriftPastPath W b (t k) w)

def originalFieldSum (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) : ℕ → Ω → ℝ :=
  predictableGaussianSum (brownianMeshIncrement W.B t) (originalFieldCoefficient W b t H)

def originalFieldVariation (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) : ℕ → Ω → ℝ :=
  predictableGaussianVariation (brownianMeshVariance t) (originalFieldCoefficient W b t H)

def originalFieldPastSum (b : BoundedLipschitzDrift) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (n : ℕ) (p : ScalarContinuousPath (t n)) : ℝ :=
  ∑ i : Fin n, H i (scalarContinuousPathRestrict (t i) (t n) (ht (by omega)) p) *
    (boundedDriftRecoverBrownianPast b (t n) p ⟨t (i + 1), ht (by omega)⟩ -
      boundedDriftRecoverBrownianPast b (t n) p ⟨t i, ht (by omega)⟩)

def originalFieldPastVariation (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (n : ℕ) (p : ScalarContinuousPath (t n)) : ℝ :=
  ∑ i : Fin n, (H i (scalarContinuousPathRestrict (t i) (t n) (ht (by omega)) p)) ^ 2 *
    (brownianMeshVariance t i : ℝ)

theorem measurable_originalFieldCoefficient (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (k : ℕ) :
    Measurable (originalFieldCoefficient W b t H k) :=
  (hH k).comp (measurable_boundedDriftPastPath W b (t k))

theorem measurable_originalFieldPastSum (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) : Measurable (originalFieldPastSum b t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact ((hH i).comp (measurable_scalarContinuousPathRestrict _ _ _)).mul
    (((measurable_pi_apply _).comp (measurable_boundedDriftRecoverBrownianPast b _)).sub
      ((measurable_pi_apply _).comp (measurable_boundedDriftRecoverBrownianPast b _)))

theorem measurable_originalFieldPastVariation (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : OriginalFieldCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (originalFieldPastVariation t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact (((hH i).comp (measurable_scalarContinuousPathRestrict _ _ _)).pow_const 2).mul_const _

theorem originalFieldPastSum_actual (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t) (n : ℕ) :
    (fun w => originalFieldPastSum b t ht H n (boundedDriftPastPath W b (t n) w)) =ᵐ[W.law]
      originalFieldSum W b t H n := by
  have hrestrict : ∀ᵐ w ∂W.law, ∀ i : Fin n,
      scalarContinuousPathRestrict (t i) (t n) (ht (by omega))
        (boundedDriftPastPath W b (t n) w) = boundedDriftPastPath W b (t i) w := by
    exact ae_all_iff.mpr (fun i => boundedDriftPastPath_restrict W b _ _ (ht (by omega)))
  filter_upwards [hrestrict, boundedDriftRecoverBrownianPast_actual W b (t n)] with w hr hb
  rw [originalFieldSum, predictableGaussianSum_eq_fin_sum]
  unfold originalFieldPastSum
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i, hb]
  rfl

theorem originalFieldPastVariation_actual (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t) (n : ℕ) :
    (fun w => originalFieldPastVariation t ht H n (boundedDriftPastPath W b (t n) w)) =ᵐ[W.law]
      originalFieldVariation W b t H n := by
  have hrestrict : ∀ᵐ w ∂W.law, ∀ i : Fin n,
      scalarContinuousPathRestrict (t i) (t n) (ht (by omega))
        (boundedDriftPastPath W b (t n) w) = boundedDriftPastPath W b (t i) w :=
    ae_all_iff.mpr (fun i => boundedDriftPastPath_restrict W b _ _ (ht (by omega)))
  filter_upwards [hrestrict] with w hr
  rw [originalFieldVariation, predictableGaussianVariation_eq_fin_sum]
  unfold originalFieldPastVariation
  apply Finset.sum_congr rfl
  intro i _
  rw [hr i]
  rfl

theorem originalField_state_indep_increment (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    IndepFun (fun w => (originalFieldSum W b t H n w, originalFieldCoefficient W b t H n w,
      originalFieldVariation W b t H n w)) (brownianMeshIncrement W.B t n) W.law := by
  let Φ := fun p : ScalarContinuousPath (t n) =>
    (originalFieldPastSum b t ht H n p, H n p, originalFieldPastVariation t ht H n p)
  have hΦ : Measurable Φ := (measurable_originalFieldPastSum b t ht H hH n).prodMk
    ((hH n).prodMk (measurable_originalFieldPastVariation t ht H hH n))
  have he : t n + brownianMeshVariance t n = t (n + 1) :=
    add_tsub_cancel_of_le (ht (by omega))
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
  filter_upwards [originalFieldPastSum_actual W b t ht H n,
    originalFieldPastVariation_actual W b t ht H n] with w hs hv
  dsimp only [Φ, Function.comp_def]
  rw [hs, hv]
  rfl

theorem originalFieldSum_isometry (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun w => originalFieldCoefficient W b t H k w ^ 2) W.law)
    (n : ℕ) :
    Integrable (fun w => originalFieldSum W b t H n w ^ 2) W.law ∧
      Integrable (originalFieldVariation W b t H n) W.law ∧
      (∫ w, originalFieldSum W b t H n w ^ 2 ∂W.law) =
        ∑ k : Fin n, (brownianMeshVariance t k : ℝ) *
          ∫ w, originalFieldCoefficient W b t H k w ^ 2 ∂W.law := by
  let := W.isProbability
  have hi := predictableGaussianSum_L2_isometry W.law (brownianMeshIncrement W.B t)
    (originalFieldCoefficient W b t H) (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw W.brownian.toIsPreBrownianReal t ht)
    (fun k => (measurable_originalFieldCoefficient W b t H hH k).aemeasurable) hHsq
    (originalField_state_indep_increment W b t ht H hH) n
  refine ⟨hi.1, hi.2.1, hi.2.2.trans ?_⟩
  exact integral_predictableGaussianVariation _ _ _ hHsq n

theorem originalFieldSum_mgf (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : OriginalFieldCoefficient t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) (v : ℝ)
    (hv : ∀ᵐ w ∂W.law, originalFieldVariation W b t H n w ≤ v) :
    Integrable (fun w => Real.exp (θ * originalFieldSum W b t H n w)) W.law ∧
      mgf (originalFieldSum W b t H n) W.law θ ≤ Real.exp (θ ^ 2 * v / 2) := by
  let := W.isProbability
  exact predictableGaussianSum_mgf_bound W.law (brownianMeshIncrement W.B t)
    (originalFieldCoefficient W b t H) (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw W.brownian.toIsPreBrownianReal t ht)
    (fun k => (measurable_originalFieldCoefficient W b t H hH k).aemeasurable)
    (originalField_state_indep_increment W b t ht H hH) θ n v hv

end SKConstants.Completion.LJ
