module

public import SKConstants.AdaptedGaussianMaximal
public import Mathlib.Probability.BrownianMotion.Basic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def gaussianHistoryOfVector : (n : ℕ) → (Fin n → ℝ) → GaussianHistory n
  | 0, _ => PUnit.unit
  | n + 1, x => (gaussianHistoryOfVector n (fun i => x i.castSucc), x (Fin.last n))

theorem measurable_gaussianHistoryOfVector (n : ℕ) :
    Measurable (gaussianHistoryOfVector n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (Measurable.of_eval fun i => measurable_pi_apply i.castSucc)).prodMk
      (measurable_pi_apply (Fin.last n))

def gaussianHistoryOfSequence (xi : ℕ → ℝ) : (n : ℕ) → GaussianHistory n :=
  Nat.rec (motive := fun n => GaussianHistory n) PUnit.unit (fun n history => (history, xi n))

theorem gaussianHistoryOfSequence_eq_vector (xi : ℕ → ℝ) (n : ℕ) :
    gaussianHistoryOfSequence xi n = gaussianHistoryOfVector n (fun i => xi i.val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (gaussianHistoryOfSequence xi n, xi n) =
      (gaussianHistoryOfVector n (fun i => xi i.val), xi n)
    rw [ih]

theorem independent_sequence_history_indep_next {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (xi : ℕ → Ω → ℝ) (hxi : ∀ k, AEMeasurable (xi k) P)
    (hindep : iIndepFun xi P) (n : ℕ) :
    IndepFun (fun ω => gaussianHistoryOfSequence (fun k => xi k ω) n) (xi n) P := by
  have hd : Disjoint (Finset.range n) {n} := by simp
  have hi := hindep.indepFun_finset₀ (Finset.range n) {n} hd hxi
  let f : ((Finset.range n) → ℝ) → GaussianHistory n :=
    fun v => gaussianHistoryOfVector n
      (fun i => v ⟨i.val, Finset.mem_range.mpr i.isLt⟩)
  have hf : Measurable f := (measurable_gaussianHistoryOfVector n).comp
    (Measurable.of_eval fun i : Fin n =>
      measurable_pi_apply (⟨i.val, Finset.mem_range.mpr i.isLt⟩ : Finset.range n))
  have hg : Measurable (fun v : ({n} : Finset ℕ) → ℝ => v ⟨n, by simp⟩) :=
    measurable_pi_apply _
  convert hi.comp hf hg using 1
  · funext ω
    exact gaussianHistoryOfSequence_eq_vector _ n
  · rfl

theorem independent_gaussian_sequence_history_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (xi : ℕ → Ω → ℝ) (dt : ℕ → ℝ≥0)
    (hlaw : ∀ k, HasLaw (xi k) (gaussianReal 0 (dt k)) P)
    (hindep : iIndepFun xi P) (n : ℕ) :
    HasLaw (fun ω => gaussianHistoryOfSequence (fun k => xi k ω) n)
      (gaussianHistoryLaw dt n) P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  induction n with
  | zero => exact hasLaw_dirac_of_ae_eq Filter.EventuallyEq.rfl
  | succ n ih =>
    exact (independent_sequence_history_indep_next xi (fun k => (hlaw k).aemeasurable)
      hindep n).hasLaw_prod ih (hlaw n)

def brownianMeshVariance (t : ℕ → ℝ≥0) (k : ℕ) : ℝ≥0 := t (k + 1) - t k

def brownianMeshIncrement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (k : ℕ) (ω : Ω) : ℝ := B (t (k + 1)) ω - B (t k) ω

theorem brownianMeshIncrement_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (k : ℕ) :
    HasLaw (brownianMeshIncrement B t k) (gaussianReal 0 (brownianMeshVariance t k)) P := by
  have he : nndist (t (k + 1) : ℝ) (t k : ℝ) = brownianMeshVariance t k := by
    apply NNReal.eq
    rw [coe_nndist, Real.dist_eq, abs_of_nonneg]
    · exact (NNReal.coe_sub (ht (by omega))).symm
    · exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (by omega)))
  unfold brownianMeshIncrement
  rw [← he]
  convert hB.hasLaw_sub (t (k + 1)) (t k) using 1
  rfl

theorem brownianMeshIncrement_iIndepFun {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) : iIndepFun (brownianMeshIncrement B t) P :=
  hB.hasIndepIncrements.nat ht

def brownianGaussianHistory {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (n : ℕ) (ω : Ω) : GaussianHistory n :=
  gaussianHistoryOfSequence (fun k => brownianMeshIncrement B t k ω) n

theorem brownianGaussianHistory_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    HasLaw (brownianGaussianHistory B t n) (gaussianHistoryLaw (brownianMeshVariance t) n) P :=
  independent_gaussian_sequence_history_hasLaw (brownianMeshIncrement B t)
    (brownianMeshVariance t) (brownianMeshIncrement_hasLaw hB t ht)
    (brownianMeshIncrement_iIndepFun hB t ht) n

def brownianAdaptedSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (n : ℕ) (ω : Ω) : ℝ :=
  adaptedGaussianSum H n (brownianGaussianHistory B t n ω)

def brownianAdaptedQuadraticVariation {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : GaussianPredictableCoefficient) (n : ℕ) (ω : Ω) : ℝ :=
  adaptedGaussianQuadraticVariation (brownianMeshVariance t) H n
    (brownianGaussianHistory B t n ω)

def brownianAdaptedRunningAbsMax {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : GaussianPredictableCoefficient) (n : ℕ) (ω : Ω) : ℝ :=
  adaptedGaussianRunningAbsMax H n (brownianGaussianHistory B t n ω)

theorem brownianAdaptedQuadraticVariation_bound_iff {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) (V : ℝ) :
    (∀ᵐ ω ∂P, brownianAdaptedQuadraticVariation B t H n ω ≤ V) ↔
      ∀ᵐ z ∂gaussianHistoryLaw (brownianMeshVariance t) n,
        adaptedGaussianQuadraticVariation (brownianMeshVariance t) H n z ≤ V := by
  exact (brownianGaussianHistory_hasLaw hB t ht n).ae_iff
    (measurableSet_setOfPred.1 (measurableSet_le
      (measurable_adaptedGaussianQuadraticVariation (brownianMeshVariance t) H hH n)
      measurable_const))

theorem integrable_exp_brownianAdaptedSum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ ω ∂P, brownianAdaptedQuadraticVariation B t H n ω ≤ V) (theta : ℝ) :
    Integrable (fun ω => Real.exp (theta * brownianAdaptedSum B t H n ω)) P :=
  (brownianGaussianHistory_hasLaw hB t ht n).integrable_comp
    (integrable_exp_adaptedGaussianSum (brownianMeshVariance t) H hH n V
      ((brownianAdaptedQuadraticVariation_bound_iff hB t ht H hH n V).mp hV) theta)

theorem mgf_brownianAdaptedSum_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ ω ∂P, brownianAdaptedQuadraticVariation B t H n ω ≤ V) (theta : ℝ) :
    mgf (brownianAdaptedSum B t H n) P theta ≤ Real.exp (theta ^ 2 * V / 2) := by
  have he := (brownianGaussianHistory_hasLaw hB t ht n).integral_comp
    (((measurable_adaptedGaussianSum H hH n).const_mul theta).exp.aestronglyMeasurable)
  change mgf (brownianAdaptedSum B t H n) P theta =
    mgf (adaptedGaussianSum H n) (gaussianHistoryLaw (brownianMeshVariance t) n) theta at he
  rw [he]
  exact mgf_adaptedGaussianSum_le (brownianMeshVariance t) H hH n V
    ((brownianAdaptedQuadraticVariation_bound_iff hB t ht H hH n V).mp hV) theta

theorem brownianAdaptedSum_maximal_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ ω ∂P, brownianAdaptedQuadraticVariation B t H n ω ≤ V)
    (hVp : 0 < V) (u : ℝ) (hu : 0 < u) :
    P.real {ω | u ≤ brownianAdaptedRunningAbsMax B t H n ω} ≤
      2 * Real.exp (-(u ^ 2 / (2 * V))) := by
  unfold brownianAdaptedRunningAbsMax
  rw [(brownianGaussianHistory_hasLaw hB t ht n).measureReal_eq
    (measurableSet_le measurable_const (measurable_adaptedGaussianRunningAbsMax H hH n))]
  exact adaptedGaussianSum_maximal_tail (brownianMeshVariance t) H hH n V
    ((brownianAdaptedQuadraticVariation_bound_iff hB t ht H hH n V).mp hV) hVp u hu

end SKConstants
