module
public import SKConstants.PredictableGaussianSums
public import SKConstants.ScalarProcessInnovationFiltration
public import SKConstants.ScalarProcessWeightedMesh

public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
@[expose] def scalarActualObservationPast {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (u : Bool × Ω) : Iic T → ℝ := fun s => scalarHiddenContinuousField z B s u
@[expose] def scalarObservationPastRestrict {s T : ℝ≥0} (hs : s ≤ T)
    (w : Iic T → ℝ) : Iic s → ℝ := fun t => w ⟨t,t.property.trans hs⟩
lemma measurable_scalarObservationPastRestrict {s T : ℝ≥0} (hs : s ≤ T) :
    Measurable (scalarObservationPastRestrict hs) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)
@[expose] def scalarPathPoint {T : ℝ≥0} (s : ℝ≥0) (hs : s ≤ T) : Icc (0 : ℝ) (T : ℝ) :=
  ⟨s,s.coe_nonneg, NNReal.coe_le_coe.mpr hs⟩
@[expose] def scalarObservationPastInnovation {T : ℝ≥0} (z : ℝ) (s : ℝ≥0)
    (hs : s ≤ T) (w : Iic T → ℝ) : ℝ :=
  scalarInnovationPath T z (scalarPathFromPast T w) (scalarPathPoint s hs)
lemma measurable_scalarObservationPastInnovation {T : ℝ≥0} (z : ℝ) (s : ℝ≥0) (hs : s ≤ T) :
    Measurable (scalarObservationPastInnovation z s hs) :=
  (ContinuousMap.measurable_eval _).comp
    ((measurable_scalarInnovationPath T z).comp (measurable_scalarPathFromPast T))

lemma aemeasurable_scalarActualObservationPast {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    AEMeasurable (scalarActualObservationPast z B T) (scalarHiddenBrownianLaw z P) := by
  obtain ⟨Ypaths,Mpaths,hYm,hMm,hdef,he,hsig⟩ := scalarHiddenBrownian_actual_pathVersions P T z B hB
  let F := fun f : ScalarContinuousPath T => fun s : Iic T => f (scalarPathPoint s s.property)
  have hF : Measurable F := Measurable.of_eval (fun s => ContinuousMap.measurable_eval _)
  apply (hF.comp hYm).aemeasurable.congr
  filter_upwards [he] with u hu
  funext s
  exact (hu (scalarPathPoint s s.property)).1

lemma scalarObservationPastInnovation_actual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P, ∀ s : ℝ≥0, ∀ hs : s ≤ T,
      scalarObservationPastInnovation z s hs (scalarActualObservationPast z B T u) =
        scalarContinuousInnovation z B s u := by
  obtain ⟨Ypaths,Mpaths,hYm,hMm,hdef,he,hsig⟩ := scalarHiddenBrownian_actual_pathVersions P T z B hB
  filter_upwards [he] with u hu
  have hp : scalarPathFromPast T (scalarActualObservationPast z B T u) = Ypaths u := by
    have hd : (fun k => scalarHiddenContinuousField z B
        ⟨scalarPathDenseTimes T k, (scalarPathDenseTimes T k).property.1⟩ u) =
        scalarPathDenseSamples T (Ypaths u) := by
      funext k
      exact (hu (scalarPathDenseTimes T k)).1.symm
    change scalarPathFromDenseSamples T
      (fun k => scalarHiddenContinuousField z B
        ⟨scalarPathDenseTimes T k, (scalarPathDenseTimes T k).property.1⟩ u) = _
    rw [hd]
    exact scalarPathFromDenseSamples_leftInverse T (Ypaths u)
  intro s hs
  unfold scalarObservationPastInnovation
  rw [hp, ← hdef u]
  exact (hu (scalarPathPoint s hs)).2

abbrev ScalarObservationPredictableCoefficient (t : ℕ → ℝ≥0) :=
  (k : ℕ) → (Iic (t k) → ℝ) → ℝ
@[expose] def scalarObservationCoefficient {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ScalarObservationPredictableCoefficient t) (k : ℕ) (u : Bool × Ω) : ℝ :=
  H k (scalarActualObservationPast z B (t k) u)
lemma aemeasurable_scalarObservationCoefficient {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (H : ScalarObservationPredictableCoefficient t)
    (hH : ∀ k, Measurable (H k)) (k : ℕ) :
    AEMeasurable (scalarObservationCoefficient z B t H k) (scalarHiddenBrownianLaw z P) :=
  (hH k).comp_aemeasurable (aemeasurable_scalarActualObservationPast P (t k) z B hB)

@[expose] def scalarObservationPredictableSum {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ScalarObservationPredictableCoefficient t) :=
  predictableGaussianSum (brownianMeshIncrement (scalarContinuousInnovation z B) t)
    (scalarObservationCoefficient z B t H)
@[expose] def scalarObservationPredictableVariation {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ScalarObservationPredictableCoefficient t) :=
  predictableGaussianVariation (brownianMeshVariance t) (scalarObservationCoefficient z B t H)

@[expose] def scalarObservationPastSum (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (n : ℕ) (w : Iic (t n) → ℝ) : ℝ :=
  ∑ i : Fin n, H i (scalarObservationPastRestrict (ht (Nat.le_of_lt i.isLt)) w) *
    (scalarObservationPastInnovation z (t (i+1)) (ht (by omega)) w -
      scalarObservationPastInnovation z (t i) (ht (Nat.le_of_lt i.isLt)) w)
@[expose] def scalarObservationPastVariation (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (n : ℕ) (w : Iic (t n) → ℝ) : ℝ :=
  ∑ i : Fin n, H i (scalarObservationPastRestrict (ht (Nat.le_of_lt i.isLt)) w) ^ 2 *
    (brownianMeshVariance t i : ℝ)
lemma measurable_scalarObservationPastSum (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (scalarObservationPastSum z t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact ((hH i).comp (measurable_scalarObservationPastRestrict _)).mul
    ((measurable_scalarObservationPastInnovation z _ _).sub
      (measurable_scalarObservationPastInnovation z _ _))
lemma measurable_scalarObservationPastVariation (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (scalarObservationPastVariation t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact (((hH i).comp (measurable_scalarObservationPastRestrict _)).pow_const 2).mul_const _

lemma scalarObservationPastVariation_actual {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ScalarObservationPredictableCoefficient t)
    (n : ℕ) (u : Bool × Ω) :
    scalarObservationPastVariation t ht H n (scalarActualObservationPast z B (t n) u) =
      scalarObservationPredictableVariation z B t H n u := by
  rw [scalarObservationPredictableVariation, predictableGaussianVariation_eq_fin_sum]
  rfl
lemma scalarObservationPastSum_actual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (n : ℕ) :
    (fun u => scalarObservationPastSum z t ht H n (scalarActualObservationPast z B (t n) u)) =ᵐ[scalarHiddenBrownianLaw z P]
      scalarObservationPredictableSum z B t H n := by
  filter_upwards [scalarObservationPastInnovation_actual P (t n) z B hB] with u hu
  rw [scalarObservationPredictableSum, predictableGaussianSum_eq_fin_sum]
  unfold scalarObservationPastSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [hu]
  rfl
lemma scalarObservationPredictable_state_indep_increment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    IndepFun
      (fun u => (scalarObservationPredictableSum z B t H n u,
        scalarObservationCoefficient z B t H n u, scalarObservationPredictableVariation z B t H n u))
      (brownianMeshIncrement (scalarContinuousInnovation z B) t n)
      (scalarHiddenBrownianLaw z P) := by
  let Φ := fun w : Iic (t n) → ℝ =>
    (scalarObservationPastSum z t ht H n w, H n w, scalarObservationPastVariation t ht H n w)
  have hΦ : Measurable Φ := (measurable_scalarObservationPastSum z t ht H hH n).prodMk
    ((hH n).prodMk (measurable_scalarObservationPastVariation t ht H hH n))
  have hi := scalarContinuousInnovation_indepFun_shift_observationPast P (t n) z B hB
  have hx : IndepFun (brownianMeshIncrement (scalarContinuousInnovation z B) t n)
      (Φ ∘ scalarActualObservationPast z B (t n)) (scalarHiddenBrownianLaw z P) := by
    have he : t n + brownianMeshVariance t n = t (n+1) :=
      add_tsub_cancel_of_le (ht (by omega))
    change IndepFun (fun u => scalarContinuousInnovation z B (t (n+1)) u -
      scalarContinuousInnovation z B (t n) u)
      (fun u => Φ (fun s => scalarHiddenContinuousField z B s u)) _
    simpa only [Function.comp_def, he] using
      hi.comp (φ := fun f : ℝ≥0 → ℝ => f (brownianMeshVariance t n)) (ψ := Φ)
        (measurable_pi_apply _) hΦ
  apply hx.symm.congr _ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [scalarObservationPastSum_actual P z B hB t ht H n] with u hu
  dsimp only [Φ, Function.comp_def]
  rw [scalarObservationPastVariation_actual]
  exact congrArg (fun a => (a, scalarObservationCoefficient z B t H n u,
      scalarObservationPredictableVariation z B t H n u)) hu

@[expose] def scalarObservationPredictableExponential {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ScalarObservationPredictableCoefficient t) (theta : ℝ) (n : ℕ) (u : Bool × Ω) : ℝ :=
  Real.exp (theta * scalarObservationPredictableSum z B t H n u -
    theta ^ 2 * scalarObservationPredictableVariation z B t H n u / 2)

lemma scalarObservationPredictableExponential_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k)) (theta : ℝ) (n : ℕ) :
    Integrable (scalarObservationPredictableExponential z B t H theta n) (scalarHiddenBrownianLaw z P) ∧
    (∫ u, scalarObservationPredictableExponential z B t H theta n u ∂scalarHiddenBrownianLaw z P) = 1 := by
  exact predictableGaussianExponential_integral (scalarHiddenBrownianLaw z P)
    (brownianMeshIncrement (scalarContinuousInnovation z B) t) (scalarObservationCoefficient z B t H)
    (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw (scalarContinuousInnovation_isBrownianReal P z B hB).toIsPreBrownianReal t ht)
    (aemeasurable_scalarObservationCoefficient P z B hB t H hH)
    (scalarObservationPredictable_state_indep_increment P z B hB t ht H hH) theta n

lemma scalarObservationPredictableSum_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun u => scalarObservationCoefficient z B t H k u ^ 2)
      (scalarHiddenBrownianLaw z P)) (n : ℕ) :
    Integrable (fun u => scalarObservationPredictableSum z B t H n u ^ 2) (scalarHiddenBrownianLaw z P) ∧
    Integrable (scalarObservationPredictableVariation z B t H n) (scalarHiddenBrownianLaw z P) ∧
    (∫ u, scalarObservationPredictableSum z B t H n u ^ 2 ∂scalarHiddenBrownianLaw z P) =
      ∫ u, scalarObservationPredictableVariation z B t H n u ∂scalarHiddenBrownianLaw z P := by
  exact predictableGaussianSum_L2_isometry (scalarHiddenBrownianLaw z P)
    (brownianMeshIncrement (scalarContinuousInnovation z B) t) (scalarObservationCoefficient z B t H)
    (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw (scalarContinuousInnovation_isBrownianReal P z B hB).toIsPreBrownianReal t ht)
    (aemeasurable_scalarObservationCoefficient P z B hB t H hH) hHsq
    (scalarObservationPredictable_state_indep_increment P z B hB t ht H hH) n

lemma scalarObservationPredictableSum_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (theta : ℝ) (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, scalarObservationPredictableVariation z B t H n u ≤ V) :
    Integrable (fun u => Real.exp (theta * scalarObservationPredictableSum z B t H n u)) (scalarHiddenBrownianLaw z P) ∧
    mgf (scalarObservationPredictableSum z B t H n) (scalarHiddenBrownianLaw z P) theta ≤ Real.exp (theta ^ 2 * V / 2) := by
  exact predictableGaussianSum_mgf_bound (scalarHiddenBrownianLaw z P)
    (brownianMeshIncrement (scalarContinuousInnovation z B) t) (scalarObservationCoefficient z B t H)
    (brownianMeshVariance t)
    (brownianMeshIncrement_hasLaw (scalarContinuousInnovation_isBrownianReal P z B hB).toIsPreBrownianReal t ht)
    (aemeasurable_scalarObservationCoefficient P z B hB t H hH)
    (scalarObservationPredictable_state_indep_increment P z B hB t ht H hH) theta n V hV
lemma scalarObservationPredictableSum_L2_isometry_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun u => scalarObservationCoefficient z B t H k u ^ 2)
      (scalarHiddenBrownianLaw z P)) (n : ℕ) :
    (∫ u, scalarObservationPredictableSum z B t H n u ^ 2 ∂scalarHiddenBrownianLaw z P) =
      ∑ k : Fin n, (brownianMeshVariance t k : ℝ) *
        ∫ u, scalarObservationCoefficient z B t H k u ^ 2 ∂scalarHiddenBrownianLaw z P := by
  rw [(scalarObservationPredictableSum_L2_isometry P z B hB t ht H hH hHsq n).2.2]
  exact integral_predictableGaussianVariation _ _ _ hHsq n

@[expose] def scalarCurrentObservationCoefficient (t : ℕ → ℝ≥0) (H : ℝ → ℝ) :
    ScalarObservationPredictableCoefficient t := fun k w => H (w ⟨t k, Set.mem_Iic.mpr le_rfl⟩)
lemma measurable_scalarCurrentObservationCoefficient (t : ℕ → ℝ≥0) (H : ℝ → ℝ)
    (hH : Measurable H) (k : ℕ) : Measurable (scalarCurrentObservationCoefficient t H k) :=
  hH.comp (measurable_pi_apply _)
lemma scalarObservationCoefficient_current {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ℝ → ℝ) (k : ℕ) (u : Bool × Ω) :
    scalarObservationCoefficient z B t (scalarCurrentObservationCoefficient t H) k u =
      H (scalarHiddenContinuousField z B (t k) u) := rfl
lemma integrable_scalarObservationCoefficient_sq_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (C : ℝ) (hC : ∀ k w, ‖H k w‖ ≤ C) (k : ℕ) :
    Integrable (fun u => scalarObservationCoefficient z B t H k u ^ 2) (scalarHiddenBrownianLaw z P) := by
  apply (integrable_const (C ^ 2 : ℝ)).mono'
    ((aemeasurable_scalarObservationCoefficient P z B hB t H hH k).pow_const 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC k _) 2

lemma scalarObservationPredictableSum_current_uniform {Ω : Type*} (H : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) :
    scalarObservationPredictableSum z B (scalarUniformTime n)
      (scalarCurrentObservationCoefficient (scalarUniformTime n) H) m u =
        scalarWeightedBrownianMeshSum H z B n m u := by
  rw [scalarObservationPredictableSum, predictableGaussianSum_eq_range_sum]
  rfl

lemma scalarWeightedBrownianMeshSum_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ → ℝ) (hH : Measurable H)
    (C : ℝ) (hC : ∀ y, ‖H y‖ ≤ C) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (n m : ℕ) :
    Integrable (fun u => scalarWeightedBrownianMeshSum H z B n m u ^ 2) (scalarHiddenBrownianLaw z P) ∧
    (∫ u, scalarWeightedBrownianMeshSum H z B n m u ^ 2 ∂scalarHiddenBrownianLaw z P) =
      ∑ k : Fin m, (1 / ((n : ℝ) + 1)) *
        ∫ u, H (scalarHiddenContinuousField z B (scalarUniformTime n k) u) ^ 2 ∂scalarHiddenBrownianLaw z P := by
  let A := scalarCurrentObservationCoefficient (scalarUniformTime n) H
  have hm : ∀ k, Measurable (A k) := measurable_scalarCurrentObservationCoefficient _ H hH
  have hsq := integrable_scalarObservationCoefficient_sq_of_bounded P z B hB
    (scalarUniformTime n) A hm C (fun k w => hC _) 
  have hi := scalarObservationPredictableSum_L2_isometry P z B hB (scalarUniformTime n)
    (scalarUniformTime_monotone n) A hm hsq m
  have he := scalarObservationPredictableSum_L2_isometry_sum P z B hB (scalarUniformTime n)
    (scalarUniformTime_monotone n) A hm hsq m
  simpa only [A, scalarObservationPredictableSum_current_uniform, scalarObservationCoefficient_current,
    brownianMeshVariance_scalarUniformTime, NNReal.coe_div, NNReal.coe_one, NNReal.coe_add,
    NNReal.coe_natCast] using And.intro hi.1 he
lemma scalarWeightedBrownianMeshSum_defect_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (n m : ℕ) :
    Integrable (fun u => scalarWeightedBrownianMeshSum scalarDefect z B n m u ^ 2)
      (scalarHiddenBrownianLaw z P) ∧
    (∫ u, scalarWeightedBrownianMeshSum scalarDefect z B n m u ^ 2 ∂scalarHiddenBrownianLaw z P) =
      ∑ k : Fin m, (1 / ((n : ℝ) + 1)) * ∫ u,
        scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u) ^ 2
          ∂scalarHiddenBrownianLaw z P := by
  apply scalarWeightedBrownianMeshSum_L2_isometry P scalarDefect measurable_scalarDefect 1 _ z B hB n m
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg (scalarDefect_pos y).le]
  exact scalarDefect_le_one y
end SKConstants
