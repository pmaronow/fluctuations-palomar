module
public import SKConstants.ScalarObservationPredictableSums

public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma gaussian_mgf_two_sided_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Ω → ℝ) (V : ℝ)
    (hmgf : ∀ θ : ℝ, Integrable (fun ω => Real.exp (θ * S ω)) P ∧
      mgf S P θ ≤ Real.exp (θ ^ 2 * V / 2)) (hV : 0 < V)
    (u : ℝ) (hu : 0 ≤ u) :
    P.real {ω | u ≤ |S ω|} ≤ 2 * Real.exp (-(u ^ 2 / (2 * V))) := by
  have hupper := measure_ge_le_exp_mul_mgf u (div_nonneg hu hV.le) (hmgf (u/V)).1
  have hlower := measure_le_le_exp_mul_mgf (-u)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hV.le) (hmgf (-u/V)).1
  have hup : P.real {ω | u ≤ S ω} ≤ Real.exp (-(u ^ 2 / (2 * V))) := by
    apply hupper.trans
    apply (mul_le_mul_of_nonneg_left (hmgf (u/V)).2 (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hdown : P.real {ω | S ω ≤ -u} ≤ Real.exp (-(u ^ 2 / (2 * V))) := by
    apply hlower.trans
    apply (mul_le_mul_of_nonneg_left (hmgf (-u/V)).2 (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hevent : {ω | u ≤ |S ω|} = {ω | u ≤ S ω} ∪ {ω | S ω ≤ -u} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, le_abs]
    constructor <;> intro h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith)

lemma scalarObservationPredictableSum_two_sided_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      scalarObservationPredictableVariation z B t H n u ≤ V)
    (hVp : 0 < V) (a : ℝ) (ha : 0 ≤ a) :
    (scalarHiddenBrownianLaw z P).real {u | a ≤ |scalarObservationPredictableSum z B t H n u|} ≤
      2 * Real.exp (-(a ^ 2 / (2 * V))) :=
  gaussian_mgf_two_sided_tail _ _ V
    (fun θ => scalarObservationPredictableSum_mgf_bound P z B hB t ht H hH θ n V hV) hVp a ha

@[expose] def predictableGaussianRunningAbsMax {Ω : Type*} (X H : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => max (predictableGaussianRunningAbsMax X H n ω) |predictableGaussianSum X H (n+1) ω|
@[expose] def predictableGaussianFirstExitCoefficient {Ω : Type*} (X H : ℕ → Ω → ℝ)
    (a : ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if predictableGaussianRunningAbsMax X H k ω < a then H k ω else 0

lemma predictableGaussianFirstExit_sum_properties {Ω : Type*} (X H : ℕ → Ω → ℝ)
    (a : ℝ) (ha : 0 < a) (n : ℕ) (ω : Ω) :
    (predictableGaussianRunningAbsMax X H n ω < a →
      predictableGaussianSum X (predictableGaussianFirstExitCoefficient X H a) n ω =
        predictableGaussianSum X H n ω) ∧
    (a ≤ predictableGaussianRunningAbsMax X H n ω →
      a ≤ |predictableGaussianSum X (predictableGaussianFirstExitCoefficient X H a) n ω|) := by
  induction n with
  | zero =>
    constructor
    · intro _; rfl
    · intro h; exact False.elim ((not_le_of_gt ha) h)
  | succ n ih =>
    by_cases hb : predictableGaussianRunningAbsMax X H n ω < a
    · have hs : predictableGaussianSum X (predictableGaussianFirstExitCoefficient X H a) (n+1) ω =
          predictableGaussianSum X H (n+1) ω := by
        simp only [predictableGaussianSum, predictableGaussianFirstExitCoefficient, hb, ↓reduceIte]
        rw [ih.1 hb]
      constructor
      · intro _; exact hs
      · intro h
        rw [hs]
        rcases le_max_iff.mp h with h | h
        · exact False.elim ((not_le_of_gt hb) h)
        · exact h
    · have hc : a ≤ predictableGaussianRunningAbsMax X H n ω := le_of_not_gt hb
      have hs : predictableGaussianSum X (predictableGaussianFirstExitCoefficient X H a) (n+1) ω =
          predictableGaussianSum X (predictableGaussianFirstExitCoefficient X H a) n ω := by
        simp only [predictableGaussianSum, predictableGaussianFirstExitCoefficient, hb,
          ↓reduceIte, zero_mul, add_zero]
      constructor
      · intro h
        have hm : predictableGaussianRunningAbsMax X H n ω ≤
            predictableGaussianRunningAbsMax X H (n+1) ω := le_max_left _ _
        exact False.elim ((not_le_of_gt h) (hc.trans hm))
      · intro _; rw [hs]; exact ih.2 hc

lemma predictableGaussianFirstExit_variation_le {Ω : Type*} (X H : ℕ → Ω → ℝ)
    (v : ℕ → ℝ≥0) (a : ℝ) (n : ℕ) (ω : Ω) :
    predictableGaussianVariation v (predictableGaussianFirstExitCoefficient X H a) n ω ≤
      predictableGaussianVariation v H n ω := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    apply add_le_add ih
    unfold predictableGaussianFirstExitCoefficient
    split_ifs
    · exact le_rfl
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact mul_nonneg (sq_nonneg _) (v n).coe_nonneg
lemma predictableGaussianSum_congr {Ω : Type*} (X H K : ℕ → Ω → ℝ)
    (ω : Ω) (h : ∀ k, H k ω = K k ω) (n : ℕ) :
    predictableGaussianSum X H n ω = predictableGaussianSum X K n ω := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [predictableGaussianSum, ih, h n]
lemma predictableGaussianVariation_congr {Ω : Type*} (v : ℕ → ℝ≥0) (H K : ℕ → Ω → ℝ)
    (ω : Ω) (h : ∀ k, H k ω = K k ω) (n : ℕ) :
    predictableGaussianVariation v H n ω = predictableGaussianVariation v K n ω := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [predictableGaussianVariation, ih, h n]

@[expose] def scalarObservationPredictableRunningAbsMax {Ω : Type*}
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (H : ScalarObservationPredictableCoefficient t) :=
  predictableGaussianRunningAbsMax (brownianMeshIncrement (scalarContinuousInnovation z B) t)
    (scalarObservationCoefficient z B t H)
@[expose] def scalarObservationPastRunningAbsMax (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) : (n : ℕ) → (Iic (t n) → ℝ) → ℝ
  | 0, _ => 0
  | n+1, w => max
      (scalarObservationPastRunningAbsMax z t ht H n (scalarObservationPastRestrict (ht (by omega)) w))
      |scalarObservationPastSum z t ht H (n+1) w|
lemma measurable_scalarObservationPastRunningAbsMax (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (scalarObservationPastRunningAbsMax z t ht H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp (measurable_scalarObservationPastRestrict _)).max
      ((continuous_abs.measurable).comp (measurable_scalarObservationPastSum z t ht H hH (n+1)))
lemma scalarObservationPastRunningAbsMax_actual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (n : ℕ) :
    (fun u => scalarObservationPastRunningAbsMax z t ht H n
      (scalarActualObservationPast z B (t n) u)) =ᵐ[scalarHiddenBrownianLaw z P]
        scalarObservationPredictableRunningAbsMax z B t H n := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    filter_upwards [ih, scalarObservationPastSum_actual P z B hB t ht H (n+1)] with u hu hs
    change max (scalarObservationPastRunningAbsMax z t ht H n
      (scalarActualObservationPast z B (t n) u)) _ = max _ _
    rw [hu, hs]
    rfl

@[expose] def scalarObservationFirstExitCoefficient (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (a : ℝ) : ScalarObservationPredictableCoefficient t :=
  fun k w => if scalarObservationPastRunningAbsMax z t ht H k w < a then H k w else 0
lemma measurable_scalarObservationFirstExitCoefficient (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k)) (a : ℝ) (k : ℕ) :
    Measurable (scalarObservationFirstExitCoefficient z t ht H a k) :=
  Measurable.ite
    (measurableSet_lt (measurable_scalarObservationPastRunningAbsMax z t ht H hH k) measurable_const)
    (hH k) measurable_const
lemma scalarObservationFirstExitCoefficient_actual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (a : ℝ) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P, ∀ k,
      scalarObservationCoefficient z B t (scalarObservationFirstExitCoefficient z t ht H a) k u =
        predictableGaussianFirstExitCoefficient
          (brownianMeshIncrement (scalarContinuousInnovation z B) t)
          (scalarObservationCoefficient z B t H) a k u := by
  have he : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, ∀ k,
      scalarObservationPastRunningAbsMax z t ht H k (scalarActualObservationPast z B (t k) u) =
        scalarObservationPredictableRunningAbsMax z B t H k u :=
    ae_all_iff.2 (scalarObservationPastRunningAbsMax_actual P z B hB t ht H)
  filter_upwards [he] with u hu
  intro k
  unfold scalarObservationCoefficient scalarObservationFirstExitCoefficient
  rw [hu k]
  rfl

lemma scalarObservationPredictableSum_maximal_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      scalarObservationPredictableVariation z B t H n u ≤ V)
    (hVp : 0 < V) (a : ℝ) (ha : 0 < a) :
    (scalarHiddenBrownianLaw z P).real {u | a ≤ scalarObservationPredictableRunningAbsMax z B t H n u} ≤
      2 * Real.exp (-(a ^ 2 / (2 * V))) := by
  let K := scalarObservationFirstExitCoefficient z t ht H a
  have hK := measurable_scalarObservationFirstExitCoefficient z t ht H hH a
  have he := scalarObservationFirstExitCoefficient_actual P z B hB t ht H a
  have hKV : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      scalarObservationPredictableVariation z B t K n u ≤ V := by
    filter_upwards [he, hV] with u hu hv
    change predictableGaussianVariation _ (scalarObservationCoefficient z B t K) n u ≤ V
    rw [predictableGaussianVariation_congr _ _ _ u hu n]
    exact (predictableGaussianFirstExit_variation_le _ _ _ a n u).trans hv
  have htail := scalarObservationPredictableSum_two_sided_tail P z B hB t ht K hK n V hKV hVp a ha.le
  apply le_trans ?_ htail
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [he] with u hu
  intro h
  change a ≤ |predictableGaussianSum _ (scalarObservationCoefficient z B t K) n u|
  rw [predictableGaussianSum_congr _ _ _ u hu n]
  exact (predictableGaussianFirstExit_sum_properties _ _ a ha n u).2 h
lemma predictableGaussianRunningAbsMax_ge_iff {Ω : Type*} (X H : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (a : ℝ) :
    a ≤ predictableGaussianRunningAbsMax X H n ω ↔
      ∃ k : ℕ, k ≤ n ∧ a ≤ |predictableGaussianSum X H k ω| := by
  induction n with
  | zero => simp [predictableGaussianRunningAbsMax, predictableGaussianSum]
  | succ n ih =>
    rw [predictableGaussianRunningAbsMax, le_max_iff, ih]
    constructor
    · rintro (⟨k,hk,ha⟩ | ha)
      · exact ⟨k, Nat.le_succ_of_le hk, ha⟩
      · exact ⟨n+1,le_rfl,ha⟩
    · rintro ⟨k,hk,ha⟩
      by_cases hkn : k ≤ n
      · exact Or.inl ⟨k,hkn,ha⟩
      · have he : k = n+1 := by omega
        exact Or.inr (he ▸ ha)

lemma aemeasurable_scalarObservationPredictableRunningAbsMax {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    AEMeasurable (scalarObservationPredictableRunningAbsMax z B t H n) (scalarHiddenBrownianLaw z P) :=
  ((measurable_scalarObservationPastRunningAbsMax z t ht H hH n).comp_aemeasurable
    (aemeasurable_scalarActualObservationPast P (t n) z B hB)).congr
      (scalarObservationPastRunningAbsMax_actual P z B hB t ht H n)

lemma scalarObservationPredictableSum_any_prefix_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : ScalarObservationPredictableCoefficient t) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      scalarObservationPredictableVariation z B t H n u ≤ V)
    (hVp : 0 < V) (a : ℝ) (ha : 0 < a) :
    (scalarHiddenBrownianLaw z P).real
      {u | ∃ k : ℕ, k ≤ n ∧ a ≤ |scalarObservationPredictableSum z B t H k u|} ≤
        2 * Real.exp (-(a ^ 2 / (2 * V))) := by
  have he : {u | ∃ k : ℕ, k ≤ n ∧ a ≤ |scalarObservationPredictableSum z B t H k u|} =
      {u | a ≤ scalarObservationPredictableRunningAbsMax z B t H n u} := by
    ext u
    exact (predictableGaussianRunningAbsMax_ge_iff _ _ n u a).symm
  rw [he]
  exact scalarObservationPredictableSum_maximal_tail P z B hB t ht H hH n V hV hVp a ha
end SKConstants
