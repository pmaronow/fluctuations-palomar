module
public import SKConstants.ScalarProcessSampledHistory
public import SKConstants.ScalarProcessUniformMesh
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma scalarHiddenWeight_le_one (b : Bool) (z : ℝ) : scalarHiddenWeight b z ≤ 1 := by
  have hs := scalarWeight_sum z
  cases b
  · have hp := (scalarPlusWeight_pos z).le
    change scalarMinusWeight z ≤ 1
    linarith
  · have hm := (scalarMinusWeight_pos z).le
    change scalarPlusWeight z ≤ 1
    linarith

lemma norm_scalarHiddenWeight_le_one (b : Bool) (z : ℝ) : ‖scalarHiddenWeight b z‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (scalarHiddenWeight_pos b z).le]
  exact scalarHiddenWeight_le_one b z

lemma integrable_scalarHiddenWeight_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (b : Bool) (g f : α → ℝ) (hg : Measurable g) (hf : Integrable f μ) :
    Integrable (fun x => scalarHiddenWeight b (g x) * f x) μ :=
  hf.bdd_mul ((measurable_scalarHiddenWeight b).comp hg).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_scalarHiddenWeight_le_one b (g x)))

lemma integrable_tanh_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g f : α → ℝ) (hg : Measurable g) (hf : Integrable f μ) :
    Integrable (fun x => Real.tanh (g x) * f x) μ :=
  hf.bdd_mul (measurable_scalarTanh.comp hg).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_tanh_le_one (g x)))

lemma integral_scalarInnovation_gaussian (z : ℝ) (t : ℝ≥0) (b : Bool) :
    (∫ y, scalarInnovation z t y ∂gaussianReal (z + scalarHiddenSign b * (t : ℝ)) t) =
      (t : ℝ) * (scalarHiddenSign b - Real.tanh z) := by
  have hi : Integrable (fun y : ℝ => y)
      (gaussianReal (z + scalarHiddenSign b * (t : ℝ)) t) :=
    (memLp_id_gaussianReal 1).integrable (by simp)
  unfold scalarInnovation
  rw [integral_sub (f := fun y : ℝ => y - z) (g := fun _ : ℝ => (t : ℝ) * Real.tanh z)
      (hi.sub (integrable_const z)) (integrable_const _),
    integral_sub (f := fun y : ℝ => y) (g := fun _ : ℝ => z) hi (integrable_const z),
    integral_id_gaussianReal]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  ring

lemma integral_scalarHiddenWeight_mul_innovation (b : Bool) (z : ℝ) (t : ℝ≥0) :
    (∫ y, scalarHiddenWeight b y * scalarInnovation z t y ∂scalarTransitionKernel t z) =
      scalarHiddenWeight b z * (t : ℝ) * (scalarHiddenSign b - Real.tanh z) := by
  have hw := integral_withDensity_eq_integral_toReal_smul
    (μ := scalarTransitionKernel t z) (measurable_scalarHiddenWeight b).ennreal_ofReal
    (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)) (scalarInnovation z t)
  rw [scalarTransitionKernel_withDensity_hiddenWeight b z t, integral_smul_measure,
    ENNReal.toReal_ofReal (scalarHiddenWeight_pos b z).le,
    integral_scalarInnovation_gaussian] at hw
  have he : (fun y : ℝ => (ENNReal.ofReal (scalarHiddenWeight b y)).toReal • scalarInnovation z t y) =
      (fun y => scalarHiddenWeight b y * scalarInnovation z t y) := by
    funext y
    rw [ENNReal.toReal_ofReal (scalarHiddenWeight_pos b y).le]
    rfl
  rw [he] at hw
  exact hw.symm.trans (by ring)

lemma scalarHiddenSign_innovation_one_step (z : ℝ) (t : ℝ≥0) :
    (∑ b : Bool, scalarHiddenWeight b z *
      (∫ y, scalarHiddenSign b * scalarInnovation z t y
        ∂gaussianReal (z + scalarHiddenSign b * (t : ℝ)) t)) = (t : ℝ) * scalarDefect z := by
  simp_rw [integral_const_mul, integral_scalarInnovation_gaussian]
  simp only [Fintype.sum_bool,
    scalarHiddenSign, scalarHiddenWeight, Bool.false_eq_true, ↓reduceIte]
  have hs := scalarWeight_sum z
  have hd := scalarWeight_difference z
  unfold scalarDefect
  calc
    _ = (t : ℝ) * ((scalarPlusWeight z + scalarMinusWeight z) -
      Real.tanh z * (scalarPlusWeight z - scalarMinusWeight z)) := by ring
    _ = _ := by rw [hs, hd]; ring

lemma integral_tanh_mul_scalarInnovation (z : ℝ) (t : ℝ≥0) :
    (∫ y, Real.tanh y * scalarInnovation z t y ∂scalarTransitionKernel t z) =
      (t : ℝ) * scalarDefect z := by
  have hi := integrable_scalarInnovation_transition z t
  have hp := integrable_scalarHiddenWeight_mul true id (scalarInnovation z t) measurable_id hi
  have hm := integrable_scalarHiddenWeight_mul false id (scalarInnovation z t) measurable_id hi
  dsimp only [id_eq] at hp hm
  have he : (fun y => Real.tanh y * scalarInnovation z t y) =
      (fun y => scalarHiddenWeight true y * scalarInnovation z t y -
        scalarHiddenWeight false y * scalarInnovation z t y) := by
    funext y
    rw [scalarHiddenWeight, scalarHiddenWeight]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [← sub_mul, scalarWeight_difference]
  rw [he, integral_sub hp hm, integral_scalarHiddenWeight_mul_innovation,
    integral_scalarHiddenWeight_mul_innovation]
  simp only [scalarHiddenSign, scalarHiddenWeight, Bool.false_eq_true, ↓reduceIte]
  have hs := scalarWeight_sum z
  have hd := scalarWeight_difference z
  unfold scalarDefect
  calc
    _ = (t : ℝ) * ((scalarPlusWeight z + scalarMinusWeight z) -
      Real.tanh z * (scalarPlusWeight z - scalarMinusWeight z)) := by ring
    _ = _ := by rw [hs, hd]; ring

lemma integrable_scalarHiddenHistory_of_observation (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (f : ScalarObservationHistory n → ℝ)
    (hf : Integrable f (scalarObservationHistoryLaw z dt n)) :
    Integrable f (scalarHiddenObservationHistoryLaw b z dt n) := by
  rw [scalarObservationHistoryLaw_eq_hidden_mixture] at hf
  cases b
  · exact (integrable_smul_measure (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (scalarMinusWeight_pos z)))
      ENNReal.ofReal_ne_top).mp (hf.mono_measure (Measure.le_add_left le_rfl))
  · exact (integrable_smul_measure (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (scalarPlusWeight_pos z)))
      ENNReal.ofReal_ne_top).mp (hf.mono_measure (Measure.le_add_right le_rfl))

lemma integral_scalarHistory_hiddenWeight_mul (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (f : ScalarObservationHistory n → ℝ) :
    (∫ H, scalarHiddenWeight b (scalarLastField z n H) * f H
      ∂scalarObservationHistoryLaw z dt n) =
      scalarHiddenWeight b z * (∫ H, f H ∂scalarHiddenObservationHistoryLaw b z dt n) := by
  have hw := integral_withDensity_eq_integral_toReal_smul
    (μ := scalarObservationHistoryLaw z dt n)
    ((measurable_scalarHiddenWeight b).comp (measurable_scalarLastField z n)).ennreal_ofReal
    (Filter.Eventually.of_forall (fun H => ENNReal.ofReal_lt_top)) f
  simp only [Function.comp_def] at hw
  rw [scalarObservationHistoryLaw_withDensity_hiddenWeight b z dt n, integral_smul_measure,
    ENNReal.toReal_ofReal (scalarHiddenWeight_pos b z).le] at hw
  have he : (fun H : ScalarObservationHistory n =>
      (ENNReal.ofReal (scalarHiddenWeight b (scalarLastField z n H))).toReal • f H) =
      (fun H => scalarHiddenWeight b (scalarLastField z n H) * f H) := by
    funext H
    rw [ENNReal.toReal_ofReal (scalarHiddenWeight_pos b _).le]
    rfl
  rw [he] at hw
  exact hw.symm

lemma integral_scalarHiddenJoint_sign_mul (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ)
    (f : ScalarObservationHistory n → ℝ)
    (hi : Integrable f (scalarObservationHistoryLaw z dt n)) :
    (∫ u, scalarHiddenSign u.1 * f u.2 ∂scalarHiddenJointHistoryLaw z dt n) =
      ∫ H, Real.tanh (scalarLastField z n H) * f H ∂scalarObservationHistoryLaw z dt n := by
  have hs : ∀ b : Bool, Integrable scalarHiddenSign (Measure.dirac b) := by
    intro b
    exact integrable_dirac (by finiteness)
  have hh (b : Bool) := integrable_scalarHiddenHistory_of_observation b z dt n f hi
  rw [scalarHiddenJointHistoryLaw,
    integral_add_measure (((hs true).mul_prod (hh true)).smul_measure ENNReal.ofReal_ne_top)
      (((hs false).mul_prod (hh false)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (scalarPlusWeight_pos z).le,
    ENNReal.toReal_ofReal (scalarMinusWeight_pos z).le,
    integral_prod_mul scalarHiddenSign f, integral_prod_mul scalarHiddenSign f,
    integral_dirac, integral_dirac]
  simp only [scalarHiddenSign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul,
    smul_eq_mul, mul_neg, ← sub_eq_add_neg]
  have hp := integrable_scalarHiddenWeight_mul true (scalarLastField z n) f
    (measurable_scalarLastField z n) hi
  have hm := integrable_scalarHiddenWeight_mul false (scalarLastField z n) f
    (measurable_scalarLastField z n) hi
  change scalarHiddenWeight true z * (∫ H, f H ∂scalarHiddenObservationHistoryLaw true z dt n) -
    scalarHiddenWeight false z * (∫ H, f H ∂scalarHiddenObservationHistoryLaw false z dt n) = _
  rw [← integral_scalarHistory_hiddenWeight_mul true z dt n f,
    ← integral_scalarHistory_hiddenWeight_mul false z dt n f, ← integral_sub hp hm]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro H
  change scalarHiddenWeight true (scalarLastField z n H) * f H -
    scalarHiddenWeight false (scalarLastField z n H) * f H = _
  rw [← sub_mul]
  change (scalarPlusWeight (scalarLastField z n H) - scalarMinusWeight (scalarLastField z n H)) * f H = _
  rw [scalarWeight_difference]

lemma integrable_scalarHiddenJoint_sign_mul (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ)
    (f : ScalarObservationHistory n → ℝ)
    (hi : Integrable f (scalarObservationHistoryLaw z dt n)) :
    Integrable (fun u => scalarHiddenSign u.1 * f u.2) (scalarHiddenJointHistoryLaw z dt n) := by
  have hs (b : Bool) : Integrable scalarHiddenSign (Measure.dirac b) :=
    integrable_dirac (by finiteness)
  have hh (b : Bool) := integrable_scalarHiddenHistory_of_observation b z dt n f hi
  rw [scalarHiddenJointHistoryLaw]
  exact (((hs true).mul_prod (hh true)).smul_measure ENNReal.ofReal_ne_top).add_measure
    (((hs false).mul_prod (hh false)).smul_measure ENNReal.ofReal_ne_top)

lemma integrable_scalarHistoryPosteriorInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Integrable (fun H => Real.tanh (scalarLastField z n H) * scalarHistoryInnovationSum z dt n H)
      (scalarObservationHistoryLaw z dt n) :=
  integrable_tanh_mul (scalarLastField z n) (scalarHistoryInnovationSum z dt n)
    (measurable_scalarLastField z n) (integrable_scalarHistoryInnovationSum z dt n)

lemma integral_scalarHistoryPosteriorInnovationSum_succ (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ H, Real.tanh (scalarLastField z (n + 1) H) * scalarHistoryInnovationSum z dt (n + 1) H
      ∂scalarObservationHistoryLaw z dt (n + 1)) =
      (∫ H, Real.tanh (scalarLastField z n H) * scalarHistoryInnovationSum z dt n H
        ∂scalarObservationHistoryLaw z dt n) +
        (dt n : ℝ) * (∫ H, scalarDefect (scalarLastField z n H) ∂scalarObservationHistoryLaw z dt n) := by
  have hp := integrable_tanh_mul (fun H : ScalarObservationHistory (n + 1) => H.2)
    (fun H => scalarHistoryInnovationSum z dt n H.1) measurable_snd
    (integrable_scalarHistoryLift z dt n _ (measurable_scalarHistoryInnovationSum z dt n)
      (integrable_scalarHistoryInnovationSum z dt n))
  have hj := integrable_tanh_mul (fun H : ScalarObservationHistory (n + 1) => H.2)
    (fun H => scalarInnovation (scalarLastField z n H.1) (dt n) H.2) measurable_snd
    (integrable_scalarHistoryInnovationStep z dt n)
  change (∫ H : ScalarObservationHistory (n + 1), Real.tanh H.2 *
    (scalarHistoryInnovationSum z dt n H.1 + scalarInnovation (scalarLastField z n H.1) (dt n) H.2)
    ∂scalarObservationHistoryLaw z dt (n + 1)) = _
  simp_rw [mul_add]
  rw [integral_add hp hj]
  change (∫ H : ScalarObservationHistory n × ℝ,
    Real.tanh H.2 * scalarHistoryInnovationSum z dt n H.1
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) +
    (∫ H : ScalarObservationHistory n × ℝ,
    Real.tanh H.2 * scalarInnovation (scalarLastField z n H.1) (dt n) H.2
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) = _
  rw [Measure.integral_compProd hp, Measure.integral_compProd hj]
  simp_rw [scalarObservationStepKernel_apply, integral_mul_const, integral_tanh_scalarTransitionKernel,
    integral_tanh_mul_scalarInnovation]
  rw [integral_const_mul]

lemma integral_scalarHiddenSign_innovationSum (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ u, scalarHiddenSign u.1 * scalarHistoryInnovationSum z dt n u.2
      ∂scalarHiddenJointHistoryLaw z dt n) =
      ∑ k ∈ Finset.range n, (dt k : ℝ) *
        (∫ H, scalarDefect (scalarLastField z k H) ∂scalarObservationHistoryLaw z dt k) := by
  rw [integral_scalarHiddenJoint_sign_mul z dt n _
    (integrable_scalarHistoryInnovationSum z dt n)]
  induction n with
  | zero => simp [scalarHistoryInnovationSum]
  | succ n ih => rw [integral_scalarHistoryPosteriorInnovationSum_succ, Finset.sum_range_succ, ih]

lemma scalarUniformHiddenJointHistory_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (n m : ℕ) :
    HasLaw (fun u : Bool × Ω => (u.1, scalarUniformObservationHistory z B n m u))
      (scalarHiddenJointHistoryLaw z (brownianMeshVariance (scalarUniformTime n)) m)
      (scalarHiddenBrownianLaw z P) :=
  scalarBrownianPriorField_jointHistory_hasLaw hB z (scalarUniformTime n)
    (scalarUniformTime_monotone n) (scalarUniformTime_zero n) m

lemma integrable_scalarUniformHiddenSignInnovation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (n m : ℕ) :
    Integrable (fun u => scalarHiddenSign u.1 * scalarEulerInnovation z B (scalarUniformTime n m) n u)
      (scalarHiddenBrownianLaw z P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi := (scalarUniformHiddenJointHistory_hasLaw hB z n m).integrable_comp
    (integrable_scalarHiddenJoint_sign_mul z (brownianMeshVariance (scalarUniformTime n)) m
      (scalarHistoryInnovationSum z (brownianMeshVariance (scalarUniformTime n)) m)
      (integrable_scalarHistoryInnovationSum z _ m))
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  apply hi.congr
  filter_upwards [hz] with u hu
  simp only [Function.comp_def]
  rw [scalarHistoryInnovationSum_uniform_eq z B n m u hu]

lemma integral_scalarUniformDefect (z : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (n k : ℕ) :
    (∫ H, scalarDefect (scalarLastField z k H)
      ∂scalarObservationHistoryLaw z (brownianMeshVariance (scalarUniformTime n)) k) =
      ∫ u, scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u)
        ∂scalarHiddenBrownianLaw z P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi := (scalarUniformObservationHistory_hasLaw hB z n k).integral_comp
    ((measurable_scalarDefect.comp (measurable_scalarLastField z k)).aestronglyMeasurable)
  apply hi.symm.trans
  apply integral_congr_ae
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  filter_upwards [hz] with u hu
  simp only [Function.comp_def]
  congr 1
  rw [scalarUniformObservationHistory]
  have hy : scalarHiddenContinuousField z B (scalarUniformTime n 0) u = z := by
    simp [scalarHiddenContinuousField, scalarUniformTime_zero, hu]
  exact scalarLastField_sampled (fun k => scalarHiddenContinuousField z B (scalarUniformTime n k))
    z k u hy

lemma integral_scalarUniformHiddenSignInnovation (z : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (n m : ℕ) :
    (∫ u, scalarHiddenSign u.1 * scalarEulerInnovation z B (scalarUniformTime n m) n u
      ∂scalarHiddenBrownianLaw z P) =
      ∑ k ∈ Finset.range m, (1 / ((n : ℝ) + 1)) *
        (∫ u, scalarDefect (scalarHiddenContinuousField z B (scalarUniformTime n k) u)
          ∂scalarHiddenBrownianLaw z P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmeas : Measurable (fun u : Bool × ScalarObservationHistory m =>
      scalarHiddenSign u.1 * scalarHistoryInnovationSum z (brownianMeshVariance (scalarUniformTime n)) m u.2) :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul
      ((measurable_scalarHistoryInnovationSum z _ m).comp measurable_snd)
  have hi := (scalarUniformHiddenJointHistory_hasLaw hB z n m).integral_comp hmeas.aestronglyMeasurable
  rw [integral_scalarHiddenSign_innovationSum] at hi
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  have he : (fun u => scalarHiddenSign u.1 * scalarHistoryInnovationSum z
      (brownianMeshVariance (scalarUniformTime n)) m (scalarUniformObservationHistory z B n m u))
      =ᵐ[scalarHiddenBrownianLaw z P]
      (fun u => scalarHiddenSign u.1 * scalarEulerInnovation z B (scalarUniformTime n m) n u) := by
    filter_upwards [hz] with u hu
    rw [scalarHistoryInnovationSum_uniform_eq z B n m u hu]
  rw [← integral_congr_ae he]
  calc
    _ = _ := hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_scalarUniformDefect z hB n k, brownianMeshVariance_scalarUniformTime]
      simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]

end SKConstants
