module

public import SKConstants.BrownianGaussianHistory
public import SKConstants.ScalarProcessHiddenChannel

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def scalarDriftedGaussianHistory (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → GaussianHistory n → ScalarObservationHistory n
  | 0, _ => PUnit.unit
  | n + 1, h =>
      let past := scalarDriftedGaussianHistory b z dt n h.1
      (past, scalarLastField z n past + scalarHiddenSign b * (dt n : ℝ) + h.2)

theorem measurable_scalarDriftedGaussianHistory (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) : Measurable (scalarDriftedGaussianHistory b z dt n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).prodMk
      (((measurable_scalarLastField z n).comp (ih.comp measurable_fst)).add_const _ |>.add
        measurable_snd)

theorem scalarDriftedGaussianHistory_hasLaw (b : Bool) (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) :
    HasLaw (scalarDriftedGaussianHistory b z dt n) (scalarHiddenObservationHistoryLaw b z dt n)
      (gaussianHistoryLaw dt n) := by
  refine ⟨(measurable_scalarDriftedGaussianHistory b z dt n).aemeasurable, ?_⟩
  induction n with
  | zero =>
    change (Measure.dirac PUnit.unit).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    change ((gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n))).map
      (scalarDriftedGaussianHistory b z dt (n + 1)) =
      scalarHiddenObservationHistoryLaw b z dt n ⊗ₘ
        scalarHiddenObservationStepKernel b z (dt n) n
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_scalarDriftedGaussianHistory b z dt (n + 1))]
    change (∫⁻ p : GaussianHistory n × ℝ,
      f (scalarDriftedGaussianHistory b z dt (n + 1) p)
      ∂(gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n))) =
      ∫⁻ p : ScalarObservationHistory n × ℝ, f p
      ∂scalarHiddenObservationHistoryLaw b z dt n ⊗ₘ
        scalarHiddenObservationStepKernel b z (dt n) n
    have hg : Measurable (fun p : GaussianHistory n × ℝ =>
        f (scalarDriftedGaussianHistory b z dt (n + 1) p)) :=
      hf.comp (measurable_scalarDriftedGaussianHistory b z dt (n + 1))
    rw [lintegral_prod _ hg.aemeasurable, Measure.lintegral_compProd hf]
    have hinner (h : GaussianHistory n) :
        (∫⁻ x, f (scalarDriftedGaussianHistory b z dt (n + 1) (h, x))
          ∂gaussianReal 0 (dt n)) =
        ∫⁻ y, f (scalarDriftedGaussianHistory b z dt n h, y)
          ∂scalarHiddenObservationStepKernel b z (dt n) n
            (scalarDriftedGaussianHistory b z dt n h) := by
      rw [scalarHiddenObservationStepKernel_apply]
      have hshift : (gaussianReal 0 (dt n)).map
          (fun x => scalarLastField z n (scalarDriftedGaussianHistory b z dt n h) +
            scalarHiddenSign b * (dt n : ℝ) + x) =
          gaussianReal (scalarLastField z n (scalarDriftedGaussianHistory b z dt n h) +
            scalarHiddenSign b * (dt n : ℝ)) (dt n) := by
        simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := dt n)
          (scalarLastField z n (scalarDriftedGaussianHistory b z dt n h) +
            scalarHiddenSign b * (dt n : ℝ))
      rw [← hshift]
      exact (lintegral_map (f := fun y => f (scalarDriftedGaussianHistory b z dt n h, y))
        (hf.comp measurable_prodMk_left)
        (measurable_const_add (scalarLastField z n (scalarDriftedGaussianHistory b z dt n h) +
          scalarHiddenSign b * (dt n : ℝ)))).symm
    simp_rw [hinner]
    have hmeas : Measurable (fun h : ScalarObservationHistory n =>
        ∫⁻ y, f (h, y) ∂scalarHiddenObservationStepKernel b z (dt n) n h) :=
      hf.lintegral_kernel_prod_right'
    rw [← ih, lintegral_map hmeas (measurable_scalarDriftedGaussianHistory b z dt n)]

def scalarSampledFieldHistory {Ω : Type*} (Y : ℕ → Ω → ℝ) :
    (n : ℕ) → Ω → ScalarObservationHistory n
  | 0, _ => PUnit.unit
  | n + 1, omega => (scalarSampledFieldHistory Y n omega, Y n omega)

theorem aemeasurable_scalarSampledFieldHistory {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ k, AEMeasurable (Y k) P) (n : ℕ) :
    AEMeasurable (scalarSampledFieldHistory Y n) P := by
  induction n with
  | zero => exact aemeasurable_const
  | succ n ih => exact ih.prodMk (hY n)

theorem scalarSampledFieldHistory_comp {A Ω : Type*} (Y : ℕ → A → ℝ)
    (f : Ω → A) (n : ℕ) (omega : Ω) :
    scalarSampledFieldHistory Y n (f omega) =
      scalarSampledFieldHistory (fun k omega => Y k (f omega)) n omega := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (_, _) = (_, _)
    rw [ih]

theorem scalarLastField_sampled {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ)
    (n : ℕ) (omega : Ω) (hzero : Y 0 omega = z) :
    scalarLastField z n (scalarSampledFieldHistory (fun k => Y (k + 1)) n omega) =
      Y n omega := by
  cases n with
  | zero => exact hzero.symm
  | succ n => rfl

theorem scalarHistoryInnovationSum_sampled {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ)
    (dt : ℕ → ℝ≥0) (n : ℕ) (omega : Ω) (hzero : Y 0 omega = z) :
    scalarHistoryInnovationSum z dt n
        (scalarSampledFieldHistory (fun k => Y (k + 1)) n omega) =
      Y n omega - z - ∑ k ∈ Finset.range n, (dt k : ℝ) * Real.tanh (Y k omega) := by
  induction n with
  | zero => simp only [scalarHistoryInnovationSum, hzero, sub_self, Finset.sum_range_zero]
  | succ n ih =>
    change scalarHistoryInnovationSum z dt n
      (scalarSampledFieldHistory (fun k => Y (k + 1)) n omega) +
      scalarInnovation (scalarLastField z n
        (scalarSampledFieldHistory (fun k => Y (k + 1)) n omega)) (dt n) (Y (n + 1) omega) = _
    rw [ih, scalarLastField_sampled Y z n omega hzero, Finset.sum_range_succ]
    unfold scalarInnovation
    ring

def scalarBrownianHiddenField {Ω : Type*} (b : Bool) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (k : ℕ) (omega : Ω) : ℝ :=
  z + scalarHiddenSign b * ((t (k + 1) : ℝ) - (t 0 : ℝ)) +
    B (t (k + 1)) omega - B (t 0) omega

theorem scalarDriftedGaussianHistory_brownian_last {Ω : Type*}
    (b : Bool) (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (omega : Ω) :
    scalarLastField z n (scalarDriftedGaussianHistory b z (brownianMeshVariance t) n
      (brownianGaussianHistory B t n omega)) =
      z + scalarHiddenSign b * ((t n : ℝ) - (t 0 : ℝ)) + B (t n) omega - B (t 0) omega := by
  induction n with
  | zero => simp [scalarLastField]
  | succ n ih =>
    change scalarLastField z n (scalarDriftedGaussianHistory b z (brownianMeshVariance t) n
        (brownianGaussianHistory B t n omega)) +
      scalarHiddenSign b * (brownianMeshVariance t n : ℝ) + brownianMeshIncrement B t n omega = _
    rw [ih]
    unfold brownianMeshVariance brownianMeshIncrement
    rw [NNReal.coe_sub (ht (by omega))]
    ring

theorem scalarDriftedGaussianHistory_brownian_eq {Ω : Type*}
    (b : Bool) (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (n : ℕ) (omega : Ω) :
    scalarDriftedGaussianHistory b z (brownianMeshVariance t) n
      (brownianGaussianHistory B t n omega) =
      scalarSampledFieldHistory (scalarBrownianHiddenField b z B t) n omega := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (scalarDriftedGaussianHistory b z (brownianMeshVariance t) n
      (brownianGaussianHistory B t n omega), _) =
      (scalarSampledFieldHistory (scalarBrownianHiddenField b z B t) n omega, _)
    congr 1
    have he := scalarDriftedGaussianHistory_brownian_last b z B t ht (n + 1) omega
    exact he

theorem scalarBrownianHiddenField_history_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (b : Bool) (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) :
    HasLaw (scalarSampledFieldHistory (scalarBrownianHiddenField b z B t) n)
      (scalarHiddenObservationHistoryLaw b z (brownianMeshVariance t) n) P := by
  have h := (scalarDriftedGaussianHistory_hasLaw b z (brownianMeshVariance t) n).comp
    (brownianGaussianHistory_hasLaw hB t ht n)
  have he : (scalarDriftedGaussianHistory b z (brownianMeshVariance t) n ∘
      brownianGaussianHistory B t n) =
      scalarSampledFieldHistory (scalarBrownianHiddenField b z B t) n :=
    funext (scalarDriftedGaussianHistory_brownian_eq b z B t ht n)
  rwa [he] at h

theorem scalarBrownianField_history_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (b : Bool) (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    HasLaw (scalarSampledFieldHistory (fun k omega =>
        z + scalarHiddenSign b * (t (k + 1) : ℝ) + B (t (k + 1)) omega) n)
      (scalarHiddenObservationHistoryLaw b z (brownianMeshVariance t) n) P := by
  apply (scalarBrownianHiddenField_history_hasLaw hB b z t ht n).congr
  filter_upwards [hB.eval_zero_ae_eq_zero] with omega hzero
  have he : (fun k => z + scalarHiddenSign b * (t (k + 1) : ℝ) + B (t (k + 1)) omega) =
      fun k => scalarBrownianHiddenField b z B t k omega := by
    funext k
    simp only [scalarBrownianHiddenField, ht0, NNReal.coe_zero, sub_zero, hzero]
  induction n with
  | zero => rfl
  | succ n ih =>
    change (_, z + scalarHiddenSign b * (t (n + 1) : ℝ) + B (t (n + 1)) omega) =
      (_, scalarBrownianHiddenField b z B t n omega)
    rw [ih, congrFun he n]

theorem scalarBrownianPriorField_history_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    HasLaw (scalarSampledFieldHistory (fun k (u : Bool × Ω) =>
        z + scalarHiddenSign u.1 * (t (k + 1) : ℝ) + B (t (k + 1)) u.2) n)
      (scalarObservationHistoryLaw z (brownianMeshVariance t) n)
      ((ENNReal.ofReal (scalarPlusWeight z) • Measure.dirac true +
        ENNReal.ofReal (scalarMinusWeight z) • Measure.dirac false).prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let F : Bool × Ω → ScalarObservationHistory n :=
    scalarSampledFieldHistory (fun k (u : Bool × Ω) =>
      z + scalarHiddenSign u.1 * (t (k + 1) : ℝ) + B (t (k + 1)) u.2) n
  have hm (rho : Measure Bool) : AEMeasurable F (rho.prod P) := by
    apply aemeasurable_scalarSampledFieldHistory
    intro k
    have hsign : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1) :=
      (measurable_of_countable scalarHiddenSign).comp measurable_fst
    exact (hsign.mul_const _ |>.const_add z).aemeasurable.add
      ((hB.aemeasurable (t (k + 1))).comp_snd)
  have hmap (b : Bool) : ((Measure.dirac b).prod P).map F =
      scalarHiddenObservationHistoryLaw b z (brownianMeshVariance t) n := by
    have hF := hm (Measure.dirac b)
    rw [Measure.dirac_prod] at hF ⊢
    rw [AEMeasurable.map_map_of_aemeasurable hF measurable_prodMk_left.aemeasurable]
    have he : F ∘ Prod.mk b = scalarSampledFieldHistory
        (fun k omega => z + scalarHiddenSign b * (t (k + 1) : ℝ) + B (t (k + 1)) omega) n := by
      funext omega
      exact scalarSampledFieldHistory_comp _ (Prod.mk b) n omega
    rw [he]
    exact (scalarBrownianField_history_hasLaw hB b z t ht ht0 n).map_eq
  refine ⟨hm _, ?_⟩
  change ((ENNReal.ofReal (scalarPlusWeight z) • Measure.dirac true +
      ENNReal.ofReal (scalarMinusWeight z) • Measure.dirac false).prod P).map F = _
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    AEMeasurable.map_add₀ ((hm _).smul_measure _) ((hm _).smul_measure _),
    Measure.map_smul _ (hm _), Measure.map_smul _ (hm _), hmap, hmap]
  exact (scalarObservationHistoryLaw_eq_hidden_mixture z (brownianMeshVariance t) n).symm

theorem scalarBrownianPriorField_jointHistory_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (z : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    HasLaw (fun u : Bool × Ω => (u.1, scalarSampledFieldHistory
        (fun k (u : Bool × Ω) =>
          z + scalarHiddenSign u.1 * (t (k + 1) : ℝ) + B (t (k + 1)) u.2) n u))
      (scalarHiddenJointHistoryLaw z (brownianMeshVariance t) n)
      ((ENNReal.ofReal (scalarPlusWeight z) • Measure.dirac true +
        ENNReal.ofReal (scalarMinusWeight z) • Measure.dirac false).prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let F : Bool × Ω → ScalarObservationHistory n :=
    scalarSampledFieldHistory (fun k (u : Bool × Ω) =>
      z + scalarHiddenSign u.1 * (t (k + 1) : ℝ) + B (t (k + 1)) u.2) n
  let G : Bool × Ω → Bool × ScalarObservationHistory n := fun u => (u.1, F u)
  have hm (rho : Measure Bool) : AEMeasurable G (rho.prod P) := by
    apply measurable_fst.aemeasurable.prodMk
    apply aemeasurable_scalarSampledFieldHistory
    intro k
    have hsign : Measurable (fun u : Bool × Ω => scalarHiddenSign u.1) :=
      (measurable_of_countable scalarHiddenSign).comp measurable_fst
    exact (hsign.mul_const _ |>.const_add z).aemeasurable.add
      ((hB.aemeasurable (t (k + 1))).comp_snd)
  have hmap (b : Bool) : ((Measure.dirac b).prod P).map G =
      (Measure.dirac b).prod (scalarHiddenObservationHistoryLaw b z (brownianMeshVariance t) n) := by
    have hG := hm (Measure.dirac b)
    rw [Measure.dirac_prod] at hG ⊢
    rw [AEMeasurable.map_map_of_aemeasurable hG measurable_prodMk_left.aemeasurable]
    let H : Ω → ScalarObservationHistory n := scalarSampledFieldHistory
      (fun k omega => z + scalarHiddenSign b * (t (k + 1) : ℝ) + B (t (k + 1)) omega) n
    have hH : HasLaw H (scalarHiddenObservationHistoryLaw b z (brownianMeshVariance t) n) P :=
      scalarBrownianField_history_hasLaw hB b z t ht ht0 n
    have he : G ∘ Prod.mk b = Prod.mk b ∘ H := by
      funext omega
      apply Prod.ext
      · rfl
      · exact scalarSampledFieldHistory_comp _ (Prod.mk b) n omega
    rw [he, ← AEMeasurable.map_map_of_aemeasurable
      measurable_prodMk_left.aemeasurable hH.aemeasurable, hH.map_eq, Measure.dirac_prod]
  refine ⟨hm _, ?_⟩
  change ((ENNReal.ofReal (scalarPlusWeight z) • Measure.dirac true +
      ENNReal.ofReal (scalarMinusWeight z) • Measure.dirac false).prod P).map G = _
  rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    AEMeasurable.map_add₀ ((hm _).smul_measure _) ((hm _).smul_measure _),
    Measure.map_smul _ (hm _), Measure.map_smul _ (hm _), hmap, hmap]
  rfl

end SKConstants
