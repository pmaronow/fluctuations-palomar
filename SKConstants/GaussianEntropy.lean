module

public import SKConstants.ScalarProcessGaussianMoments
public import SKConstants.AdaptedGaussianMGF
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem gaussianReal_absolutelyContinuous_gaussianReal (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal a v ≪ gaussianReal b v :=
  (gaussianReal_absolutelyContinuous a hv).trans (gaussianReal_absolutelyContinuous' b hv)

theorem rnDeriv_gaussianReal_eq_density_ratio (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (gaussianReal a v).rnDeriv (gaussianReal b v) =ᵐ[gaussianReal b v]
      fun x => gaussianPDF a v x / gaussianPDF b v x := by
  have hbvol := gaussianReal_absolutelyContinuous b hv
  filter_upwards [Measure.rnDeriv_eq_div (gaussianReal_absolutelyContinuous a hv) hbvol,
    (rnDeriv_gaussianReal a v).filter_mono hbvol.ae_le,
    (rnDeriv_gaussianReal b v).filter_mono hbvol.ae_le] with x hratio ha hb
  rw [hratio, ha, hb]

theorem log_gaussianPDFReal_ratio (a b x : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Real.log (gaussianPDFReal a v x / gaussianPDFReal b v x) =
      ((x - b) ^ 2 - (x - a) ^ 2) / (2 * (v : ℝ)) := by
  rw [Real.log_div (gaussianPDFReal_pos a v x hv).ne' (gaussianPDFReal_pos b v x hv).ne']
  have hpref : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by
    have hvp : 0 < (v : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hv
    positivity
  simp only [gaussianPDFReal]
  rw [Real.log_mul hpref (Real.exp_pos _).ne',
    Real.log_mul hpref (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  ring

theorem llr_gaussianReal_eq_square_difference (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    llr (gaussianReal a v) (gaussianReal b v) =ᵐ[gaussianReal a v]
      fun x => ((x - b) ^ 2 - (x - a) ^ 2) / (2 * (v : ℝ)) := by
  have hac := gaussianReal_absolutelyContinuous_gaussianReal a b v hv
  filter_upwards [(rnDeriv_gaussianReal_eq_density_ratio a b v hv).filter_mono hac.ae_le]
    with x hx
  simp only [llr, hx, ENNReal.toReal_div, toReal_gaussianPDF]
  exact log_gaussianPDFReal_ratio a b x v hv

theorem integrable_llr_gaussianReal (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (llr (gaussianReal a v) (gaussianReal b v)) (gaussianReal a v) :=
  (((gaussianReal_integrable_shift_sq a b v).sub
    (gaussianReal_integrable_shift_sq a a v)).div_const (2 * (v : ℝ))).congr
      (llr_gaussianReal_eq_square_difference a b v hv).symm

theorem integral_llr_gaussianReal (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ x, llr (gaussianReal a v) (gaussianReal b v) x ∂gaussianReal a v) =
      (a - b) ^ 2 / (2 * (v : ℝ)) := by
  rw [integral_congr_ae (llr_gaussianReal_eq_square_difference a b v hv), integral_div,
    integral_sub (gaussianReal_integrable_shift_sq a b v)
      (gaussianReal_integrable_shift_sq a a v),
    gaussianReal_integral_shift_sq, gaussianReal_integral_shift_sq]
  congr 1
  ring

theorem klDiv_gaussianReal_same_variance (a b : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) =
      ENNReal.ofReal ((a - b) ^ 2 / (2 * (v : ℝ))) := by
  rw [klDiv_of_ac_of_integrable (gaussianReal_absolutelyContinuous_gaussianReal a b v hv)
    (integrable_llr_gaussianReal a b v hv), integral_llr_gaussianReal a b v hv]
  simp only [probReal_univ, add_sub_cancel_right]

theorem klDiv_prod_swap {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) (rho eta : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure rho] [IsProbabilityMeasure eta] :
    klDiv (mu.prod rho) (nu.prod eta) = klDiv (rho.prod mu) (eta.prod nu) := by
  apply le_antisymm
  · simpa only [Measure.prod_swap] using
      klDiv_map_le (rho.prod mu) (eta.prod nu) measurable_swap
  · simpa only [Measure.prod_swap] using
      klDiv_map_le (mu.prod rho) (nu.prod eta) measurable_swap

theorem klDiv_prod_add {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) (rho eta : Measure B)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure rho] [IsProbabilityMeasure eta] :
    klDiv (mu.prod rho) (nu.prod eta) = klDiv mu nu + klDiv rho eta := by
  have hsame : klDiv (mu.prod rho) (mu.prod eta) = klDiv rho eta := by
    rw [klDiv_prod_swap]
    simpa only [Measure.compProd_const] using klDiv_compProd_left rho eta (Kernel.const B mu)
  have hchain := klDiv_compProd_eq_add mu nu (Kernel.const A rho) (Kernel.const A eta)
  simpa only [Measure.compProd_const, hsame] using hchain

def gaussianMeanHistoryLaw (mean : ℕ → ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → Measure (GaussianHistory n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (gaussianMeanHistoryLaw mean dt n).prod (gaussianReal (mean n) (dt n))

instance gaussianMeanHistoryLaw_isProbability (mean : ℕ → ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (gaussianMeanHistoryLaw mean dt n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    change IsProbabilityMeasure ((gaussianMeanHistoryLaw mean dt n).prod
      (gaussianReal (mean n) (dt n)))
    infer_instance

theorem klDiv_gaussianMeanHistoryLaw (a b : ℕ → ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (hdt : ∀ k < n, dt k ≠ 0) :
    klDiv (gaussianMeanHistoryLaw a dt n) (gaussianMeanHistoryLaw b dt n) =
      ENNReal.ofReal (∑ k ∈ Finset.range n, (a k - b k) ^ 2 / (2 * (dt k : ℝ))) := by
  induction n with
  | zero => simp [gaussianMeanHistoryLaw]
  | succ n ih =>
    rw [gaussianMeanHistoryLaw, gaussianMeanHistoryLaw, klDiv_prod_add,
      ih (fun k hk => hdt k (by omega)),
      klDiv_gaussianReal_same_variance _ _ _ (hdt n (by omega)), Finset.sum_range_succ]
    exact (ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => by positivity) (by positivity)).symm

theorem klDiv_map_measurableEquiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu nu : Measure A) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (e : A ≃ᵐ B) : klDiv (mu.map e) (nu.map e) = klDiv mu nu := by
  apply le_antisymm
  · exact klDiv_map_le mu nu e.measurable
  · simpa only [MeasurableEquiv.map_symm_map] using
      klDiv_map_le (mu.map e) (nu.map e) e.symm.measurable

theorem klDiv_compProd_same_left_eq_lintegral {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace.CountableOrCountablyGenerated A B]
    (mu : Measure A) [IsProbabilityMeasure mu] (ka kb : Kernel A B)
    [IsMarkovKernel ka] [IsMarkovKernel kb] (hac : ∀ i, ka i ≪ kb i) :
    klDiv (mu ⊗ₘ ka) (mu ⊗ₘ kb) = ∫⁻ i, klDiv (ka i) (kb i) ∂mu := by
  have hjac : mu ⊗ₘ ka ≪ mu ⊗ₘ kb :=
    Measure.AbsolutelyContinuous.compProd_right (ae_of_all _ hac)
  rw [klDiv_eq_lintegral_klFun_of_ac hjac]
  have hJoint : (fun p => ENNReal.ofReal (klFun ((mu ⊗ₘ ka).rnDeriv (mu ⊗ₘ kb) p).toReal))
      =ᵐ[mu ⊗ₘ kb] fun p => ENNReal.ofReal (klFun (ka.rnDeriv kb p.1 p.2).toReal) := by
    filter_upwards [rnDeriv_measure_compProd_right mu ka kb] with p hp
    rw [hp]
  rw [lintegral_congr_ae hJoint, Measure.lintegral_compProd (by fun_prop)]
  refine lintegral_congr_ae (ae_of_all _ fun i => ?_)
  change (∫⁻ x, ENNReal.ofReal (klFun (ka.rnDeriv kb i x).toReal) ∂kb i) =
    klDiv (ka i) (kb i)
  rw [klDiv_eq_lintegral_klFun_of_ac (hac i)]
  apply lintegral_congr_ae
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := ka) (η := kb) (a := i)]
    with x hx
  rw [hx]

theorem klDiv_pi_gaussianReal_same_variances (n : ℕ) (a b : Fin n → ℝ)
    (v : Fin n → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    klDiv (Measure.pi fun i => gaussianReal (a i) (v i))
      (Measure.pi fun i => gaussianReal (b i) (v i)) =
      ENNReal.ofReal (∑ i, (a i - b i) ^ 2 / (2 * (v i : ℝ))) := by
  induction n with
  | zero =>
    have hab : a = b := Subsingleton.elim _ _
    subst b
    simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    rw [← klDiv_map_measurableEquiv _ _ e]
    rw [(measurePreserving_piFinSuccAbove (fun i => gaussianReal (a i) (v i)) 0).map_eq,
      (measurePreserving_piFinSuccAbove (fun i => gaussianReal (b i) (v i)) 0).map_eq,
      klDiv_prod_add, klDiv_gaussianReal_same_variance _ _ _ (hv 0),
      ih (fun i => a ((0 : Fin (n + 1)).succAbove i))
        (fun i => b ((0 : Fin (n + 1)).succAbove i))
        (fun i => v ((0 : Fin (n + 1)).succAbove i)) (fun i => hv _)]
    rw [← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ => by positivity)]
    congr 1
    simp [Fin.sum_univ_succ]

def finiteGaussianSmoothingKernel {A : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (a : A → ℝ) (v : ℝ≥0) : Kernel A ℝ where
  toFun i := gaussianReal (a i) v
  measurable' := measurable_of_countable _

instance finiteGaussianSmoothingKernel_isMarkov {A : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (a : A → ℝ) (v : ℝ≥0) :
    IsMarkovKernel (finiteGaussianSmoothingKernel a v) := by
  constructor
  intro i
  change IsProbabilityMeasure (gaussianReal (a i) v)
  infer_instance

theorem integrable_finite_label {A : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (mu : Measure A) [IsFiniteMeasure mu] (f : A → ℝ) :
    Integrable f mu := by
  classical
  exact Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable
    (∑ i, ‖f i‖) (ae_of_all _ fun i =>
      Finset.single_le_sum (fun j _ => norm_nonneg (f j)) (Finset.mem_univ i))

theorem klDiv_joint_finiteGaussianSmoothing {A : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (mu : Measure A) [IsProbabilityMeasure mu]
    (a b : A → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (mu ⊗ₘ finiteGaussianSmoothingKernel a v)
      (mu ⊗ₘ finiteGaussianSmoothingKernel b v) =
      ENNReal.ofReal (∫ i, (a i - b i) ^ 2 / (2 * (v : ℝ)) ∂mu) := by
  have ha : Measurable a := measurable_of_countable _
  have hb : Measurable b := measurable_of_countable _
  let ka := finiteGaussianSmoothingKernel a v
  let kb := finiteGaussianSmoothingKernel b v
  have hac : mu ⊗ₘ ka ≪ mu ⊗ₘ kb :=
    Measure.AbsolutelyContinuous.compProd_right
      (ae_of_all _ fun i => gaussianReal_absolutelyContinuous_gaussianReal (a i) (b i) v hv)
  have hkernel : ∀ᵐ p ∂(mu ⊗ₘ kb), ka.rnDeriv kb p.1 p.2 =
      gaussianPDF (a p.1) v p.2 / gaussianPDF (b p.1) v p.2 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun (Kernel.measurable_rnDeriv ka kb) (by fun_prop))
    exact ae_of_all _ fun i =>
      (Kernel.rnDeriv_eq_rnDeriv_measure (κ := ka) (η := kb) (a := i)).trans
        (rnDeriv_gaussianReal_eq_density_ratio (a i) (b i) v hv)
  have hllr : llr (mu ⊗ₘ ka) (mu ⊗ₘ kb) =ᵐ[mu ⊗ₘ ka]
      fun p => ((p.2 - b p.1) ^ 2 - (p.2 - a p.1) ^ 2) / (2 * (v : ℝ)) := by
    filter_upwards [(rnDeriv_measure_compProd_right mu ka kb).filter_mono hac.ae_le,
      hkernel.filter_mono hac.ae_le] with p hp hkp
    simp only [llr, hp, hkp, ENNReal.toReal_div, toReal_gaussianPDF]
    exact log_gaussianPDFReal_ratio (a p.1) (b p.1) p.2 v hv
  have hpoly : Integrable
      (fun p : A × ℝ => ((p.2 - b p.1) ^ 2 - (p.2 - a p.1) ^ 2) / (2 * (v : ℝ)))
      (mu ⊗ₘ ka) := by
    apply (Measure.integrable_compProd_iff (by fun_prop)).mpr
    constructor
    · exact ae_of_all _ fun i =>
        ((gaussianReal_integrable_shift_sq (a i) (b i) v).sub
          (gaussianReal_integrable_shift_sq (a i) (a i) v)).div_const _
    · exact integrable_finite_label mu _
  rw [klDiv_of_ac_of_integrable hac (hpoly.congr hllr.symm)]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae hllr, Measure.integral_compProd hpoly]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun i => by
    change (∫ x : ℝ, ((x - b i) ^ 2 - (x - a i) ^ 2) / (2 * (v : ℝ))
      ∂gaussianReal (a i) v) = (a i - b i) ^ 2 / (2 * (v : ℝ))
    rw [integral_div, integral_sub (gaussianReal_integrable_shift_sq (a i) (b i) v)
      (gaussianReal_integrable_shift_sq (a i) (a i) v),
      gaussianReal_integral_shift_sq, gaussianReal_integral_shift_sq]
    congr 1
    ring

theorem klDiv_finiteGaussianSmoothing_mixture_le {A : Type*} [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (mu : Measure A) [IsProbabilityMeasure mu]
    (a b : A → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (finiteGaussianSmoothingKernel a v ∘ₘ mu)
      (finiteGaussianSmoothingKernel b v ∘ₘ mu) ≤
      ENNReal.ofReal (∫ i, (a i - b i) ^ 2 / (2 * (v : ℝ)) ∂mu) := by
  have h := klDiv_map_le (mu ⊗ₘ finiteGaussianSmoothingKernel a v)
    (mu ⊗ₘ finiteGaussianSmoothingKernel b v) measurable_snd
  change klDiv (mu ⊗ₘ finiteGaussianSmoothingKernel a v).snd
    (mu ⊗ₘ finiteGaussianSmoothingKernel b v).snd ≤ _ at h
  rw [Measure.snd_compProd, Measure.snd_compProd,
    klDiv_joint_finiteGaussianSmoothing mu a b v hv] at h
  exact h

end SKConstants
