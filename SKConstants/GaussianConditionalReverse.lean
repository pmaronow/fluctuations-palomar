module

public import SKConstants.GaussianContinuumMixtures
public import SKConstants.ConditionalGibbsTransport

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def gaussianEuclideanSmoothingKernel {ι : Type*} [Fintype ι] (c : ℝ) (v : ℝ≥0) :
    Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  ((gaussianPiSmoothingKernel (fun _ : ι => v)).comap
    (fun z : EuclideanSpace ℝ ι => fun i => c * z i) (by fun_prop)).map
      (MeasurableEquiv.toLp 2 (ι → ℝ))

instance gaussianEuclideanSmoothingKernel_isMarkov {ι : Type*} [Fintype ι]
    (c : ℝ) (v : ℝ≥0) : IsMarkovKernel (gaussianEuclideanSmoothingKernel (ι := ι) c v) := by
  unfold gaussianEuclideanSmoothingKernel
  exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable

theorem gaussianEuclideanSmoothingKernel_apply {ι : Type*} [Fintype ι]
    (c : ℝ) (v : ℝ≥0) (z : EuclideanSpace ℝ ι) :
    gaussianEuclideanSmoothingKernel c v z =
      (Measure.pi (fun i => gaussianReal (c * z i) v)).map
        (MeasurableEquiv.toLp 2 (ι → ℝ)) := by
  rw [gaussianEuclideanSmoothingKernel, Kernel.map_apply _
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable, Kernel.comap_apply,
    gaussianPiSmoothingKernel_apply]

theorem gaussianEuclideanSmoothingKernel_eq_affine_map {ι : Type*} [Fintype ι]
    (c : ℝ) (v : ℝ≥0) (z : EuclideanSpace ℝ ι) :
    gaussianEuclideanSmoothingKernel c v z =
      (GaussianProposal.primitiveGaussian ι).map
        (fun w => c • z + Real.sqrt (v : ℝ) • w) := by
  let f : (ι → ℝ) → (ι → ℝ) := fun w i => c * z i + Real.sqrt (v : ℝ) * w i
  have hp : (Measure.pi (fun _ : ι => gaussianReal 0 1)).map f =
      Measure.pi (fun i => gaussianReal (c * z i) v) := by
    rw [Measure.pi_map_pi (fun i => (show Measurable
      (fun y : ℝ => c * z i + Real.sqrt (v : ℝ) * y) by fun_prop).aemeasurable)]
    congr 1
    funext i
    rw [show (fun y : ℝ => c * z i + Real.sqrt (v : ℝ) * y) =
      (fun y => c * z i + y) ∘ (fun y => Real.sqrt (v : ℝ) * y) by rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    simp
  rw [gaussianEuclideanSmoothingKernel_apply, ← hp, Measure.map_map
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable (by fun_prop),
    GaussianProposal.primitiveGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (WithLp.measurable_toLp 2 (ι → ℝ))]
  congr 1

theorem klDiv_gaussianEuclideanSmoothingKernel {ι : Type*} [Fintype ι]
    (c : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (z w : EuclideanSpace ℝ ι) :
    klDiv (gaussianEuclideanSmoothingKernel c v z)
      (gaussianEuclideanSmoothingKernel c v w) =
      ENNReal.ofReal (c ^ 2 / (2 * (v : ℝ))) * edist z w ^ 2 := by
  rw [gaussianEuclideanSmoothingKernel_apply, gaussianEuclideanSmoothingKernel_apply,
    klDiv_map_measurableEquiv, klDiv_pi_gaussianReal_same_variances_fintype
      (fun i => c * z i) (fun i => c * w i) (fun _ => v) (fun _ => hv)]
  have he : (∑ i, (c * z i - c * w i) ^ 2 / (2 * (v : ℝ))) =
      c ^ 2 / (2 * (v : ℝ)) * ‖z - w‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [PiLp.sub_apply]
    ring
  rw [he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
    edist_dist, dist_eq_norm]

theorem kernel_comp_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (f : A → B) (hf : Measurable f)
    (κ : Kernel B C) : κ ∘ₘ μ.map f = κ.comap f hf ∘ₘ μ := by
  rw [← Measure.deterministic_comp_eq_map hf, Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap]

theorem klDiv_gaussianEuclideanSmoothing_le_coupling {ι : Type*} [Fintype ι]
    (c : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (μ ν : Measure (EuclideanSpace ℝ ι))
    (q : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)) [IsProbabilityMeasure q]
    (hfst : q.map Prod.fst = μ) (hsnd : q.map Prod.snd = ν) :
    klDiv (gaussianEuclideanSmoothingKernel c v ∘ₘ ν)
      (gaussianEuclideanSmoothingKernel c v ∘ₘ μ) ≤
      ENNReal.ofReal (c ^ 2 / (2 * (v : ℝ))) * (∫⁻ p, edist p.1 p.2 ^ 2 ∂q) := by
  let κ := gaussianEuclideanSmoothingKernel (ι := ι) c v
  let ka : Kernel (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
    κ.comap Prod.snd measurable_snd
  let kb : Kernel (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
    κ.comap Prod.fst measurable_fst
  have hac (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ka p ≪ kb p := by
    apply (klDiv_ne_top_iff.mp ?_).1
    change klDiv (κ p.2) (κ p.1) ≠ ⊤
    rw [klDiv_gaussianEuclideanSmoothingKernel c v hv]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by finiteness)
  have h := klDiv_map_le (q ⊗ₘ ka) (q ⊗ₘ kb) measurable_snd
  change klDiv (q ⊗ₘ ka).snd (q ⊗ₘ kb).snd ≤ _ at h
  rw [Measure.snd_compProd, Measure.snd_compProd,
    klDiv_compProd_same_left_eq_lintegral q ka kb hac] at h
  rw [← hsnd, ← hfst, kernel_comp_map q Prod.snd measurable_snd,
    kernel_comp_map q Prod.fst measurable_fst]
  refine h.trans_eq ?_
  change (∫⁻ p, klDiv (κ p.2) (κ p.1) ∂q) = _
  dsimp only [κ]
  simp_rw [klDiv_gaussianEuclideanSmoothingKernel c v hv, edist_comm]
  exact lintegral_const_mul _ (by fun_prop)

theorem conditionalGibbs_reverse_smoothing_KL {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (proposal : Measure (EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure proposal]
    (c : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianEuclideanSmoothingKernel c v ∘ₘ conditionalGibbsGaussianLaw beta sigma x)
      (gaussianEuclideanSmoothingKernel c v ∘ₘ proposal) ≤
      ENNReal.ofReal (c ^ 2 / (v : ℝ)) * klDiv proposal (conditionalGibbsGaussianLaw beta sigma x) := by
  obtain ⟨q, hq, hfst, hsnd, hcost⟩ :=
    conditionalGibbs_exists_coupling_cost_le_two_klDiv beta sigma x proposal
  let _ := hq
  have h := klDiv_gaussianEuclideanSmoothing_le_coupling c v hv proposal
    (conditionalGibbsGaussianLaw beta sigma x) q hfst hsnd
  have hc : ENNReal.ofReal (c ^ 2 / (2 * (v : ℝ))) * (∫⁻ p, edist p.1 p.2 ^ 2 ∂q) ≤
      ENNReal.ofReal (c ^ 2 / (2 * (v : ℝ))) *
        (2 * klDiv proposal (conditionalGibbsGaussianLaw beta sigma x)) := by gcongr
  refine (h.trans hc).trans_eq ?_
  have hec : ENNReal.ofReal (c ^ 2 / (2 * (v : ℝ))) * 2 =
      ENNReal.ofReal (c ^ 2 / (v : ℝ)) := by
    rw [← ENNReal.ofReal_ofNat 2]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ c ^ 2 / (2 * (v : ℝ)))]
    congr 1
    ring
  rw [← mul_assoc, hec]

theorem klDiv_compProd_same_left_eq_lintegral_ae {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace.CountableOrCountablyGenerated A B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ka kb : Kernel A B)
    [IsMarkovKernel ka] [IsMarkovKernel kb] (hac : ∀ᵐ i ∂μ, ka i ≪ kb i) :
    klDiv (μ ⊗ₘ ka) (μ ⊗ₘ kb) = ∫⁻ i, klDiv (ka i) (kb i) ∂μ := by
  have hjac : μ ⊗ₘ ka ≪ μ ⊗ₘ kb := Measure.AbsolutelyContinuous.compProd_right hac
  rw [klDiv_eq_lintegral_klFun_of_ac hjac]
  have hJoint : (fun p => ENNReal.ofReal (klFun ((μ ⊗ₘ ka).rnDeriv (μ ⊗ₘ kb) p).toReal))
      =ᵐ[μ ⊗ₘ kb] fun p => ENNReal.ofReal (klFun (ka.rnDeriv kb p.1 p.2).toReal) := by
    filter_upwards [rnDeriv_measure_compProd_right μ ka kb] with p hp
    rw [hp]
  rw [lintegral_congr_ae hJoint, Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hac] with i hi
  change (∫⁻ x, ENNReal.ofReal (klFun (ka.rnDeriv kb i x).toReal) ∂kb i) = klDiv (ka i) (kb i)
  rw [klDiv_eq_lintegral_klFun_of_ac hi]
  apply lintegral_congr_ae
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := ka) (η := kb) (a := i)] with x hx
  rw [hx]

def conditionalGibbsGaussianKernel (n : ℕ) (beta sigma : ℝ) :
    Kernel (Spin n) (EuclideanSpace ℝ (Fin n × Fin n)) where
  toFun x := conditionalGibbsGaussianLaw beta sigma x
  measurable' := measurable_of_countable _

instance conditionalGibbsGaussianKernel_isMarkov (n : ℕ) (beta sigma : ℝ) :
    IsMarkovKernel (conditionalGibbsGaussianKernel n beta sigma) := by
  constructor
  intro x
  exact conditionalGibbsGaussianLaw_isProbability beta sigma x

theorem conditionalGibbs_common_spin_reverse_smoothing_KL (n : ℕ) (beta sigma : ℝ)
    (spinLaw : Measure (Spin n)) [IsProbabilityMeasure spinLaw]
    (proposal : Kernel (Spin n) (EuclideanSpace ℝ (Fin n × Fin n))) [IsMarkovKernel proposal]
    (c : ℝ) (hc : c ≠ 0) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (spinLaw ⊗ₘ (gaussianEuclideanSmoothingKernel c v ∘ₖ conditionalGibbsGaussianKernel n beta sigma))
      (spinLaw ⊗ₘ (gaussianEuclideanSmoothingKernel c v ∘ₖ proposal)) ≤
      ENNReal.ofReal (c ^ 2 / (v : ℝ)) *
        klDiv (spinLaw ⊗ₘ proposal) (spinLaw ⊗ₘ conditionalGibbsGaussianKernel n beta sigma) := by
  let ref := conditionalGibbsGaussianKernel n beta sigma
  let κ := gaussianEuclideanSmoothingKernel (ι := Fin n × Fin n) c v
  let C := ENNReal.ofReal (c ^ 2 / (v : ℝ))
  have hpoint (x : Spin n) : klDiv ((κ ∘ₖ ref) x) ((κ ∘ₖ proposal) x) ≤
      C * klDiv (proposal x) (ref x) :=
    conditionalGibbs_reverse_smoothing_KL beta sigma x (proposal x) c v hv
  by_cases hD : klDiv (spinLaw ⊗ₘ proposal) (spinLaw ⊗ₘ ref) = ⊤
  · have hC : C ≠ 0 := by
      apply ENNReal.ofReal_ne_zero_iff.mpr
      exact div_pos (sq_pos_of_ne_zero hc) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
    change klDiv (spinLaw ⊗ₘ (κ ∘ₖ ref)) (spinLaw ⊗ₘ (κ ∘ₖ proposal)) ≤
      C * klDiv (spinLaw ⊗ₘ proposal) (spinLaw ⊗ₘ ref)
    simp [hD, hC]
  · have hac := (klDiv_ne_top_iff.mp hD).1.kernel_of_compProd
    have hchain := klDiv_compProd_same_left_eq_lintegral_ae spinLaw proposal ref hac
    have hfinite : ∀ᵐ x ∂spinLaw, klDiv (proposal x) (ref x) < ⊤ := by
      apply ae_lt_top (measurable_of_countable _)
      rwa [← hchain]
    have hac' : ∀ᵐ x ∂spinLaw, (κ ∘ₖ ref) x ≪ (κ ∘ₖ proposal) x := by
      filter_upwards [hfinite] with x hx
      apply (klDiv_ne_top_iff.mp ?_).1
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx.ne) (hpoint x)
    have hrev := klDiv_compProd_same_left_eq_lintegral_ae spinLaw (κ ∘ₖ ref) (κ ∘ₖ proposal) hac'
    change klDiv (spinLaw ⊗ₘ (κ ∘ₖ ref)) (spinLaw ⊗ₘ (κ ∘ₖ proposal)) ≤
      C * klDiv (spinLaw ⊗ₘ proposal) (spinLaw ⊗ₘ ref)
    rw [hrev, hchain, ← lintegral_const_mul C (measurable_of_countable _)]
    exact lintegral_mono hpoint

theorem conditionalGibbs_reverse_smoothing_KL_delta {n : ℕ} (beta sigma : ℝ) (x : Spin n)
    (proposal : Measure (EuclideanSpace ℝ (Fin n × Fin n))) [IsProbabilityMeasure proposal]
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ ≤ 1) :
    klDiv (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∘ₘ
      conditionalGibbsGaussianLaw beta sigma x)
      (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∘ₘ proposal) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) * klDiv proposal (conditionalGibbsGaussianLaw beta sigma x) := by
  have hb := conditionalGibbs_reverse_smoothing_KL beta sigma x proposal
    (Real.sqrt (1 - (δ : ℝ))) δ hδ
  refine hb.trans ?_
  have hc : ENNReal.ofReal ((Real.sqrt (1 - (δ : ℝ))) ^ 2 / (δ : ℝ)) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hδ1))]
    exact div_le_div_of_nonneg_right (sub_le_self _ δ.coe_nonneg) δ.coe_nonneg
  gcongr

theorem conditionalGibbs_common_spin_reverse_smoothing_KL_delta (n : ℕ) (beta sigma : ℝ)
    (spinLaw : Measure (Spin n)) [IsProbabilityMeasure spinLaw]
    (proposal : Kernel (Spin n) (EuclideanSpace ℝ (Fin n × Fin n))) [IsMarkovKernel proposal]
    (δ : ℝ≥0) (hδ : δ ≠ 0) (hδ1 : δ < 1) :
    klDiv (spinLaw ⊗ₘ (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∘ₖ
      conditionalGibbsGaussianKernel n beta sigma))
      (spinLaw ⊗ₘ (gaussianEuclideanSmoothingKernel (Real.sqrt (1 - (δ : ℝ))) δ ∘ₖ proposal)) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) *
        klDiv (spinLaw ⊗ₘ proposal) (spinLaw ⊗ₘ conditionalGibbsGaussianKernel n beta sigma) := by
  have hc0 : Real.sqrt (1 - (δ : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr (by exact_mod_cast hδ1))).ne'
  have hb := conditionalGibbs_common_spin_reverse_smoothing_KL n beta sigma spinLaw proposal
    (Real.sqrt (1 - (δ : ℝ))) hc0 δ hδ
  refine hb.trans ?_
  have hc : ENNReal.ofReal ((Real.sqrt (1 - (δ : ℝ))) ^ 2 / (δ : ℝ)) ≤
      ENNReal.ofReal (1 / (δ : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [Real.sq_sqrt (sub_nonneg.mpr (by exact_mod_cast hδ1.le))]
    exact div_le_div_of_nonneg_right (sub_le_self _ δ.coe_nonneg) δ.coe_nonneg
  gcongr

end SKConstants
