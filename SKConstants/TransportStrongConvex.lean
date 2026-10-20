module

public import SKConstants.TransportPrekopaLeindler
public import SKConstants.TransportHopfCoupling

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set Filter Real
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace SKConstants.Transport
open WeakHessianTransport
set_option backward.isDefEq.respectTransparency false

def expPotentialLaw {ι : Type*} [Fintype ι] (U : EuclideanSpace ℝ ι → ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x)))

lemma bounded_exp_integrable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (f : X →ᵇ ℝ) (t : ℝ) : Integrable (fun x => Real.exp (t * f x)) ν := by
  apply (integrable_const (Real.exp (|t| * ‖f‖))).mono' (by fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * f x)).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (abs_nonneg t))

lemma bounded_integrableExpSet {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (f : X →ᵇ ℝ) : integrableExpSet f ν = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
  exact bounded_exp_integrable ν f t

def boundedHopf {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X →ᵇ ℝ) : X →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (hopfLax f 1)
    (hopfLax_continuous f.continuous
      (fun x => (abs_le.mp (f.norm_coe_le_norm x)).1)
      (fun x => (abs_le.mp (f.norm_coe_le_norm x)).2)
      (by linarith [norm_nonneg f]) (by norm_num))
    ‖f‖ (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨lower_le_hopfLax
        (fun y => (abs_le.mp (f.norm_coe_le_norm y)).1) (by norm_num) x,
        (hopfLax_le_self (fun y => (abs_le.mp (f.norm_coe_le_norm y)).1)
          (by norm_num) x).trans (abs_le.mp (f.norm_coe_le_norm x)).2⟩)

@[simp] lemma boundedHopf_apply {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : X →ᵇ ℝ) (x : X) : boundedHopf f x = hopfLax f 1 x := rfl

lemma expPotential_integral {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hU : Measurable U) (F : EuclideanSpace ℝ ι → ℝ) :
    (∫ x, F x ∂expPotentialLaw U) =
      ∫ x, Real.exp (-U x) * F x ∂volume := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-U x))) := by fun_prop
  rw [expPotentialLaw, integral_withDensity_eq_integral_toReal_smul
    hm (by filter_upwards with x; simp)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

lemma expPotential_integrable {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hU : Measurable U) (F : EuclideanSpace ℝ ι → ℝ) :
    Integrable F (expPotentialLaw U) ↔
      Integrable (fun x => Real.exp (-U x) * F x) volume := by
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-U x))) := by fun_prop
  simpa only [expPotentialLaw, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    using (integrable_withDensity_iff_integrable_smul₀'
      hm.aemeasurable
      (by filter_upwards with x; simp) (g := F) (μ := volume))

lemma strongConvex_hopf_PL {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hU : StrongConvexOn univ 1 U)
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (x y : EuclideanSpace ℝ ι) :
    Real.exp (-U x + (1 - t) * boundedHopf f x) ^ t *
      Real.exp (-U y - t * f y) ^ (1 - t) ≤
        Real.exp (-U (t • x + (1 - t) • y)) := by
  have hcv := hU.2 (mem_univ x) (mem_univ y) ht0.le (sub_pos.mpr ht1).le
    (show t + (1 - t) = 1 by ring)
  have hq := hopfLax_le_objective
    (fun z => (abs_le.mp (f.norm_coe_le_norm z)).1) (by norm_num : (0 : ℝ) < 1) x y
  rw [hopfObjective, mul_one, ← boundedHopf_apply] at hq
  rw [dist_eq_norm] at hq
  simp only [smul_eq_mul] at hcv
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
    Real.log_exp, Real.log_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ht0.le (sub_pos.mpr ht1).le,
    mul_le_mul_of_nonneg_left hq (mul_nonneg ht0.le (sub_pos.mpr ht1).le)]

lemma strongConvex_hopf_mgf_interpolation {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hUm : Measurable U)
    (hU : StrongConvexOn univ 1 U) [IsProbabilityMeasure (expPotentialLaw U)]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    mgf (boundedHopf f) (expPotentialLaw U) (1 - t) ^ t *
      mgf f (expPotentialLaw U) (-t) ^ (1 - t) ≤ 1 := by
  have hFInt := (expPotential_integrable U hUm _).mp
    (bounded_exp_integrable (expPotentialLaw U) (boundedHopf f) (1 - t))
  have hGInt := (expPotential_integrable U hUm _).mp
    (bounded_exp_integrable (expPotentialLaw U) f (-t))
  have hDInt := (expPotential_integrable U hUm (fun _ => 1)).mp (integrable_const 1)
  have hf : Integrable (fun x => Real.exp (-U x + (1 - t) * boundedHopf f x)) := by
    simpa only [Real.exp_add] using hFInt
  have hg : Integrable (fun x => Real.exp (-U x - t * f x)) := by
    simpa only [sub_eq_add_neg, neg_mul, Real.exp_add] using hGInt
  have hh : Integrable (fun x => Real.exp (-U x)) := by simpa using hDInt
  have hp := TransportPrekopa.prekopaLeindler_euclidean_integral
    (fun x => (Real.exp_pos _).le) (fun x => (Real.exp_pos _).le)
    (fun x => (Real.exp_pos _).le)
    (by fun_prop) (by fun_prop) (by fun_prop) hf hg hh ht0 ht1
    (strongConvex_hopf_PL U hU f ht0 ht1)
  have hF : (∫ x, Real.exp (-U x + (1 - t) * boundedHopf f x)) =
      mgf (boundedHopf f) (expPotentialLaw U) (1 - t) := by
    rw [mgf, expPotential_integral U hUm]
    simp only [Real.exp_add]
  have hG : (∫ x, Real.exp (-U x - t * f x)) =
      mgf f (expPotentialLaw U) (-t) := by
    rw [mgf, expPotential_integral U hUm]
    simp only [sub_eq_add_neg, neg_mul, Real.exp_add]
  have hD : (∫ x, Real.exp (-U x)) = 1 := by
    have h := expPotential_integral U hUm (fun _ => 1)
    simpa using h.symm
  rwa [hF, hG, hD] at hp

theorem strongConvex_hopf_log_mgf_le {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hUm : Measurable U)
    (hU : StrongConvexOn univ 1 U) [IsProbabilityMeasure (expPotentialLaw U)]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) :
    Real.log (mgf (boundedHopf f) (expPotentialLaw U) 1) ≤
      ∫ x, f x ∂expPotentialLaw U := by
  let ν := expPotentialLaw U
  let Q := boundedHopf f
  let H : ℝ → ℝ := fun t => t * Real.log (mgf Q ν (1 - t)) +
    (1 - t) * Real.log (mgf f ν (-t))
  have hQset : integrableExpSet Q ν = univ := bounded_integrableExpSet ν Q
  have hfset : integrableExpSet f ν = univ := bounded_integrableExpSet ν f
  have hAm : HasDerivAt (fun t => mgf Q ν (1 - t))
      (-(∫ x, Q x * Real.exp (Q x) ∂ν)) 0 := by
    convert (hasDerivAt_mgf (X := Q) (μ := ν) (t := 1)
      (by rw [hQset]; simp)).comp_of_eq 0
        ((hasDerivAt_const 0 (1 : ℝ)).sub (hasDerivAt_id 0)) (by simp) using 1 <;>
      simp [Function.comp_def, Pi.sub_apply]
  have hA := hAm.log (by simpa using (mgf_pos (bounded_exp_integrable ν Q 1)).ne')
  have hBm : HasDerivAt (fun t => mgf f ν (-t)) (-(∫ x, f x ∂ν)) 0 := by
    convert (hasDerivAt_mgf (X := f) (μ := ν) (t := 0)
      (by rw [hfset]; simp)).comp_of_eq 0 (hasDerivAt_id 0).neg (by simp) using 1 <;>
      simp [Function.comp_def]
  have hB : HasDerivAt (fun t => Real.log (mgf f ν (-t)))
      (-(∫ x, f x ∂ν)) 0 := by
    simpa using hBm.log (by simp)
  have hD : HasDerivAt H
      (Real.log (mgf Q ν 1) - ∫ x, f x ∂ν) 0 := by
    convert ((hasDerivAt_id 0).mul hA).add
      (((hasDerivAt_const 0 (1 : ℝ)).sub (hasDerivAt_id 0)).mul hB) using 1
    · funext t; rfl
    · simp [sub_eq_add_neg]
  have hH0 : H 0 = 0 := by simp [H]
  have hH (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : H t ≤ 0 := by
    have hp := strongConvex_hopf_mgf_interpolation U hUm hU f ht0 ht1
    have hAp := mgf_pos (bounded_exp_integrable ν Q (1 - t))
    have hBp := mgf_pos (bounded_exp_integrable ν f (-t))
    have hh : Real.exp (H t) ≤ Real.exp 0 := by
      change mgf Q ν (1 - t) ^ t * mgf f ν (-t) ^ (1 - t) ≤ 1 at hp
      rw [Real.rpow_def_of_pos hAp, Real.rpow_def_of_pos hBp] at hp
      simpa only [H, Real.exp_add, Real.exp_zero,
        mul_comm (Real.log (mgf Q ν (1 - t))) t,
        mul_comm (Real.log (mgf f ν (-t))) (1 - t)] using hp
    exact Real.exp_le_exp.mp hh
  have hn : Real.log (mgf Q ν 1) - ∫ x, f x ∂ν ≤ 0 := by
    apply le_of_tendsto hD.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht0 ht1
    change 0 < t at ht0
    simpa only [smul_eq_mul, zero_add, hH0, sub_zero] using
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le) (hH t ht0 ht1)
  exact sub_nonpos.mp hn

end SKConstants.Transport
