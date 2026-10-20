module

public import SKConstants.TransportStrongConvex
public import SKConstants.ScalarProcessRowMGFLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Transport

theorem strongConvex_bounded_lipschitz_exp_le {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hUm : Measurable U)
    (hU : StrongConvexOn univ 1 U) [IsProbabilityMeasure (expPotentialLaw U)]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    (∫ x, Real.exp (f x) ∂expPotentialLaw U) ≤
      Real.exp ((∫ x, f x ∂expPotentialLaw U) + (L : ℝ)^2 / 2) := by
  let ν := expPotentialLaw U
  have hq := strongConvex_hopf_log_mgf_le U hUm hU f
  have hp : 0 < mgf (boundedHopf f) ν 1 := by
    unfold mgf
    apply integral_pos_iff_support_of_nonneg
      (fun x => (Real.exp_pos _).le) (bounded_exp_integrable ν (boundedHopf f) 1) |>.mpr
    have hs : Function.support (fun x => Real.exp (1 * boundedHopf f x)) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (Real.exp_pos _).ne'
    rw [hs, measure_univ]
    norm_num
  have hqe : mgf (boundedHopf f) ν 1 ≤ Real.exp (∫ x, f x ∂ν) := by
    have h := Real.exp_le_exp.mpr hq
    change Real.exp (Real.log (mgf (boundedHopf f) ν 1)) ≤ _ at h
    rwa [Real.exp_log hp] at h
  have hpoint (x) : Real.exp (f x - (L : ℝ)^2 / 2) ≤
      Real.exp (boundedHopf f x) := by
    apply Real.exp_le_exp.mpr
    simpa only [boundedHopf_apply, one_mul] using
      WeakHessianTransport.hopfLax_ge_lipschitz hf (by norm_num : (0 : ℝ) < 1) x
  have hi : Integrable (fun x => Real.exp (f x - (L : ℝ)^2 / 2)) ν := by
    simp_rw [Real.exp_sub]
    exact (bounded_exp_integrable ν f 1 |>.congr (by simp)).div_const _
  have h := integral_mono hi (bounded_exp_integrable ν (boundedHopf f) 1 |>.congr (by simp)) hpoint
  simp_rw [Real.exp_sub] at h
  rw [integral_div] at h
  have hle : (∫ x, Real.exp (f x) ∂ν) / Real.exp ((L : ℝ)^2 / 2) ≤
      Real.exp (∫ x, f x ∂ν) := h.trans (by simpa only [mgf, one_mul] using hqe)
  rw [div_le_iff₀ (Real.exp_pos _)] at hle
  simpa only [Real.exp_add] using hle

theorem strongConvex_bounded_lipschitz_hasSubgaussianMGF {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hUm : Measurable U)
    (hU : StrongConvexOn univ 1 U) [IsProbabilityMeasure (expPotentialLaw U)]
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂expPotentialLaw U)
      (L^2) (expPotentialLaw U) := by
  let ν := expPotentialLaw U
  have hi (t : ℝ) : Integrable
      (fun x => Real.exp (t * (f x - ∫ y, f y ∂ν))) ν := by
    simp_rw [mul_sub, Real.exp_sub]
    exact (bounded_exp_integrable ν f t).div_const _
  refine ⟨hi, fun t => ?_⟩
  let g : EuclideanSpace ℝ ι →ᵇ ℝ := t • f
  have hg : LipschitzWith (‖t‖₊ * L) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (t * f x) (t * f y) ≤ _
    simp only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
      Real.norm_eq_abs]
    have h := hf.dist_le_mul x y
    rw [Real.dist_eq] at h
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (abs_nonneg t)
  have hb := strongConvex_bounded_lipschitz_exp_le U hUm hU g hg
  have hmean : (∫ x, g x ∂ν) = t * ∫ x, f x ∂ν := by
    exact integral_const_mul _ _
  rw [hmean] at hb
  change (∫ x, Real.exp (t * (f x - ∫ y, f y ∂ν)) ∂ν) ≤ _
  simp_rw [mul_sub, Real.exp_sub]
  rw [integral_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  calc
    _ ≤ Real.exp (t * (∫ x, f x ∂ν) + (‖t‖₊ * L : ℝ≥0)^2 / 2) := hb
    _ = Real.exp ((L^2 : ℝ≥0) * t^2 / 2) * Real.exp (t * ∫ x, f x ∂ν) := by
      rw [← Real.exp_add]
      congr 1
      simp only [NNReal.coe_pow, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
      nlinarith [sq_abs t]

def concentrationClip (n : ℕ) (x : ℝ) : ℝ := max (-(n : ℝ)) (min (n : ℝ) x)

lemma concentrationClip_abs_le (n : ℕ) (x : ℝ) :
    |concentrationClip n x| ≤ |x| := by
  unfold concentrationClip
  rw [abs_le]
  constructor
  · exact le_max_of_le_right (le_min (by linarith [abs_nonneg x, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]) (neg_abs_le x))
  · apply max_le
    · exact (neg_nonpos.mpr ((Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)))).trans (abs_nonneg x)
    · exact (min_le_right _ _).trans (le_abs_self x)

lemma concentrationClip_abs_le_nat (n : ℕ) (x : ℝ) :
    |concentrationClip n x| ≤ (n : ℝ) := by
  unfold concentrationClip
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] : -(n : ℝ) ≤ (n : ℝ)) (min_le_left _ _)⟩

lemma concentrationClip_tendsto (x : ℝ) :
    Tendsto (fun n => concentrationClip n x) atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have h : |x| ≤ (n : ℝ) := hN.le.trans (Nat.cast_le.mpr hn)
  simp only [concentrationClip, min_eq_right (le_abs_self x |>.trans h),
    max_eq_right ((neg_le_neg h).trans (neg_abs_le x))]

theorem strongConvex_lipschitz_hasSubgaussianMGF {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hUm : Measurable U)
    (hU : StrongConvexOn univ 1 U) [IsProbabilityMeasure (expPotentialLaw U)]
    {f : EuclideanSpace ℝ ι → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hfi : Integrable f (expPotentialLaw U)) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂expPotentialLaw U)
      (L^2) (expPotentialLaw U) := by
  let ν := expPotentialLaw U
  let fc (n : ℕ) : EuclideanSpace ℝ ι →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => concentrationClip n (f x))
      ((continuous_const.max (continuous_const.min hf.continuous)))
      (n : ℝ) (fun x => by simpa only [Real.norm_eq_abs] using concentrationClip_abs_le_nat n (f x))
  have hfc (n) : LipschitzWith L (fc n) := (hf.const_min (n : ℝ)).const_max (-(n : ℝ))
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => fc n x) atTop (𝓝 (f x)) :=
    ae_of_all _ (fun x => concentrationClip_tendsto (f x))
  have hm : Tendsto (fun n => ∫ x, fc n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (fc n).continuous.aestronglyMeasurable) hfi.abs
      (fun n => ae_of_all _ (fun x => by
        change |concentrationClip n (f x)| ≤ |f x|
        exact concentrationClip_abs_le n (f x))) hlim
  apply SKConstants.hasSubgaussianMGF_of_tendstoInMeasure
    (fun n => strongConvex_bounded_lipschitz_hasSubgaussianMGF U hUm hU (fc n) (hfc n))
    (tendstoInMeasure_of_tendsto_ae
      (fun n => ((fc n).continuous.sub continuous_const).aestronglyMeasurable) ?_)
    tendsto_const_nhds
  filter_upwards [hlim] with x hx
  exact hx.sub hm

end SKConstants.Transport
