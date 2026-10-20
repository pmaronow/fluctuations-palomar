module

public import SKConstants.Completion.N9Z2.Comparison
public import SKConstants.MeshResidualGaussianSquare
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N9Z2
open SKConstantsOAI.ZeroTemperatureSK M1 LFine N9 N9c

theorem integral_id_mul_nonneg_of_monotone (μ : Measure ℝ)
    (hxi : Integrable (fun x : ℝ => x) μ) (hcenter : (∫ x : ℝ, x ∂μ) = 0)
    (g : ℝ → ℝ) (hgi : Integrable (fun x => x*g x) μ) (hg : Monotone g) :
    0 ≤ ∫ x : ℝ, x*g x ∂μ := by
  have hp (x : ℝ) : 0 ≤ x*(g x-g 0) := by
    rcases le_total 0 x with hx | hx
    · exact mul_nonneg hx (sub_nonneg.mpr (hg hx))
    · exact mul_nonneg_of_nonpos_of_nonpos hx (sub_nonpos.mpr (hg hx))
  have h := MeasureTheory.integral_nonneg (f := fun x : ℝ => x*(g x-g 0)) hp (μ := μ)
  have he : (fun x => x*(g x-g 0)) = (fun x => x*g x-x*g 0) := by
    funext x
    ring
  rw [he, integral_sub hgi (hxi.mul_const _), integral_mul_const, hcenter, zero_mul,
    sub_zero] at h
  exact h

theorem integral_id_mul_le_of_monotone_difference (μ : Measure ℝ)
    (hxi : Integrable (fun x : ℝ => x) μ) (hcenter : (∫ x : ℝ, x ∂μ) = 0)
    (hxsq : Integrable (fun x : ℝ => x^2) μ)
    (g : ℝ → ℝ) (hgi : Integrable (fun x => x*g x) μ)
    (L : ℝ) (hg : Monotone (fun x => L*x-g x)) :
    (∫ x : ℝ, x*g x ∂μ) ≤ L*(∫ x : ℝ, x^2 ∂μ) := by
  have he : (fun x => x*(L*x-g x)) = (fun x => L*x^2-x*g x) := by
    funext x
    ring
  have hi : Integrable (fun x => x*(L*x-g x)) μ := by
    rw [he]
    exact (hxsq.const_mul L).sub hgi
  have h := integral_id_mul_nonneg_of_monotone μ hxi hcenter _ hi hg
  rw [he, integral_sub (hxsq.const_mul L) hgi, integral_const_mul] at h
  linarith

theorem monotone_difference_of_lipschitz {L : ℝ≥0} {g : ℝ → ℝ}
    (hg : LipschitzWith L g) : Monotone (fun x => (L : ℝ)*x-g x) := by
  intro x y hxy
  have hd : |g y-g x| ≤ (L : ℝ)*(y-x) := by
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] using hg.dist_le_mul y x
  have hle := (le_abs_self (g y-g x)).trans hd
  linarith

def freshEndpointMean {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0)
    (B D : ScalarContinuousPath a) (x : ℝ) : ℝ :=
  ∫ s, (if freshRowSign W β hβ a h f B D (x,s) then (1 : ℝ) else -1)
    ∂freshRowSeedLaw W h f

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_freshEndpointMean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (B D : ScalarContinuousPath a) :
    Measurable (freshEndpointMean W β hβ a h f B D) := by
  exact (((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
    (measurable_freshRowSign W β hβ a h f B D)).stronglyMeasurable.integral_prod_right').measurable

theorem freshRowSign_seed_integrable (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (B D : ScalarContinuousPath a) (x : ℝ) :
    Integrable (fun s => if freshRowSign W β hβ a h f B D (x,s) then (1 : ℝ) else -1)
      (freshRowSeedLaw W h f) := by
  apply Integrable.of_bound
    (((measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      ((measurable_freshRowSign W β hβ a h f B D).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable) 1
  exact ae_of_all _ fun s => by
    change ‖if freshRowSign W β hβ a h f B D (x,s) then (1 : ℝ) else -1‖ ≤ 1
    split <;> norm_num

theorem freshEndpointMean_monotone (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (B D : ScalarContinuousPath a) :
    Monotone (freshEndpointMean W β hβ a h f B D) := by
  intro x y hxy
  exact integral_mono (freshRowSign_seed_integrable W β hβ a h f B D x)
    (freshRowSign_seed_integrable W β hβ a h f B D y)
    (fun s => freshRowSign_endpoint_monotone W β hβ a h f B D s hxy)

theorem freshEndpointMean_abs_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (B D : ScalarContinuousPath a) (x : ℝ) :
    |freshEndpointMean W β hβ a h f B D x| ≤ 1 := by
  change ‖∫ s, (if freshRowSign W β hβ a h f B D (x,s) then (1 : ℝ) else -1)
    ∂freshRowSeedLaw W h f‖ ≤ 1
  apply le_trans (norm_integral_le_integral_norm _)
  simp only [Real.norm_eq_abs]
  have he : (fun s => |if freshRowSign W β hβ a h f B D (x,s) then (1 : ℝ) else -1|) =
      fun _ : FreshRowSeed h f => (1 : ℝ) := by
    funext s
    split <;> norm_num
  rw [he]
  simp

theorem freshRowMixedMean_eq_endpoint_integral (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a) :
    freshRowMixedMean W β hβ a h f (B,D) =
      ∫ x : ℝ, x*freshEndpointMean W β hβ a h f B D x ∂gaussianReal 0 1 := by
  have he : Integrable (fun z : ℝ × FreshRowSeed h f => z.1)
      ((gaussianReal 0 1).prod (freshRowSeedLaw W h f)) :=
    ((memLp_id_gaussianReal 1).integrable (by norm_num)).comp_fst _
  have hs : Measurable (fun z : ℝ × FreshRowSeed h f =>
      if freshRowSign W β hβ a h f B D z then (1 : ℝ) else -1) :=
    (measurable_of_finite (fun b : Bool => if b then (1 : ℝ) else -1)).comp
      (measurable_freshRowSign W β hβ a h f B D)
  have hi := he.bdd_mul hs.aestronglyMeasurable (c := 1)
    (ae_of_all _ fun z => by split <;> norm_num)
  rw [freshRowMixedMean, integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (∫ s, (if freshRowSign W β hβ a h f B D (x,s) then (1 : ℝ) else -1)*x
      ∂freshRowSeedLaw W h f) = x*freshEndpointMean W β hβ a h f B D x
    rw [integral_mul_const]
    exact mul_comm _ _

theorem freshEndpointMean_mul_integrable (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a) :
    Integrable (fun x : ℝ => x*freshEndpointMean W β hβ a h f B D x) (gaussianReal 0 1) := by
  apply ((memLp_id_gaussianReal 1).integrable (by norm_num)).mul_bdd
    (measurable_freshEndpointMean W β hβ a h f B D).aestronglyMeasurable (c := 1)
  exact ae_of_all _ fun x => freshEndpointMean_abs_le_one W β hβ a h f B D x

theorem freshRowMixedMean_nonneg (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (B D : ScalarContinuousPath a) :
    0 ≤ freshRowMixedMean W β hβ a h f (B,D) := by
  rw [freshRowMixedMean_eq_endpoint_integral]
  exact integral_id_mul_nonneg_of_monotone _
    ((memLp_id_gaussianReal 1).integrable (by norm_num)) (by simp) _
    (freshEndpointMean_mul_integrable W β hβ a h f B D)
    (freshEndpointMean_monotone W β hβ a h f B D)

theorem freshRowMixedMean_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (B D : ScalarContinuousPath a) :
    freshRowMixedMean W β hβ a h f (B,D) ≤ 1 := by
  rw [freshRowMixedMean_eq_endpoint_integral]
  have hi : Integrable (fun x : ℝ => (x^2+1)/2) (gaussianReal 0 1) :=
    (((memLp_id_gaussianReal 2).integrable_sq).add (integrable_const 1)).div_const 2
  have hpoint (x : ℝ) : x*freshEndpointMean W β hβ a h f B D x ≤ (x^2+1)/2 := by
    have hp : x*freshEndpointMean W β hβ a h f B D x ≤ |x| := by
      calc
        _ ≤ |x*freshEndpointMean W β hβ a h f B D x| := le_abs_self _
        _ = |x| * |freshEndpointMean W β hβ a h f B D x| := abs_mul _ _
        _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left
          (freshEndpointMean_abs_le_one W β hβ a h f B D x) (abs_nonneg x)
        _ = |x| := mul_one _
    nlinarith [sq_nonneg (|x|-1), sq_abs x]
  have hle := integral_mono (freshEndpointMean_mul_integrable W β hβ a h f B D) hi hpoint
  have he : (∫ x : ℝ, (x^2+1)/2 ∂gaussianReal 0 1) = 1 := by
    rw [integral_div, integral_add (f := fun x : ℝ => x^2) (g := fun _ => (1 : ℝ))
      (memLp_id_gaussianReal 2).integrable_sq (integrable_const 1),
      integral_gaussian_square]
    norm_num
  exact hle.trans_eq he

theorem freshRowMixedMean_le_of_lipschitz (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (a h f : ℝ≥0) (B D : ScalarContinuousPath a)
    (L : ℝ≥0) (hL : LipschitzWith L (freshEndpointMean W β hβ a h f B D)) :
    freshRowMixedMean W β hβ a h f (B,D) ≤ (L : ℝ) := by
  rw [freshRowMixedMean_eq_endpoint_integral]
  have hh := integral_id_mul_le_of_monotone_difference (gaussianReal 0 1)
    ((memLp_id_gaussianReal 1).integrable (by norm_num)) (by simp)
    ((memLp_id_gaussianReal 2).integrable_sq) _
    (freshEndpointMean_mul_integrable W β hβ a h f B D) (L : ℝ)
    (monotone_difference_of_lipschitz hL)
  simpa only [integral_gaussian_square, NNReal.coe_one, mul_one] using hh

end SKConstants.Completion.N9Z2
