module

public import SKConstants.PredictableGaussianSums
public import SKConstants.ScalarProcessPosteriorIncrement
public import SKConstants.Completion.LFine.IndependentFourth
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9b
open LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem integrable_gaussian_affine_fourth (v : ℝ≥0) (a b : ℝ) :
    Integrable (fun x : ℝ => (a+b*x)^4) (gaussianReal 0 v) :=
  integrable_fourth_of_memLp _ _ ((memLp_const a).add ((memLp_id_gaussianReal 4).const_mul b))

theorem integral_gaussian_affine_fourth (v : ℝ≥0) (a b : ℝ) :
    (∫ x : ℝ, (a+b*x)^4 ∂gaussianReal 0 v) = a^4+6*(v : ℝ)*a^2*b^2+3*(v : ℝ)^2*b^4 := by
  have hmap : (gaussianReal 0 v).map (fun x : ℝ => a+b*x) =
      gaussianReal a (NNReal.mk (b^2) (sq_nonneg b)*v) := by
    rw [show (fun x : ℝ => a+b*x) = (fun x => a+x) ∘ (fun x => b*x) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    simp only [mul_zero, zero_add]
  calc
    _ = ∫ x : ℝ, x^4 ∂(gaussianReal 0 v).map (fun x : ℝ => a+b*x) :=
      (integral_map (by fun_prop) (by fun_prop)).symm
    _ = _ := by
      rw [hmap, gaussianReal_integral_fourth]
      simp only [NNReal.coe_mul, NNReal.coe_mk]
      ring

theorem independent_gaussian_step_fourth (P : Measure Ω) [IsProbabilityMeasure P]
    (v : ℝ≥0) (X A H : Ω → ℝ)
    (hstate : AEMeasurable (fun w => (A w,H w)) P)
    (hX : HasLaw X (gaussianReal 0 v) P)
    (hind : IndepFun (fun w => (A w,H w)) X P)
    (hA : Integrable (fun w => A w^4) P)
    (hAH : Integrable (fun w => A w^2*H w^2) P)
    (hH : Integrable (fun w => H w^4) P) :
    Integrable (fun w => (A w+H w*X w)^4) P ∧
      (∫ w, (A w+H w*X w)^4 ∂P) =
        (∫ w, A w^4 ∂P) + 6*(v : ℝ)*(∫ w, A w^2*H w^2 ∂P) +
          3*(v : ℝ)^2*(∫ w, H w^4 ∂P) := by
  let S := fun w => (A w,H w)
  let μ := P.map S
  have : IsFiniteMeasure μ := P.isFiniteMeasure_map S
  let F := fun z : (ℝ × ℝ) × ℝ => (z.1.1+z.1.2*z.2)^4
  have hm : Measurable F := by fun_prop
  have hAm : Integrable (fun z : ℝ × ℝ => z.1^4) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hA
  have hAHm : Integrable (fun z : ℝ × ℝ => z.1^2*z.2^2) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hAH
  have hHm : Integrable (fun z : ℝ × ℝ => z.2^4) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hH
  have hp : Integrable F (μ.prod (gaussianReal 0 v)) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ fun z => integrable_gaussian_affine_fourth v z.1 z.2
    · convert (hAm.add (hAHm.const_mul (6*(v : ℝ)))).add
        (hHm.const_mul (3*(v : ℝ)^2)) using 1
      funext z
      simp only [F, Real.norm_eq_abs, Pi.add_apply]
      simp only [show ∀ x : ℝ, |x^4| = x^4 from fun x => abs_of_nonneg (by positivity)]
      rw [integral_gaussian_affine_fourth]
      ring
  have hlaw : HasLaw (fun w => (S w,X w)) (μ.prod (gaussianReal 0 v)) P :=
    hind.hasLaw_prod ⟨hstate,rfl⟩ hX
  refine ⟨hlaw.integrable_fun_comp hp, ?_⟩
  have he := hlaw.integral_comp hp.aestronglyMeasurable
  change (∫ w, F (S w,X w) ∂P) = ∫ z, F z ∂μ.prod (gaussianReal 0 v) at he
  rw [he, integral_prod _ hp]
  simp only [F, integral_gaussian_affine_fourth]
  have hfun : (fun z : ℝ × ℝ => z.1^4+6*(v : ℝ)*z.1^2*z.2^2+3*(v : ℝ)^2*z.2^4) =
      (fun z => z.1^4+(6*(v : ℝ))*(z.1^2*z.2^2)+(3*(v : ℝ)^2)*z.2^4) := by
    funext z
    ring
  rw [hfun, integral_add
      (f := fun z : ℝ × ℝ => z.1^4+(6*(v : ℝ))*(z.1^2*z.2^2))
      (g := fun z => (3*(v : ℝ)^2)*z.2^4)
      (hAm.add (hAHm.const_mul _)) (hHm.const_mul _),
    integral_add (f := fun z : ℝ × ℝ => z.1^4)
      (g := fun z => (6*(v : ℝ))*(z.1^2*z.2^2)) hAm (hAHm.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_map hstate (by fun_prop), integral_map hstate (by fun_prop),
    integral_map hstate (by fun_prop)]

theorem predictableGaussianSum_fourth_le (P : Measure Ω) [IsProbabilityMeasure P]
    (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hH : ∀ k, AEMeasurable (H k) P)
    (hcap : ∀ k, ∀ᵐ w ∂P, |H k w| ≤ 1)
    (hind : ∀ k, IndepFun
      (fun w => (predictableGaussianSum X H k w,H k w,predictableGaussianVariation v H k w))
        (X k) P) (n : ℕ) :
    Integrable (fun w => predictableGaussianSum X H n w^4) P ∧
      (∫ w, predictableGaussianSum X H n w^4 ∂P) ≤
        6*(∑ k ∈ Finset.range n, (v k : ℝ)) *
          (∫ w, predictableGaussianSum X H n w^2 ∂P) := by
  have hH2 (k) : Integrable (fun w => H k w^2) P :=
    Integrable.of_bound ((hH k).pow_const 2).aestronglyMeasurable 1
      ((hcap k).mono fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs (H k w), abs_nonneg (H k w)])
  have hH4 (k) : Integrable (fun w => H k w^4) P :=
    integrable_fourth_of_memLp P (H k)
      (MemLp.of_bound (hH k).aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hcap k))
  have hS2 (k) := (predictableGaussianSum_L2_isometry P X H v hX hH hH2 hind k).1
  induction n with
  | zero => simp [predictableGaussianSum]
  | succ n ih =>
    let A := predictableGaussianSum X H n
    have hm := (aemeasurable_predictableGaussianSum P X H (fun k => (hX k).aemeasurable) hH n).prodMk (hH n)
    have hi : IndepFun (fun w => (A w,H n w)) (X n) P :=
      (hind n).comp (show Measurable (fun z : ℝ × ℝ × ℝ => (z.1,z.2.1)) from by fun_prop) measurable_id
    have hAH : Integrable (fun w => A w^2*H n w^2) P := by
      apply (hS2 n).mul_bdd ((hH n).pow_const 2).aestronglyMeasurable (c := 1)
      filter_upwards [hcap n] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (H n w), abs_nonneg (H n w)]
    have hfour := independent_gaussian_step_fourth P (v n) (X n) A (H n) hm (hX n) hi ih.1 hAH (hH4 n)
    have htwo := independent_gaussian_step_square P (v n) (X n) A (H n) hm (hX n) hi (hS2 n) (hH2 n)
    refine ⟨hfour.1, ?_⟩
    change (∫ w, (A w+H n w*X n w)^4 ∂P) ≤ _
    rw [hfour.2, Finset.sum_range_succ]
    change _ ≤ 6*((∑ k ∈ Finset.range n, (v k : ℝ))+(v n : ℝ))*
      (∫ w, (A w+H n w*X n w)^2 ∂P)
    rw [htwo.2]
    have hAHle : (∫ w, A w^2*H n w^2 ∂P) ≤ ∫ w, A w^2 ∂P := by
      apply integral_mono_ae hAH (hS2 n)
      filter_upwards [hcap n] with w hw
      have hh : H n w^2 ≤ 1 := by nlinarith [sq_abs (H n w), abs_nonneg (H n w)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg (A w))
    have hHle : (∫ w, H n w^4 ∂P) ≤ ∫ w, H n w^2 ∂P := by
      apply integral_mono_ae (hH4 n) (hH2 n)
      filter_upwards [hcap n] with w hw
      have hh : H n w^2 ≤ 1 := by nlinarith [sq_abs (H n w), abs_nonneg (H n w)]
      nlinarith [sq_nonneg (H n w)]
    have hD : 0 ≤ ∑ k ∈ Finset.range n, (v k : ℝ) :=
      Finset.sum_nonneg fun k _ => (v k).coe_nonneg
    have hHpos : 0 ≤ ∫ w, H n w^2 ∂P := integral_nonneg fun _ => sq_nonneg _
    calc
      _ ≤ 6*(∑ k ∈ Finset.range n, (v k : ℝ))*(∫ w, A w^2 ∂P) +
          6*(v n : ℝ)*(∫ w, A w^2 ∂P) + 3*(v n : ℝ)^2*(∫ w, H n w^2 ∂P) :=
        add_le_add (add_le_add ih.2
          (mul_le_mul_of_nonneg_left hAHle (by positivity)))
          (mul_le_mul_of_nonneg_left hHle (by positivity))
      _ ≤ _ := by
        nlinarith [mul_nonneg hD (mul_nonneg (v n).coe_nonneg hHpos),
          mul_nonneg (sq_nonneg (v n : ℝ)) hHpos]

end SKConstants.Completion.N9b
