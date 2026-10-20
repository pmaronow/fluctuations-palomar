module

public import SKConstants.Completion.X32B.Quadrature

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X32B
open SKConstantsOAI.ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

theorem weighted_square_displacement_sq_le (c x d H : ℝ) (hc : |c| ≤ 1)
    (hd : |d| ≤ H) :
    (c * ((x + d) ^ 2 - x ^ 2)) ^ 2 ≤ 8 * H ^ 2 * x ^ 2 + 2 * H ^ 4 := by
  have hc2 : c ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one c).mpr hc
  have hd2 : d ^ 2 ≤ H ^ 2 := by
    have hH : 0 ≤ H := (abs_nonneg d).trans hd
    nlinarith [sq_abs d, mul_nonneg (sub_nonneg.mpr hd) (add_nonneg hH (abs_nonneg d))]
  have hd4 : d ^ 4 ≤ H ^ 4 := by nlinarith [sq_nonneg (d ^ 2 - H ^ 2)]
  calc
    _ ≤ ((x + d) ^ 2 - x ^ 2) ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) hc2
    _ ≤ 8 * d ^ 2 * x ^ 2 + 2 * d ^ 4 := by
      nlinarith [sq_nonneg (2 * x * d - d ^ 2)]
    _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hd2) (sq_nonneg x)]

def quadraticReplacementCell (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (s t : ℝ≥0) (H : Ω → ℝ) (w : Ω) : ℝ :=
  H w * ((b.solution W.driver t w - b.solution W.driver s w) ^ 2 -
    (W.B t w - W.B s w) ^ 2)

theorem quadraticReplacementCell_meanSquare_le (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ) (hHm : Measurable H) (hH : ∀ w, |H w| ≤ 1) :
    Integrable (fun w => quadraticReplacementCell W b s t H w ^ 2) W.law ∧
    (∫ w, quadraticReplacementCell W b s t H w ^ 2 ∂W.law) ≤
      8 * (b.bound : ℝ) ^ 2 * ((t : ℝ) - s) ^ 3 +
        2 * (b.bound : ℝ) ^ 4 * ((t : ℝ) - s) ^ 4 := by
  let := W.isProbability
  let D : ℝ := (b.bound : ℝ) * ((t : ℝ) - s)
  have hBm : Measurable (fun w => W.B t w - W.B s w) := (W.measurable t).sub (W.measurable s)
  have hBi : Integrable (fun w => (W.B t w - W.B s w) ^ 2) W.law :=
    (W.brownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_sub (s := t) (t := s)).memLp_two.integrable_sq
  have hdom : Integrable (fun w => 8 * D ^ 2 * (W.B t w - W.B s w) ^ 2 + 2 * D ^ 4) W.law :=
    (hBi.const_mul _).add (integrable_const _)
  have hb : ∀ᵐ w ∂W.law, quadraticReplacementCell W b s t H w ^ 2 ≤
      8 * D ^ 2 * (W.B t w - W.B s w) ^ 2 + 2 * D ^ 4 := by
    filter_upwards [S32bB.solution_increment_eq W b s t hst] with w hw
    unfold quadraticReplacementCell
    rw [hw]
    apply weighted_square_displacement_sq_le _ _ _ _ (hH w)
    simpa only [D, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))] using
      b.displacement_bound W s t w
  have hm : Measurable (quadraticReplacementCell W b s t H) :=
    hHm.mul ((((b.solution_measurable W t).sub (b.solution_measurable W s)).pow_const 2).sub
      (hBm.pow_const 2))
  have hi : Integrable (fun w => quadraticReplacementCell W b s t H w ^ 2) W.law :=
    hdom.mono' (hm.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hb] with w hw
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hw)
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi hdom hb
  rw [integral_add (hBi.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hh
  have hG := (W.brownian.toIsPreBrownianReal.hasLaw_sub t s).integral_comp
    (f := fun x : ℝ => x ^ 2) (by fun_prop)
  have hdist : nndist (t : ℝ) (s : ℝ) = t - s := by
    ext
    simp only [coe_nndist, Real.dist_eq, NNReal.coe_sub hst,
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))]
  change (∫ w, (W.B t w - W.B s w) ^ 2 ∂W.law) =
    ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) at hG
  rw [hdist, integral_gaussian_square, NNReal.coe_sub hst] at hG
  rw [hG] at hh
  convert hh using 1
  dsimp only [D]
  ring

def quadraticReplacement (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (H : ℝ≥0 → Ω → ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    quadraticReplacementCell W b ((brownianDyadicGrid V).time l k)
      ((brownianDyadicGrid V).time l (k + 1)) (H ((brownianDyadicGrid V).time l k)) w

theorem quadraticReplacement_meanSquare_le (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (H : ℝ≥0 → Ω → ℝ)
    (hHm : ∀ t, Measurable (H t)) (hH : ∀ t w, |H t w| ≤ 1) (V : ℝ≥0) (l : ℕ) :
    Integrable (fun w => quadraticReplacement W b H V l w ^ 2) W.law ∧
    (∫ w, quadraticReplacement W b H V l w ^ 2 ∂W.law) ≤
      8 * (b.bound : ℝ) ^ 2 * (V : ℝ) ^ 2 * brownianDyadicWidth V l +
        2 * (b.bound : ℝ) ^ 4 * (V : ℝ) ^ 2 * brownianDyadicWidth V l ^ 2 := by
  let t := (brownianDyadicGrid V).time l
  let E := fun k => quadraticReplacementCell W b (t k) (t (k + 1)) (H (t k))
  have hm (k : ℕ) : Measurable (E k) := by
    apply (hHm (t k)).mul
    exact (((b.solution_measurable W _).sub (b.solution_measurable W _)).pow_const 2).sub
      (((W.measurable _).sub (W.measurable _)).pow_const 2)
  have hc (k : ℕ) := quadraticReplacementCell_meanSquare_le W b (t k) (t (k + 1))
    ((brownianDyadicGrid V).monotone l (Nat.le_succ k)) (H (t k)) (hHm _) (hH _)
  have hLp (k : ℕ) : MemLp (E k) 2 W.law :=
    (memLp_two_iff_integrable_sq (hm k).aestronglyMeasurable).mpr (hc k).1
  have hi : Integrable (fun w => quadraticReplacement W b H V l w ^ 2) W.law :=
    (memLp_finsetSum _ (fun k _ => hLp k)).integrable_sq
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi
    ((integrable_finsetSum _ (fun k _ => (hc k).1)).const_mul (2 ^ l : ℝ)) (fun w => by
      have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2 ^ l))
        (fun _ : ℕ => (1 : ℝ)) (fun k => E k w)
      simpa only [quadraticReplacement, E, t, one_mul, one_pow, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] using hs)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => (hc k).1)] at hh
  have hcell (k : ℕ) : (∫ w, E k w ^ 2 ∂W.law) ≤
      8 * (b.bound : ℝ) ^ 2 * brownianDyadicWidth V l ^ 3 +
        2 * (b.bound : ℝ) ^ 4 * brownianDyadicWidth V l ^ 4 := by
    simpa only [E, t, S32bB.dyadic_step_eq_width] using (hc k).2
  have hb := hh.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun k _ => hcell k)) (by positivity : (0 : ℝ) ≤ 2 ^ l))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hb
  convert hb using 1
  dsimp only [brownianDyadicWidth]
  field_simp

theorem quadraticReplacement_tendsto_L2 (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (H : ℝ≥0 → Ω → ℝ)
    (hHm : ∀ t, Measurable (H t)) (hH : ∀ t w, |H t w| ≤ 1) (V : ℝ≥0) :
    J3B.VanishingMeanSquare W.law (quadraticReplacement W b H V) := by
  refine ⟨fun l => (quadraticReplacement_meanSquare_le W b H hHm hH V l).1, ?_⟩
  apply squeeze_zero (fun l => integral_nonneg (fun w => sq_nonneg _))
    (fun l => (quadraticReplacement_meanSquare_le W b H hHm hH V l).2)
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using
    ((brownianDyadicWidth_tendsto V).const_mul (8 * (b.bound : ℝ) ^ 2 * (V : ℝ) ^ 2)).add
      (((brownianDyadicWidth_tendsto V).pow 2).const_mul (2 * (b.bound : ℝ) ^ 4 * (V : ℝ) ^ 2))

end SKConstants.Completion.X32B
