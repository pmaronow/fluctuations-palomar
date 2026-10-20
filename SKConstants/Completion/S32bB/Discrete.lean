module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.BrownianCenteredSquare
public import SKConstants.ParisiCDFPotentialExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace SKConstants.Completion.S32bB
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto

variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution_memLp (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (t : ℝ≥0) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (b.solution W.driver t) p W.law := by
  let := W.isProbability
  have hBrownian : MemLp (W.B t) p W.law :=
    (W.brownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval t).memLp hp
  have hB : MemLp (W.driver t) p W.law :=
    (memLp_congr_ae (W.driver_indistinguishable.mono (fun _ hw => (hw t).symm))).mp
      hBrownian
  have hC : MemLp (b.correction W.driver t) p W.law :=
    (memLp_const ((b.bound : ℝ) * t)).mono'
      (((progressive_joint_measurable _
        (b.correction_progressive _ W.driver_progressive)).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (ae_of_all _ (fun w => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg b.bound.coe_nonneg t.coe_nonneg)]
          using b.correction_bound _ W.driver_progressive t w))
  exact hB.add hC

theorem solution_increment_eq (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ w ∂W.law, b.solution W.driver t w - b.solution W.driver s w =
      (W.B t w - W.B s w) + b.displacement W s t w := by
  have he : s + (t - s) = t := add_tsub_cancel_of_le hst
  filter_upwards [b.solution_increment W s (t - s)] with w hw
  have heR : (s : ℝ) + (t - s : ℝ≥0) = t := by exact_mod_cast he
  rw [he, heR] at hw
  linarith

theorem solution_increment_sixth_moment_le (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, |b.solution W.driver t w - b.solution W.driver s w| ^ 6 ∂W.law) ≤
      32 * (((t : ℝ) - s) ^ 3 * (∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1) +
        ((b.bound : ℝ) * ((t : ℝ) - s)) ^ 6) := by
  let := W.isProbability
  have hi : Integrable (fun w => |b.solution W.driver t w - b.solution W.driver s w| ^ 6)
      W.law := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      ((solution_memLp W b t 6 (by norm_num)).sub
        (solution_memLp W b s 6 (by norm_num))).integrable_norm_pow (by norm_num : 6 ≠ 0)
  have hBi : Integrable (fun w => |W.B t w - W.B s w| ^ 6) W.law := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (W.brownian.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_sub
        (s := t) (t := s)).memLp (p := 6) (by norm_num) |>.integrable_norm_pow
          (by norm_num : 6 ≠ 0)
  have hb := integral_mono_ae hi
    ((hBi.add (integrable_const (((b.bound : ℝ) * ((t : ℝ) - s)) ^ 6))).const_mul 32) (by
      filter_upwards [solution_increment_eq W b s t hst] with w hw
      rw [hw]
      have hd := b.displacement_bound W s t w
      rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))] at hd
      calc
        _ ≤ (|W.B t w - W.B s w| + |b.displacement W s t w|) ^ 6 :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 6
        _ ≤ 32 * (|W.B t w - W.B s w| ^ 6 + |b.displacement W s t w| ^ 6) := by
          convert add_pow_le (abs_nonneg (W.B t w - W.B s w))
            (abs_nonneg (b.displacement W s t w)) 6
            using 1
          norm_num
        _ ≤ _ := by
          dsimp only [Pi.add_apply]
          gcongr)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add hBi (integrable_const _)] at hb
  have hG := (W.brownian.toIsPreBrownianReal.hasLaw_sub t s).integral_comp
    (f := fun x : ℝ => |x| ^ 6) ((continuous_abs.pow 6).measurable.aestronglyMeasurable)
  simp only [Function.comp_apply, Pi.sub_apply] at hG
  have hdist : nndist (t : ℝ) (s : ℝ) = t - s := by
    ext
    simp only [coe_nndist, Real.dist_eq, NNReal.coe_sub hst,
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))]
  change (∫ w, |W.B t w - W.B s w| ^ 6 ∂W.law) =
    (∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) at hG
  rw [hdist, gaussian_abs_pow] at hG
  rw [hG] at hb
  have hsqrt : Real.sqrt ((t - s : ℝ≥0) : ℝ) ^ 6 = ((t : ℝ) - s) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (NNReal.coe_nonneg _),
      NNReal.coe_sub hst]
  simpa only [hsqrt, integral_const, probReal_univ, smul_eq_mul, one_mul] using hb

theorem solution_increment_abs_cube_memLp (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (s t : ℝ≥0) :
    MemLp (fun w => |b.solution W.driver t w - b.solution W.driver s w| ^ 3) 2 W.law := by
  have hi := ((solution_memLp W b t 6 (by norm_num)).sub
    (solution_memLp W b s 6 (by norm_num))).integrable_norm_pow (by norm_num : 6 ≠ 0)
  apply (memLp_two_iff_integrable_sq
    ((((b.solution_measurable W t).sub (b.solution_measurable W s)).norm).pow_const 3
      |>.aestronglyMeasurable)).mpr
  simpa only [Real.norm_eq_abs, Pi.sub_apply, ← pow_mul] using hi

theorem dyadic_step_eq_width (T : ℝ≥0) (l k : ℕ) :
    ((brownianDyadicGrid T).time l (k + 1) : ℝ) - (brownianDyadicGrid T).time l k =
      brownianDyadicWidth T l := by
  simp only [brownianDyadicGrid_time_coe, brownianDyadicWidth, Nat.cast_add, Nat.cast_one]
  ring

theorem dyadic_end (T : ℝ≥0) (l : ℕ) :
    (brownianDyadicGrid T).time l (2 ^ l) = T := by
  simp [brownianDyadicGrid]

def solutionCubicSum (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (T : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    |b.solution W.driver ((brownianDyadicGrid T).time l (k + 1)) w -
      b.solution W.driver ((brownianDyadicGrid T).time l k) w| ^ 3

theorem solutionCubicSum_memLp (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (T : ℝ≥0) (l : ℕ) : MemLp (solutionCubicSum W b T l) 2 W.law := by
  exact memLp_finsetSum _ (fun k _ => solution_increment_abs_cube_memLp W b _ _)

theorem solutionCubicSum_meanSquare_le (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (T : ℝ≥0) (l : ℕ) :
    (∫ w, solutionCubicSum W b T l w ^ 2 ∂W.law) ≤
      32 * (T : ℝ) ^ 2 *
        (brownianDyadicWidth T l * (∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1) +
          (b.bound : ℝ) ^ 6 * brownianDyadicWidth T l ^ 4) := by
  let a := (brownianDyadicGrid T).time l
  let g := fun k w => |b.solution W.driver (a (k + 1)) w -
    b.solution W.driver (a k) w| ^ 3
  have hi (k : ℕ) : Integrable (fun w => g k w ^ 2) W.law :=
    (solution_increment_abs_cube_memLp W b _ _).integrable_sq
  have hsum := integral_mono ((solutionCubicSum_memLp W b T l).integrable_sq)
    ((integrable_finsetSum _ (fun k _ => hi k)).const_mul (2 ^ l : ℝ)) (fun w => by
      have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (2 ^ l))
        (fun _ : ℕ => (1 : ℝ)) (fun k => g k w)
      simpa only [solutionCubicSum, one_mul, one_pow, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat, g, a] using hh)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)] at hsum
  have hcell (k : ℕ) : (∫ w, g k w ^ 2 ∂W.law) ≤
      32 * (brownianDyadicWidth T l ^ 3 * (∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1) +
        ((b.bound : ℝ) * brownianDyadicWidth T l) ^ 6) := by
    have hh := solution_increment_sixth_moment_le W b (a k) (a (k + 1))
      ((brownianDyadicGrid T).monotone l (Nat.le_succ k))
    simpa only [g, ← pow_mul, a, dyadic_step_eq_width] using hh
  have hbound := hsum.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun k _ => hcell k)) (by positivity : (0 : ℝ) ≤ 2 ^ l))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat] at hbound
  convert hbound using 1
  dsimp only [brownianDyadicWidth]
  field_simp

theorem solutionCubicSum_tendsto_L2 (W : BrownianSystem Ω)
    (b : BoundedLipschitzDrift) (T : ℝ≥0) :
    Tendsto (fun l => ∫ w, solutionCubicSum W b T l w ^ 2 ∂W.law)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun l => integral_nonneg (fun _ => sq_nonneg _))
    (solutionCubicSum_meanSquare_le W b T)
  have hh := ((brownianDyadicWidth_tendsto T).mul_const
    (∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1)).add
      (((brownianDyadicWidth_tendsto T).pow 4).const_mul ((b.bound : ℝ) ^ 6))
  simpa only [zero_mul, zero_pow (by norm_num : 4 ≠ 0), mul_zero, add_zero] using
    hh.const_mul (32 * (T : ℝ) ^ 2)

def spatialTaylorSum (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (F : ℝ → ℝ → ℝ) (T : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    let s := (brownianDyadicGrid T).time l k
    let t := (brownianDyadicGrid T).time l (k + 1)
    let y := b.solution W.driver s w
    let d := b.solution W.driver t w - y
    F s (y + d) - F s y - deriv (F s) y * d -
      (1 / 2 : ℝ) * deriv (deriv (F s)) y * d ^ 2

theorem spatialTaylorSum_abs_le (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 3 (F t)) (C : ℝ)
    (hC : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C) (T : ℝ≥0) (l : ℕ) (w : Ω) :
    |spatialTaylorSum W b F T l w| ≤ (C / 6) * solutionCubicSum W b T l w := by
  calc
    _ ≤ ∑ k ∈ Finset.range (2 ^ l),
        |let s := (brownianDyadicGrid T).time l k
         let t := (brownianDyadicGrid T).time l (k + 1)
         let y := b.solution W.driver s w
         let d := b.solution W.driver t w - y
         F s (y + d) - F s y - deriv (F s) y * d -
           (1 / 2 : ℝ) * deriv (deriv (F s)) y * d ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (2 ^ l), (C / 6) *
        |b.solution W.driver ((brownianDyadicGrid T).time l (k + 1)) w -
          b.solution W.driver ((brownianDyadicGrid T).time l k) w| ^ 3 := by
      apply Finset.sum_le_sum
      intro k _
      exact taylor2_bound (hF _) (hC _ ) _ _
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem measurable_spatialTaylorSum (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 3 (F t)) (T : ℝ≥0) (l : ℕ) :
    Measurable (spatialTaylorSum W b F T l) := by
  apply Finset.measurable_fun_sum
  intro k _
  dsimp only
  have hY := b.solution_measurable W ((brownianDyadicGrid T).time l k)
  have hD := (b.solution_measurable W ((brownianDyadicGrid T).time l (k + 1))).sub hY
  have hF1 : ContDiff ℝ 2 (deriv (F ((brownianDyadicGrid T).time l k))) := (hF _).deriv'
  have hF2 : ContDiff ℝ 1 (deriv (deriv (F ((brownianDyadicGrid T).time l k)))) := hF1.deriv'
  exact ((((hF _).continuous.measurable.comp (hY.add hD)).sub
    ((hF _).continuous.measurable.comp hY)).sub
      ((hF1.continuous.measurable.comp hY).mul hD)).sub
        (((hF2.continuous.measurable.comp hY).const_mul _).mul (hD.pow_const 2))

theorem spatialTaylorSum_memLp (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 3 (F t)) (C : ℝ)
    (hC : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C) (T : ℝ≥0) (l : ℕ) :
    MemLp (spatialTaylorSum W b F T l) 2 W.law := by
  apply ((solutionCubicSum_memLp W b T l).const_mul (C / 6)).mono'
    (measurable_spatialTaylorSum W b F hF T l).aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs]
  exact spatialTaylorSum_abs_le W b F hF C hC T l w

theorem spatialTaylorSum_meanSquare_le (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 3 (F t)) (C : ℝ)
    (hC : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C) (T : ℝ≥0) (l : ℕ) :
    (∫ w, spatialTaylorSum W b F T l w ^ 2 ∂W.law) ≤
      (C / 6) ^ 2 * (32 * (T : ℝ) ^ 2 *
        (brownianDyadicWidth T l * (∫ x : ℝ, |x| ^ 6 ∂gaussianReal 0 1) +
          (b.bound : ℝ) ^ 6 * brownianDyadicWidth T l ^ 4)) := by
  have hh := integral_mono ((spatialTaylorSum_memLp W b F hF C hC T l).integrable_sq)
    (((solutionCubicSum_memLp W b T l).integrable_sq).const_mul ((C / 6) ^ 2)) (fun w => by
      have h := spatialTaylorSum_abs_le W b F hF C hC T l w
      have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
      simpa only [sq_abs, mul_pow] using hs)
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (solutionCubicSum_meanSquare_le W b T l) (sq_nonneg _))

theorem spatialTaylorSum_tendsto_L2 (W : BrownianSystem Ω) (b : BoundedLipschitzDrift)
    (F : ℝ → ℝ → ℝ) (hF : ∀ t, ContDiff ℝ 3 (F t)) (C : ℝ)
    (hC : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C) (T : ℝ≥0) :
    Tendsto (fun l => ∫ w, spatialTaylorSum W b F T l w ^ 2 ∂W.law)
      atTop (𝓝 0) := by
  have hbound (l : ℕ) : (∫ w, spatialTaylorSum W b F T l w ^ 2 ∂W.law) ≤
      (C / 6) ^ 2 * ∫ w, solutionCubicSum W b T l w ^ 2 ∂W.law := by
    have hh := integral_mono ((spatialTaylorSum_memLp W b F hF C hC T l).integrable_sq)
      (((solutionCubicSum_memLp W b T l).integrable_sq).const_mul ((C / 6) ^ 2)) (fun w => by
        have h := pow_le_pow_left₀ (abs_nonneg _)
          (spatialTaylorSum_abs_le W b F hF C hC T l w) 2
        simpa only [sq_abs, mul_pow] using h)
    simpa only [integral_const_mul] using hh
  exact squeeze_zero (fun l => integral_nonneg (fun _ => sq_nonneg _)) hbound
    (by simpa only [mul_zero] using (solutionCubicSum_tendsto_L2 W b T).const_mul ((C / 6) ^ 2))

end SKConstants.Completion.S32bB
