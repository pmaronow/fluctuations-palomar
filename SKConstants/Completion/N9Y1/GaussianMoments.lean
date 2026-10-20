module

public import SKConstants.Completion.N9b.ScalarFourth
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N9Y1
open LFine N9b
variable {Ω : Type*} [MeasurableSpace Ω]

theorem predictableGaussianSum_moments_le_of_coefficient_budget (P : Measure Ω) [IsProbabilityMeasure P]
    (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hH : ∀ k, AEMeasurable (H k) P)
    (hcap : ∀ k, ∀ᵐ w ∂P, |H k w| ≤ 1)
    (hind : ∀ k, IndepFun
      (fun w => (predictableGaussianSum X H k w,H k w,predictableGaussianVariation v H k w))
        (X k) P) (b : ℝ)
    (hbudget : ∀ k, (∫ w, H k w^2 ∂P) ≤ b) (n : ℕ) :
    Integrable (fun w => predictableGaussianSum X H n w^2) P ∧
      Integrable (fun w => predictableGaussianSum X H n w^4) P ∧
      (∫ w, predictableGaussianSum X H n w^2 ∂P) ≤
        (∑ k ∈ Finset.range n, (v k : ℝ))*b ∧
      (∫ w, predictableGaussianSum X H n w^4 ∂P) ≤
        3*(∑ k ∈ Finset.range n, (v k : ℝ))^2*b := by
  have hH2 (k) : Integrable (fun w => H k w^2) P :=
    Integrable.of_bound ((hH k).pow_const 2).aestronglyMeasurable 1
      ((hcap k).mono fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs (H k w), abs_nonneg (H k w)])
  have hH4 (k) : Integrable (fun w => H k w^4) P :=
    integrable_fourth_of_memLp P (H k)
      (MemLp.of_bound (hH k).aestronglyMeasurable 1
        (by simpa only [Real.norm_eq_abs] using hcap k))
  have hS2 (k) := (predictableGaussianSum_L2_isometry P X H v hX hH hH2 hind k).1
  induction n with
  | zero => simp [predictableGaussianSum]
  | succ n ih =>
    let A := predictableGaussianSum X H n
    have hm := (aemeasurable_predictableGaussianSum P X H
      (fun k => (hX k).aemeasurable) hH n).prodMk (hH n)
    have hi : IndepFun (fun w => (A w,H n w)) (X n) P :=
      (hind n).comp
        (show Measurable (fun z : ℝ × ℝ × ℝ => (z.1,z.2.1)) from by fun_prop)
        measurable_id
    have hAH : Integrable (fun w => A w^2*H n w^2) P := by
      apply (hS2 n).mul_bdd ((hH n).pow_const 2).aestronglyMeasurable (c := 1)
      filter_upwards [hcap n] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (H n w), abs_nonneg (H n w)]
    have hfour := independent_gaussian_step_fourth P (v n) (X n) A (H n)
      hm (hX n) hi ih.2.1 hAH (hH4 n)
    have htwo := independent_gaussian_step_square P (v n) (X n) A (H n)
      hm (hX n) hi (hS2 n) (hH2 n)
    have hH4le : (∫ w, H n w^4 ∂P) ≤ b := by
      apply (integral_mono_ae (hH4 n) (hH2 n) ?_).trans (hbudget n)
      filter_upwards [hcap n] with w hw
      have hh : H n w^2 ≤ 1 := by
        nlinarith [sq_abs (H n w), abs_nonneg (H n w)]
      nlinarith [sq_nonneg (H n w)]
    have hAHle : (∫ w, A w^2*H n w^2 ∂P) ≤
        (∑ k ∈ Finset.range n, (v k : ℝ))*b := by
      apply (integral_mono_ae hAH (hS2 n) ?_).trans ih.2.2.1
      filter_upwards [hcap n] with w hw
      have hh : H n w^2 ≤ 1 := by
        nlinarith [sq_abs (H n w), abs_nonneg (H n w)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg (A w))
    refine ⟨htwo.1,hfour.1,?_,?_⟩
    · change (∫ w, (A w+H n w*X n w)^2 ∂P) ≤ _
      rw [htwo.2, Finset.sum_range_succ]
      calc
        _ ≤ (∑ k ∈ Finset.range n, (v k : ℝ))*b + (v n : ℝ)*b :=
          add_le_add ih.2.2.1 (mul_le_mul_of_nonneg_left (hbudget n) (v n).coe_nonneg)
        _ = _ := by ring
    · change (∫ w, (A w+H n w*X n w)^4 ∂P) ≤ _
      rw [hfour.2, Finset.sum_range_succ]
      calc
        _ ≤ 3*(∑ k ∈ Finset.range n, (v k : ℝ))^2*b +
            6*(v n : ℝ)*((∑ k ∈ Finset.range n, (v k : ℝ))*b) + 3*(v n : ℝ)^2*b :=
          add_le_add (add_le_add ih.2.2.2
            (mul_le_mul_of_nonneg_left hAHle (by positivity)))
            (mul_le_mul_of_nonneg_left hH4le (by positivity))
        _ = _ := by ring

theorem predictableGaussianSum_moments_le (P : Measure Ω) [IsProbabilityMeasure P]
    (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hH : ∀ k, AEMeasurable (H k) P)
    (hcap : ∀ k, ∀ᵐ w ∂P, |H k w| ≤ 1)
    (hind : ∀ k, IndepFun
      (fun w => (predictableGaussianSum X H k w,H k w,predictableGaussianVariation v H k w))
        (X k) P) (n : ℕ) :
    Integrable (fun w => predictableGaussianSum X H n w^2) P ∧
      Integrable (fun w => predictableGaussianSum X H n w^4) P ∧
      (∫ w, predictableGaussianSum X H n w^2 ∂P) ≤
        ∑ k ∈ Finset.range n, (v k : ℝ) ∧
      (∫ w, predictableGaussianSum X H n w^4 ∂P) ≤
        3*(∑ k ∈ Finset.range n, (v k : ℝ))^2 := by
  simpa only [mul_one] using
    predictableGaussianSum_moments_le_of_coefficient_budget P X H v hX hH hcap hind 1
      (fun k => by
        apply (integral_mono_ae
          (Integrable.of_bound ((hH k).pow_const 2).aestronglyMeasurable 1
            ((hcap k).mono fun w hw => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
              nlinarith [sq_abs (H k w), abs_nonneg (H k w)]))
          (integrable_const 1) ?_).trans_eq (by simp)
        filter_upwards [hcap k] with w hw
        nlinarith [sq_abs (H k w), abs_nonneg (H k w)]) n

theorem fourthMoment_le_const_of_meanSquare (P : Measure Ω) [IsFiniteMeasure P]
    (S : ℕ → Ω → ℝ) (Y : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hS : ∀ n, MemLp (S n) 2 P) (hY : MemLp Y 2 P)
    (hS4 : ∀ n, Integrable (fun w => S n w^4) P)
    (hY4 : Integrable (fun w => Y w^4) P)
    (hlim : Tendsto (fun n => ∫ w, (S n w-Y w)^2 ∂P) atTop (𝓝 0))
    (hbound : ∀ n, (∫ w, S n w^4 ∂P) ≤ C) :
    (∫ w, Y w^4 ∂P) ≤ C := by
  obtain ⟨ns, _, hae⟩ := (tendstoInMeasure_of_tendsto_integral_sq
    (fun n => ((hS n).sub hY).integrable_sq) hlim).exists_seq_tendsto_ae
  have hpow : ∀ᵐ w ∂P, Tendsto (fun n => ENNReal.ofReal (S (ns n) w^4)) atTop
      (𝓝 (ENNReal.ofReal (Y w^4))) := by
    filter_upwards [hae] with w hw
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hw.pow 4)
  have hfatou : ENNReal.ofReal (∫ w, Y w^4 ∂P) ≤ ENNReal.ofReal C := by
    rw [ofReal_integral_eq_lintegral_ofReal hY4 (ae_of_all _ fun w => by positivity)]
    calc
      _ = ∫⁻ w, liminf (fun n => ENNReal.ofReal (S (ns n) w^4)) atTop ∂P :=
        lintegral_congr_ae (hpow.mono fun w hw => hw.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ w, ENNReal.ofReal (S (ns n) w^4) ∂P) atTop :=
        lintegral_liminf_le' (fun n => (hS4 (ns n)).aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal C) atTop := by
        apply Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (hS4 (ns n))
          (ae_of_all _ fun w => by positivity)]
        exact ENNReal.ofReal_le_ofReal (hbound (ns n))
      _ = _ := by simp
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hfatou

end SKConstants.Completion.N9Y1
