module

public import SKConstants.ParisiEntropyPolynomialFields
public import SKConstants.ParisiBoundedExpectation

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {T : ℝ}

def entropyPolynomialRate (F : TimeField T) (N : ℕ) (v x : ℝ) : ℝ :=
  (deriv (F.f v) x)^2*(∑ k∈range N, (F.f v x)^(2*k))

lemma entropyPolynomialRate_family (F : TimeField T) (N : ℕ) :
    BoundedSmoothFamily (entropyPolynomialRate F N) := by
  have HS : BoundedSmoothFamily (fun v x => ∑ k∈range N, (F.f v x)^(2*k)) := by
    induction N with
    | zero => simpa only [sum_range_zero] using
        (BoundedSmoothFamily.timeConst (d:=fun _ : ℝ => (0:ℝ)) measurable_const (C:=0) (by simp))
    | succ N ih =>
      simp only [sum_range_succ]
      have HP := (powerTimeField F (2*N)).smooth
      have HE : (powerTimeField F (2*N)).f=fun v x => (F.f v x)^(2*N) := by
        funext v x;exact powerTimeField_f F _ v x
      rw [HE] at HP
      exact ih.add HP
  have H := (F.smooth.deriv.mul F.smooth.deriv).mul HS
  have HE : entropyPolynomialRate F N=fun v x =>
      deriv (F.f v) x*deriv (F.f v) x*(∑ k∈range N, (F.f v x)^(2*k)) := by
    funext v x
    unfold entropyPolynomialRate
    ring
  rw [HE]
  exact H

lemma entropyPolynomial_expected_integral_between (F : TimeField T) (b : BoundedLipschitzDrift)
    (W : BrownianSystem Ω) (A V : ℝ) (hA0 : 0≤A) (hAV : A≤V) (hVT : V<T)
    (hgen : ∀ v∈Icc A V, ∀ x, F.generator b.f v x=0)
    (hbr : ∀ v : ℝ≥0, ∀ᵐ w ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r w) (Ioi (v:ℝ)) v)
    (N : ℕ) :
    (entropyPolynomialTimeField F N).expected b W V=
      (entropyPolynomialTimeField F N).expected b W A-
        (1/2:ℝ)*(∫ v in A..V, ∫ w, entropyPolynomialRate F N v
          (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
  let := W.isProbability
  have HI := (bounded_family_expected_intervalIntegrable W b (entropyPolynomialRate_family F N) A V).const_mul (-1/2:ℝ)
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hAV
    ((entropyPolynomialTimeField F N).expected_continuous b W).continuousOn
    (fun v hv => ?_) HI
  · rw [intervalIntegral.integral_const_mul] at H
    linarith
  · have hv0 : 0≤v := hA0.trans hv.1.le
    have hvV : v∈Icc A V := ⟨hv.1.le,hv.2.le⟩
    have HR := (entropyPolynomialTimeField F N).expected_hasDerivWithinAt_right b W
      (Real.toNNReal v) (by simpa only [Real.coe_toNNReal v hv0] using hv.2.trans hVT)
      (hbr (Real.toNNReal v))
    simp only [Real.coe_toNNReal v hv0] at HR
    have HE : (∫ w, (entropyPolynomialTimeField F N).generator b.f v
        (b.solution W.driver (Real.toNNReal v) w) ∂W.law)=
        (-1/2:ℝ)*(∫ w, entropyPolynomialRate F N v
          (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      rw [entropyPolynomialTimeField_generator F b.f v _ (hgen v hvV _) N]
      unfold entropyPolynomialRate
      ring
    rw [HE] at HR
    convert HR using 1 <;> ring

lemma entropyPolynomial_expected_integral (F : TimeField T) (b : BoundedLipschitzDrift)
    (W : BrownianSystem Ω) (V : ℝ) (hV0 : 0≤V) (hVT : V<T)
    (hgen : ∀ v∈Icc 0 V, ∀ x, F.generator b.f v x=0)
    (hbr : ∀ v : ℝ≥0, ∀ᵐ w ∂W.law, ContinuousWithinAt (fun r => b.pathDrift W r w) (Ioi (v:ℝ)) v)
    (N : ℕ) :
    (entropyPolynomialTimeField F N).expected b W V=
      (entropyPolynomialTimeField F N).expected b W 0-
        (1/2:ℝ)*(∫ v in 0..V, ∫ w, entropyPolynomialRate F N v
          (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
  let := W.isProbability
  have HI := (bounded_family_expected_intervalIntegrable W b (entropyPolynomialRate_family F N) 0 V).const_mul (-1/2:ℝ)
  have H := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hV0
    ((entropyPolynomialTimeField F N).expected_continuous b W).continuousOn
    (fun v hv => ?_) HI
  · rw [intervalIntegral.integral_const_mul] at H
    linarith
  · have hv0 : 0≤v := hv.1.le
    have hvV : v∈Icc 0 V := ⟨hv0,hv.2.le⟩
    have HR := (entropyPolynomialTimeField F N).expected_hasDerivWithinAt_right b W
      (Real.toNNReal v) (by simpa only [Real.coe_toNNReal v hv0] using hv.2.trans hVT)
      (hbr (Real.toNNReal v))
    simp only [Real.coe_toNNReal v hv0] at HR
    have HE : (∫ w, (entropyPolynomialTimeField F N).generator b.f v
        (b.solution W.driver (Real.toNNReal v) w) ∂W.law)=
        (-1/2:ℝ)*(∫ w, entropyPolynomialRate F N v
          (b.solution W.driver (Real.toNNReal v) w) ∂W.law) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      rw [entropyPolynomialTimeField_generator F b.f v _ (hgen v hvV _) N]
      unfold entropyPolynomialRate
      ring
    rw [HE] at HR
    convert HR using 1 <;> ring

lemma entropyPolynomialRate_nonneg (F : TimeField T) (N : ℕ) (v x : ℝ) :
    0≤entropyPolynomialRate F N v x := by
  apply mul_nonneg (sq_nonneg _)
  exact sum_nonneg (fun k _ => (show Even (2*k) from ⟨k,by omega⟩).pow_nonneg _)

lemma entropyPolynomialRate_tendsto (F : TimeField T) (v x : ℝ) (hm : |F.f v x|<1) :
    Tendsto (fun N => entropyPolynomialRate F N v x) atTop
      (𝓝 ((deriv (F.f v) x)^2/(1-(F.f v x)^2))) := by
  have hs : (F.f v x)^2<1 := by nlinarith [(abs_lt.mp hm).1,(abs_lt.mp hm).2]
  have H := (hasSum_geometric_of_lt_one (sq_nonneg (F.f v x)) hs).tendsto_sum_nat
  have HE : (fun N => ∑ k∈range N, ((F.f v x)^2)^k)=fun N => ∑ k∈range N, (F.f v x)^(2*k) := by
    funext N
    simp only [pow_mul]
  rw [HE] at H
  simpa only [entropyPolynomialRate,div_eq_mul_inv] using H.const_mul ((deriv (F.f v) x)^2)

lemma entropyPolynomialRate_le_one (F : TimeField T) (N : ℕ) (v x : ℝ)
    (hm : |F.f v x|<1) (ha : |deriv (F.f v) x|≤1-(F.f v x)^2) :
    entropyPolynomialRate F N v x≤1 := by
  have hs : (F.f v x)^2<1 := by nlinarith [(abs_lt.mp hm).1,(abs_lt.mp hm).2]
  have hd : 0<1-(F.f v x)^2 := by linarith
  have HP : (∑ k∈range N, (F.f v x)^(2*k))≤(1-(F.f v x)^2)⁻¹ := by
    have HH := (hasSum_geometric_of_lt_one (sq_nonneg (F.f v x)) hs)
    have H := HH.summable.sum_le_tsum (range N) (fun k hk => pow_nonneg (sq_nonneg (F.f v x)) k)
    rw [HH.tsum_eq] at H
    simpa only [pow_mul] using H
  have HA : (deriv (F.f v) x)^2≤(1-(F.f v x)^2)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2
  unfold entropyPolynomialRate
  calc
    _ ≤ (deriv (F.f v) x)^2*(1-(F.f v x)^2)⁻¹ := mul_le_mul_of_nonneg_left HP (sq_nonneg _)
    _ ≤ 1 := by
      rw [←div_eq_mul_inv]
      apply (div_le_iff₀ hd).mpr
      have H : 1-(F.f v x)^2≤1 := by nlinarith [sq_nonneg (F.f v x)]
      nlinarith

end SKConstants.ParisiFullSupport
