module

public import ComparisonNativeMassDyadicAccumulation

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_intervalIntegrable_sqrt_of_intervalIntegrable
    {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun u=>Real.sqrt (f u)) volume a b := by
  apply (hf.norm.add (intervalIntegrable_const (c:=(1:ℝ)))).mono_fun'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable_restrict_uIoc)
  apply ae_of_all
  intro u
  change ‖Real.sqrt (f u)‖ ≤ ‖f u‖+1
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_iff.mpr
  have hn := norm_nonneg (f u)
  have hfbound : f u ≤ ‖f u‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (f u)
  constructor
  · linarith
  · nlinarith

theorem native_intermediate_thermal_band_le
    {f : ℝ → ℝ} {c C x W eps : ℝ}
    (hc : 0 < c) (_hC : 0 < C) (hx : 0 < x) (hW : 0 < W) (heps : 0 ≤ eps)
    (hbase : c*x ≤ C*W) (hunit : 2*C*W ≤ 1)
    (hf : IntervalIntegrable f volume 0 1)
    (hf0 : ∀u∈Icc (0:ℝ) 1,0 ≤ f u)
    (hdyad : ∀v : ℝ,0 < v → 2*v ≤ 1 → c*x ≤ v → v ≤ C*W →
      (∫u in v..2*v,f u) ≤ eps*(x^4*v/(actualIntermediateMassEffectiveScale W v)^2)) :
    (∫u in c*x..C*W,f u) ≤
      eps*(x^4/W)*nativeIntermediateAccumulationConstant C := by
  have hratio : 1 ≤ (C*W)/(c*x) := (one_le_div (by positivity)).mpr hbase
  obtain ⟨K,hKlo,hKhi⟩ := exists_nat_pow_near hratio (show (1:ℝ) < 2 by norm_num)
  have hKupper : (2:ℝ)^K*(c*x) ≤ C*W := (le_div_iff₀ (by positivity)).mp hKlo
  have hKlower : C*W ≤ (2:ℝ)^(K+1)*(c*x) :=
    ((div_lt_iff₀ (by positivity)).mp hKhi).le
  let z := fun j : ℕ=>(2:ℝ)^j*(c*x)
  have hzPos j : 0 < z j := by dsimp [z]; positivity
  have hzNext j : z (j+1)=2*z j := by dsimp [z]; rw [pow_succ]; ring
  have hzLower j : c*x ≤ z j := by
    have HH := mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=j))
      (mul_pos hc hx).le
    simpa only [z,one_mul] using HH
  have hzUpper j (hj : j ≤ K) : z j ≤ C*W := by
    exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) (mul_pos hc hx).le).trans hKupper
  have hzLast : z (K+1) ≤ 2*C*W := by
    rw [hzNext]
    have HH := mul_le_mul_of_nonneg_left (hzUpper K le_rfl) (by norm_num : (0:ℝ) ≤ 2)
    nlinarith only [HH]
  have hIntegral j (hj : j < K+1) : IntervalIntegrable f volume (z j) (z (j+1)) := by
    apply hf.mono_set
    have horder : z j ≤ z (j+1) := by rw [hzNext]; linarith [hzPos j]
    have hlast : z (j+1) ≤ 1 := by
      rw [hzNext]
      have HH := mul_le_mul_of_nonneg_left (hzUpper j (by omega)) (by norm_num : (0:ℝ) ≤ 2)
      nlinarith only [HH,hunit]
    rw [uIcc_of_le horder,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (hzPos j).le hlast
  have Hpart j (hj : j∈Finset.range (K+1)) :
      (∫u in z j..z (j+1),f u) ≤
        (eps*x^4/W^2)*actualIntermediateMassEffectiveScale W (z j) := by
    have hju : j ≤ K := by have := Finset.mem_range.mp hj; omega
    have htwo : 2*z j ≤ 1 := by
      have HH := mul_le_mul_of_nonneg_left (hzUpper j hju) (by norm_num : (0:ℝ) ≤ 2)
      nlinarith only [HH,hunit]
    have HI := hdyad (z j) (hzPos j) htwo (hzLower j) (hzUpper j hju)
    rw [hzNext]
    apply HI.trans_eq
    rw [show x^4*z j/(actualIntermediateMassEffectiveScale W (z j))^2=
      x^4*(z j/(actualIntermediateMassEffectiveScale W (z j))^2) by ring,
      actualIntermediateMassEffectiveScale_inverse_square hW (hzPos j)]
    ring
  have Hsum := Finset.sum_le_sum (s:=Finset.range (K+1)) Hpart
  rw [intervalIntegral.sum_integral_adjacent_intervals hIntegral,←Finset.mul_sum] at Hsum
  have Hgeom := native_effective_dyadic_sum_le hW (mul_pos hc hx) K hKupper
  have Hscalar := mul_le_mul_of_nonneg_left Hgeom (show 0 ≤ eps*x^4/W^2 by positivity)
  have Hcover : (∫u in c*x..z (K+1),f u) ≤
      eps*(x^4/W)*nativeIntermediateAccumulationConstant C := by
    have HH := Hsum.trans Hscalar
    simpa only [z,pow_zero,one_mul] using HH.trans_eq (by field_simp)
  have hbigInt : IntervalIntegrable f volume (c*x) (z (K+1)) := by
    apply hf.mono_set
    rw [uIcc_of_le (hzLower _),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (mul_pos hc hx).le (hzLast.trans hunit)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (c*x) (z (K+1)))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact hf0 u ⟨(mul_pos hc hx).le.trans hu.1.le,hu.2.trans (hzLast.trans hunit)⟩
  exact (intervalIntegral.integral_mono_interval (a:=c*x) (b:=C*W)
    (c:=c*x) (d:=z (K+1)) le_rfl hbase hKlower hnonneg hbigInt).trans Hcover

theorem native_intermediate_error_band_ratio_le
    {f : ℝ → ℝ} {c C x W eps : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hx : 0 < x) (hW : 0 < W) (heps : 0 ≤ eps)
    (hbase : c*x ≤ C*W) (hunit : 2*C*W ≤ 1)
    (hf : IntervalIntegrable f volume 0 1)
    (hf0 : ∀u∈Icc (0:ℝ) 1,0 ≤ f u)
    (hdyad : ∀v : ℝ,0 < v → 2*v ≤ 1 → c*x ≤ v → v ≤ C*W →
      (∫u in v..2*v,f u) ≤ eps*(x^4*v/(actualIntermediateMassEffectiveScale W v)^2)) :
    (∫u in c*x..C*W,Real.sqrt (f u))/x^2 ≤
      Real.sqrt (C*eps*nativeIntermediateAccumulationConstant C) := by
  have Hthermal := native_intermediate_thermal_band_le hc hC hx hW heps hbase hunit hf hf0 hdyad
  have htop : C*W ≤ 1 := by nlinarith [mul_pos hC hW]
  have hfi : IntervalIntegrable f volume (c*x) (C*W) := by
    apply hf.mono_set
    rw [uIcc_of_le hbase,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (mul_pos hc hx).le htop
  have HCS := interval_integral_sqrt_sq_le_length hbase hfi
    (fun u hu=>hf0 u ⟨(mul_pos hc hx).le.trans hu.1,hu.2.trans htop⟩)
  have Hbound := mul_le_mul_of_nonneg_left Hthermal (sub_nonneg.mpr hbase)
  have Hlength := mul_le_mul_of_nonneg_right (show C*W-c*x ≤ C*W by linarith [mul_pos hc hx])
    (show 0 ≤ eps*(x^4/W)*nativeIntermediateAccumulationConstant C by
      exact mul_nonneg (by positivity) (nativeIntermediateAccumulationConstant_pos C).le)
  apply Real.le_sqrt_of_sq_le
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (pow_pos hx 2) 2)).mpr
  have HH := HCS.trans (Hbound.trans Hlength)
  convert HH using 1
  field_simp

theorem native_initial_plus_intermediate_error_ratio_le
    {f : ℝ → ℝ} {c C x W eps : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hx : 0 < x) (hW : 0 < W) (heps : 0 ≤ eps)
    (hbaseunit : c*x ≤ 1) (hunit : 2*C*W ≤ 1)
    (hf : IntervalIntegrable f volume 0 1)
    (hf0 : ∀u∈Icc (0:ℝ) 1,0 ≤ f u)
    (hdyad : ∀v : ℝ,0 < v → 2*v ≤ 1 → c*x ≤ v → v ≤ C*W →
      (∫u in v..2*v,f u) ≤ eps*(x^4*v/(actualIntermediateMassEffectiveScale W v)^2)) :
    (∫u in 0..C*W,Real.sqrt (f u))/x^2 ≤
      (∫u in 0..c*x,Real.sqrt (f u))/x^2+
        Real.sqrt (C*eps*nativeIntermediateAccumulationConstant C) := by
  have hsi := native_intervalIntegrable_sqrt_of_intervalIntegrable hf
  have htop : C*W ≤ 1 := by nlinarith [mul_pos hC hW]
  have hi0 : IntervalIntegrable (fun u=>Real.sqrt (f u)) volume 0 (c*x) := by
    apply hsi.mono_set
    rw [uIcc_of_le (mul_pos hc hx).le,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hbaseunit
  by_cases hbase : c*x ≤ C*W
  · have hitail : IntervalIntegrable (fun u=>Real.sqrt (f u)) volume (c*x) (C*W) := by
      apply hsi.mono_set
      rw [uIcc_of_le hbase,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (mul_pos hc hx).le htop
    rw [←intervalIntegral.integral_add_adjacent_intervals hi0 hitail,add_div]
    exact add_le_add le_rfl
      (native_intermediate_error_band_ratio_le hc hC hx hW heps hbase hunit hf hf0 hdyad)
  · have Hmono := intervalIntegral.integral_mono_interval (a:=0) (b:=C*W)
      (c:=0) (d:=c*x) le_rfl (mul_pos hC hW).le (not_le.mp hbase).le
      (ae_of_all _ (fun u=>Real.sqrt_nonneg (f u))) hi0
    have HH := div_le_div_of_nonneg_right Hmono (sq_nonneg x)
    exact HH.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))

end OAI.SKFluctuations.LaplaceWindowFormalization
