module

public import ComparisonNativeActualInheritedCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T t : ℝ}

theorem inherited_local_temperature_scalar_quantile_on {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (t : ℝ) {u : ℝ} (hu : 0 < u) :
    actualScalarClockQuantile t (n+1) M.bf M.hf u=
      actualMixedClock (n+1) M.bf M.hf u/t :=
  actualScalarClockQuantile_on (n+1) M.bf M.hf hu

theorem inherited_local_temperature_scalar_quantile_radius_abs_le {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (ht : 0 < t) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    |actualScalarClockQuantile t (n+1) M.bf M.hf u-M.R u| ≤
      (1+T/t)*|orderedPathS (n+1) M.bf M.hf u-M.R u|+
        (|M.b u-t| * orderedPathS (n+1) M.bf M.hf u+|M.h u|)/t := by
  have hs:=M.mass_mean_nonneg hu
  have herr : 0 ≤ (|M.b u-t| * orderedPathS (n+1) M.bf M.hf u+|M.h u|)/t:=by positivity
  by_cases hu0 : u=0
  · subst u
    have hR : M.R 0=0:=comparisonSweepQuantile_zero M.context.hc M.context.hk
      M.context.hkc M.context.hm M.context.hM M.alpha
    simp only [actualScalarClockQuantile,le_refl,ite_true,hR,sub_zero,abs_zero]
    exact add_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) herr
  · have hup : 0 < u:=lt_of_le_of_ne hu.1 (Ne.symm hu0)
    rw [actualScalarClockQuantile_on (n+1) M.bf M.hf hup,
      M.inherited_mixed_clock_eq_nativeScalarClock hu]
    let e:=laplaceComparisonStrength M.context.d M.lam (M.R u)
    let S:=orderedPathS (n+1) M.bf M.hf u
    have he0 : 0 ≤ e:=(laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
    have heb : e ≤ M.b u:=(laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
      (M.hlb.trans (M.hb (by norm_num) hu hu.1))
    have hh0:=M.hh0.trans (M.hh (by norm_num) hu hu.1)
    have heT : e ≤ T:=by linarith [htotal u hu]
    have hcoef : |1-e/t| ≤ 1+T/t:=by
      calc
        _ ≤ |(1:ℝ)|+|e/t|:=abs_sub _ _
        _ = 1+e/t:=by rw [abs_one,abs_div,abs_of_nonneg he0,abs_of_pos ht]
        _ ≤ 1+T/t:=add_le_add le_rfl (div_le_div_of_nonneg_right heT ht.le)
    have hid : comparisonNativeScalarClock (M.h u) (M.b u) e (M.R u) S/t-M.R u=
        (1-e/t)*(S-M.R u)+((M.b u-t)*S+M.h u)/t:=by
      unfold comparisonNativeScalarClock; field_simp; ring
    change |comparisonNativeScalarClock (M.h u) (M.b u) e (M.R u) S/t-M.R u| ≤ _
    rw [hid]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    · rw [abs_div,abs_of_pos ht]
      apply div_le_div_of_nonneg_right _ ht.le
      simpa only [abs_mul,S,abs_of_nonneg hs] using abs_add_le ((M.b u-t)*S) (M.h u)

theorem inherited_local_temperature_scalar_quantile_radius_abs_le_of_eq4 {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (ht : 0 < t) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u x Cb Ch Cs : ℝ} (hu : u∈Icc (0:ℝ) 1) (hCb : 0 ≤ Cb)
    (hb : |M.b u-t| ≤ Cb*x^2) (hh : |M.h u| ≤ Ch*x^3)
    (hs : orderedPathS (n+1) M.bf M.hf u ≤ Cs*x) :
    |actualScalarClockQuantile t (n+1) M.bf M.hf u-M.R u| ≤
      (1+T/t)*|orderedPathS (n+1) M.bf M.hf u-M.R u|+((Cb*Cs+Ch)/t)*x^3 := by
  apply (M.inherited_local_temperature_scalar_quantile_radius_abs_le hT ht htotal hu).trans
  apply add_le_add le_rfl
  have H:=mul_le_mul hb hs (M.mass_mean_nonneg hu) (mul_nonneg hCb (sq_nonneg x))
  have he : ((Cb*Cs+Ch)/t)*x^3=((Cb*x^2)*(Cs*x)+Ch*x^3)/t:=by ring
  rw [he]
  exact div_le_div_of_nonneg_right (add_le_add H hh) ht.le

theorem inherited_local_temperature_scalar_radius_integral_le_of_eq4 {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (ht : 0 < t) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {v x Cb Ch Cs : ℝ} (hv : v∈Icc (0:ℝ) 1) (hCb : 0 ≤ Cb)
    (hb : ∀u∈Icc (0:ℝ) v,|M.b u-t| ≤ Cb*x^2)
    (hh : ∀u∈Icc (0:ℝ) v,|M.h u| ≤ Ch*x^3)
    (hs : ∀u∈Icc (0:ℝ) v,orderedPathS (n+1) M.bf M.hf u ≤ Cs*x) :
    (∫u in 0..v,|actualScalarClockQuantile t (n+1) M.bf M.hf u-M.R u|) ≤
      (1+T/t)*(∫u in 0..v,|orderedPathS (n+1) M.bf M.hf u-M.R u|)+
        ((Cb*Cs+Ch)/t)*x^3*v := by
  have hsub : uIcc (0:ℝ) v ⊆ uIcc (0:ℝ) 1:=by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2
  have hqi : IntervalIntegrable (actualScalarClockQuantile t (n+1) M.bf M.hf) volume 0 v:=
    (show MonotoneOn (actualScalarClockQuantile t (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using
        actualScalarClockQuantile_monotone ht (n+1) (by omega) M.bf M.hf
          M.inherited_bf_monotone M.inherited_hf_monotone).intervalIntegrable.mono_set hsub
  have hsi : IntervalIntegrable (orderedPathS (n+1) M.bf M.hf) volume 0 v:=
    (show MonotoneOn (orderedPathS (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.mono_set hsub
  have hri : IntervalIntegrable M.R volume 0 v:=
    (comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha).intervalIntegrable 0 v
  have H:=intervalIntegral.integral_mono_on hv.1 (hqi.sub hri).abs
    (((hsi.sub hri).abs.const_mul (1+T/t)).add intervalIntegrable_const) (fun u hu=>
      M.inherited_local_temperature_scalar_quantile_radius_abs_le_of_eq4 hT ht htotal
        ⟨hu.1,hu.2.trans hv.2⟩ hCb (hb u hu) (hh u hu) (hs u hu))
  rw [intervalIntegral.integral_add ((hsi.sub hri).abs.const_mul (1+T/t)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at H
  exact H.trans_eq (by ring)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
