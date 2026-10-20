module

public import ComparisonNativeActualInheritedClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem native_scalar_clock_cubic_error_of_eq4
    {T b h e r s x Cb Ch Ce Cr Cs : ℝ}
    (_hx : 0 ≤ x) (hCb : 0 ≤ Cb) (hCe : 0 ≤ Ce)
    (hb : |b-T| ≤ Cb*x^2) (hh : |h| ≤ Ch*x^3)
    (he : |e| ≤ Ce*x^2) (hr : |r-s| ≤ Cr*x) (hs : |s| ≤ Cs*x) :
    |comparisonNativeScalarClock h b e r s-T*s| ≤ (Ch+Cb*Cs+Ce*Cr)*x^3 := by
  have hid : comparisonNativeScalarClock h b e r s-T*s=h+(b-T)*s+e*(r-s) := by
    unfold comparisonNativeScalarClock; ring
  have hbs:=mul_le_mul hb hs (abs_nonneg s) (mul_nonneg hCb (sq_nonneg x))
  have her:=mul_le_mul he hr (abs_nonneg (r-s)) (mul_nonneg hCe (sq_nonneg x))
  rw [hid]
  have H:=(abs_add_le (h+(b-T)*s) (e*(r-s))).trans
    (add_le_add (abs_add_le h ((b-T)*s)) le_rfl)
  rw [abs_mul,abs_mul] at H
  exact H.trans (by nlinarith only [hh,hbs,her])

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

def inheritedScalarCavityResidual {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) (u : ℝ) : ℝ :=
  orderedPathS (n+1) M.bf M.hf u-
    scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
      (actualMixedClock (n+1) M.bf M.hf u)

theorem inherited_clock_cubic_error_of_eq4 {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u x Cb Ch Ce Cr Cs : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (hx : 0 ≤ x) (hCb : 0 ≤ Cb) (hCe : 0 ≤ Ce)
    (hb : |M.b u-T| ≤ Cb*x^2) (hh : |M.h u| ≤ Ch*x^3)
    (he : laplaceComparisonStrength M.context.d M.lam (M.R u) ≤ Ce*x^2)
    (hr : |M.R u-orderedPathS (n+1) M.bf M.hf u| ≤ Cr*x)
    (hs : orderedPathS (n+1) M.bf M.hf u ≤ Cs*x) :
    |actualMixedClock (n+1) M.bf M.hf u-T*orderedPathS (n+1) M.bf M.hf u| ≤
      (Ch+Cb*Cs+Ce*Cr)*x^3 := by
  rw [M.inherited_mixed_clock_eq_nativeScalarClock hu]
  exact native_scalar_clock_cubic_error_of_eq4 hx hCb hCe hb hh
    (by rwa [abs_of_pos (laplaceComparisonStrength_pos M.context.d M.hlam (M.R u))]) hr
    (by rwa [abs_of_nonneg (M.mass_mean_nonneg hu)])

theorem inherited_scalar_quantile_radius_abs_le {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    |actualScalarClockQuantile T (n+1) M.bf M.hf u-M.R u| ≤
      |orderedPathS (n+1) M.bf M.hf u-M.R u|+
        (|M.b u-T| *orderedPathS (n+1) M.bf M.hf u+|M.h u|)/T := by
  have hs:=M.mass_mean_nonneg hu
  have herr : 0 ≤ (|M.b u-T| *orderedPathS (n+1) M.bf M.hf u+|M.h u|)/T := by positivity
  by_cases hu0 : u=0
  · subst u
    have hR : M.R 0=0 := comparisonSweepQuantile_zero M.context.hc M.context.hk
      M.context.hkc M.context.hm M.context.hM M.alpha
    simp only [actualScalarClockQuantile,le_refl,ite_true,hR,sub_zero,abs_zero]
    exact add_nonneg (abs_nonneg _) herr
  · have hup : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    rw [actualScalarClockQuantile_on (n+1) M.bf M.hf hup,
      M.inherited_mixed_clock_eq_nativeScalarClock hu]
    let e:=laplaceComparisonStrength M.context.d M.lam (M.R u)
    let S:=orderedPathS (n+1) M.bf M.hf u
    have he0 : 0 ≤ e := (laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
    have heb : e ≤ M.b u := (laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
      (M.hlb.trans (M.hb (by norm_num) hu hu.1))
    have hh0:=M.hh0.trans (M.hh (by norm_num) hu hu.1)
    have heT : e ≤ T := by linarith [htotal u hu]
    have hcoef0 : 0 ≤ 1-e/T := sub_nonneg.mpr ((div_le_one₀ hT).mpr heT)
    have hcoef1 : 1-e/T ≤ 1 := sub_le_self _ (div_nonneg he0 hT.le)
    have hid : comparisonNativeScalarClock (M.h u) (M.b u) e (M.R u) S/T-M.R u=
        (1-e/T)*(S-M.R u)+((M.b u-T)*S+M.h u)/T := by
      unfold comparisonNativeScalarClock; field_simp; ring
    change |comparisonNativeScalarClock (M.h u) (M.b u) e (M.R u) S/T-M.R u| ≤ _
    rw [hid]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul,abs_of_nonneg hcoef0]
      exact mul_le_of_le_one_left (abs_nonneg _) hcoef1
    · rw [abs_div,abs_of_pos hT]
      apply div_le_div_of_nonneg_right _ hT.le
      simpa only [abs_mul,S,abs_of_nonneg hs] using abs_add_le ((M.b u-T)*S) (M.h u)

theorem inherited_scalar_quantile_radius_abs_le_of_eq4 {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u x Cb Ch Cs : ℝ} (hu : u∈Icc (0:ℝ) 1) (hCb : 0 ≤ Cb)
    (hb : |M.b u-T| ≤ Cb*x^2) (hh : |M.h u| ≤ Ch*x^3)
    (hs : orderedPathS (n+1) M.bf M.hf u ≤ Cs*x) :
    |actualScalarClockQuantile T (n+1) M.bf M.hf u-M.R u| ≤
      |orderedPathS (n+1) M.bf M.hf u-M.R u|+((Cb*Cs+Ch)/T)*x^3 := by
  apply (M.inherited_scalar_quantile_radius_abs_le hT htotal hu).trans
  apply add_le_add le_rfl
  have H:=mul_le_mul hb hs (M.mass_mean_nonneg hu) (mul_nonneg hCb (sq_nonneg x))
  have he : ((Cb*Cs+Ch)/T)*x^3=((Cb*x^2)*(Cs*x)+Ch*x^3)/T := by ring
  rw [he]
  exact div_le_div_of_nonneg_right (add_le_add H hh) hT.le

theorem inherited_scalar_calibration_of_cavity_and_clock {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u x c Cs Ck Cr : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hCk : 0 ≤ Ck)
    (hS : orderedPathS (n+1) M.bf M.hf u ≤ Cs*x)
    (hK : T*c*x ≤ actualMixedClock (n+1) M.bf M.hf u)
    (hclock : |actualMixedClock (n+1) M.bf M.hf u-
      T*orderedPathS (n+1) M.bf M.hf u| ≤ Ck*x^3)
    (hres : |M.inheritedScalarCavityResidual hT htotal u| ≤ Cr*x^3) :
    let q:=actualMixedClock (n+1) M.bf M.hf u/T
    c*x ≤ q ∧ q ≤ (Cs+Ck/T)*x ∧
      |scalarPlantedEnergy hT (M.inheritedScalarMassProfile hT htotal) q-q| ≤
        (Cr+Ck/T)*x^3 := by
  dsimp only
  let S:=orderedPathS (n+1) M.bf M.hf u
  let K:=actualMixedClock (n+1) M.bf M.hf u
  have hcomp : |K/T-S| ≤ (Ck/T)*x^3 := by
    have he : K/T-S=(K-T*S)/T := by field_simp
    rw [he,abs_div,abs_of_pos hT]
    exact (div_le_div_of_nonneg_right hclock hT.le).trans_eq (by ring)
  have hx2 : x^2 ≤ 1 := by nlinarith only [hx,hx1,sq_nonneg (x-1)]
  have hx3 : x^3 ≤ x := by nlinarith only [mul_le_mul_of_nonneg_right hx2 hx.le]
  have hupper : K/T ≤ (Cs+Ck/T)*x := by
    have H:=le_abs_self (K/T-S)
    have Hsmall:=mul_le_mul_of_nonneg_left hx3 (div_nonneg hCk hT.le)
    change S ≤ Cs*x at hS
    linarith only [hS,H,Hsmall,hcomp]
  refine ⟨(le_div_iff₀ hT).mpr (by convert hK using 1; ring),hupper,?_⟩
  have H:=abs_sub_le (scalarPlantedEnergy hT (M.inheritedScalarMassProfile hT htotal) (K/T)) S (K/T)
  have hres' : |scalarPlantedEnergy hT (M.inheritedScalarMassProfile hT htotal) (K/T)-S| ≤ Cr*x^3 := by
    change |S-scalarPlantedEnergy hT (M.inheritedScalarMassProfile hT htotal) (K/T)| ≤ Cr*x^3 at hres
    rw [abs_sub_comm]; exact hres
  have hcomp' : |S-K/T| ≤ (Ck/T)*x^3 := by rw [abs_sub_comm];exact hcomp
  exact (H.trans (add_le_add hres' hcomp')).trans_eq (by ring)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
