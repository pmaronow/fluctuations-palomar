module

public import ComparisonActualHighOnlyOverlapMinimum
public import ComparisonNativeActualInheritedCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_bf_monotone {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn M.bf (Icc (0:ℝ) 1) := M.bf_monotone

theorem inherited_hf_monotone {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn M.hf (Icc (0:ℝ) 1) := M.hf_monotone

theorem inherited_clock_coe {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (M.bf u:ℝ)=M.b u-M.coefficient u ∧
      (M.hf u:ℝ)=M.h u+M.coefficient u*M.R u :=
  M.data.clock_coe M.alpha M.lam_mem hu

theorem coefficient_nonneg {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (u : ℝ) :
    0 ≤ M.coefficient u := by
  unfold coefficient ActualHighOnlyComparisonData.coefficient omittedStrengthCoefficient
  split_ifs
  · exact (laplaceComparisonStrength_pos M.data.d M.hlam _).le
  · exact le_rfl

theorem coefficient_le_lam {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (u : ℝ) :
    M.coefficient u ≤ M.lam := by
  unfold coefficient ActualHighOnlyComparisonData.coefficient omittedStrengthCoefficient
  split_ifs
  · exact laplaceComparisonStrength_le M.data.d M.hlam.le _
  · exact M.hlam.le

theorem R_zero {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) : M.R 0=0 := by
  have Hl:=omittedSweepQuantile_left zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
  have Hm:=omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha M.data.hs.1
  have Hb:=(omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha 0).1
  change M.R M.data.s=0 at Hl
  change M.R 0≤M.R M.data.s at Hm
  linarith

theorem inherited_total_clock_le {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) :
    ∀u∈Icc (0:ℝ) 1,(M.hf u:ℝ)+(M.bf u:ℝ) ≤ T :=
  fun _ hu=>M.data.total_clock_le M.alpha M.lam_mem htotal hu

theorem inherited_zero_root_field {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hroot : M.h 0=0) : M.hf 0=0 := by
  have hR : M.R 0=0 := M.R_zero
  apply NNReal.coe_injective
  rw [(M.inherited_clock_coe (by norm_num : (0:ℝ)∈Icc 0 1)).2,hroot,hR]
  simp

def inheritedScalarMassProfile {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) : boundedMassProfiles :=
  actualMixedMassProfile hT (n+1) (by omega) M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone (M.inherited_total_clock_le htotal)

theorem inheritedScalarMassProfile_mem {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) :
    M.inheritedScalarMassProfile hT htotal ∈ scalarProfiles := quantileMassProfile_mem _ _

theorem inheritedScalarMassProfile_right_continuous {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) (t : ℝ) :
    ContinuousWithinAt (M.inheritedScalarMassProfile hT htotal).val (Ici t) t :=
  quantileMassProfile_right_continuous _ _ _

theorem inherited_retained_scalar_pair_tendsto {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k => nativeOriginalScalarPairMean (finiteCutMasses us k)
      (retainedStarMixedClock n M.bf M.hf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (scalarCovarianceResponse hT (M.inheritedScalarMassProfile hT htotal)
        (actualMixedClock (n+1) M.bf M.hf u.val))) :=
  general_retained_scalar_pair_tendsto n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu

theorem inherited_mixed_clock_eq_nativeScalarClock {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    actualMixedClock (n+1) M.bf M.hf u=
      comparisonNativeScalarClock (M.h u) (M.b u)
        (M.coefficient u)
        (M.R u) (orderedPathS (n+1) M.bf M.hf u) := by
  unfold actualMixedClock comparisonNativeScalarClock
  rw [(M.inherited_clock_coe hu).1,(M.inherited_clock_coe hu).2]

theorem mass_mean_nonneg {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : 0 ≤ orderedPathS (n+1) M.bf M.hf u := by
  by_cases hu0 : u=0
  · subst u
    simp only [orderedPathS,orderedPathPair_zero,le_refl]
  · exact (orderedPath_SK_bounds (n+1) (by omega) M.bf M.hf M.bf_monotone M.hf_monotone
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).1

theorem inverse_radius_le_regular_cap {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : M.R u ≤ M.z+u/cl := by
  have hr:=omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha u
  by_cases hus : u<M.data.s
  · have Hm:=omittedSweepQuantile_monotone zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha hus.le
    have Hl:=omittedSweepQuantile_left zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
      M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
    change M.R u ≤ M.R M.data.s at Hm
    change M.R M.data.s=0 at Hl
    exact (Hm.trans_eq Hl).trans (add_nonneg M.hz.1 (div_nonneg hu.1 hcl.le))
  · by_cases hz : M.z ≤ M.R u
    · have H:=(M.regular (M.R u) ⟨hz,hr.2⟩).1
      rw [omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
        M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha ⟨le_of_not_gt hus,hu.2⟩] at H
      have H': M.R u ≤ u/cl := (le_div_iff₀ hcl).mpr (by nlinarith only [H])
      linarith [M.hz.1]
    · exact (not_le.mp hz).le.trans (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))

theorem comparison_field_le_regular_cap {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.coefficient u*M.R u ≤ M.lam*M.z+(M.lam/cl)*u := by
  have hr:=(omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha u).1
  have H:=mul_le_mul_of_nonneg_right (M.coefficient_le_lam u) hr
  have H':=mul_le_mul_of_nonneg_left (M.inverse_radius_le_regular_cap hcl hu) M.hlam.le
  apply H.trans
  convert H' using 1
  ring

variable {t : ℝ}

theorem inherited_local_temperature_scalar_quantile_on {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (t : ℝ) {u : ℝ} (hu : 0 < u) :
    actualScalarClockQuantile t (n+1) M.bf M.hf u=
      actualMixedClock (n+1) M.bf M.hf u/t :=
  actualScalarClockQuantile_on (n+1) M.bf M.hf hu

theorem inherited_local_temperature_scalar_quantile_radius_abs_le {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (ht : 0 < t) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    |actualScalarClockQuantile t (n+1) M.bf M.hf u-M.R u| ≤
      (1+T/t)*|orderedPathS (n+1) M.bf M.hf u-M.R u|+
        (|M.b u-t| * orderedPathS (n+1) M.bf M.hf u+|M.h u|)/t := by
  have hs:=M.mass_mean_nonneg hu
  have herr : 0 ≤ (|M.b u-t| * orderedPathS (n+1) M.bf M.hf u+|M.h u|)/t:=by positivity
  by_cases hu0 : u=0
  · subst u
    have hR : M.R 0=0:=M.R_zero
    simp only [actualScalarClockQuantile,le_refl,ite_true,hR,sub_zero,abs_zero]
    exact add_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) herr
  · have hup : 0 < u:=lt_of_le_of_ne hu.1 (Ne.symm hu0)
    rw [actualScalarClockQuantile_on (n+1) M.bf M.hf hup,
      M.inherited_mixed_clock_eq_nativeScalarClock hu]
    let e:=M.coefficient u
    let S:=orderedPathS (n+1) M.bf M.hf u
    have he0 : 0 ≤ e:=M.coefficient_nonneg u
    have heb : e ≤ M.b u := by
      have H:=(M.data.clocks_admissible M.alpha M.lam_mem).2.2.1 u hu
      change 0 ≤ M.b u-M.coefficient u at H
      dsimp only [e]
      linarith
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
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
