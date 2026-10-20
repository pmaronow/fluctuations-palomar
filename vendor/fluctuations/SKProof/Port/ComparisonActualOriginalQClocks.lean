module

public import SKProof.Port.OriginalQHighOnlyBridge
public import ComparisonNativeActualInheritedCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_bf_monotone {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn M.sweepBf (Icc (0:ℝ) 1) := M.sweep_bf_monotone

theorem inherited_hf_monotone {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn M.sweepHf (Icc (0:ℝ) 1) := M.sweep_hf_monotone

theorem inherited_clock_coe {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (M.sweepBf u:ℝ)=M.b u-M.sweepCoefficient u ∧
      (M.sweepHf u:ℝ)=M.h u+M.sweepCoefficient u*M.sweepRadius u :=
  M.clock_coe hu

theorem coefficient_nonneg {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (u : ℝ) :
    0 ≤ M.sweepCoefficient u := by
  unfold sweepCoefficient omittedStrengthCoefficient
  split_ifs
  · exact (laplaceComparisonStrength_pos M.data.d M.hlam _).le
  · exact le_rfl

theorem coefficient_le_lam {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (u : ℝ) :
    M.sweepCoefficient u ≤ M.lam := by
  unfold sweepCoefficient omittedStrengthCoefficient
  split_ifs
  · exact laplaceComparisonStrength_le M.data.d M.hlam.le _
  · exact M.hlam.le

theorem inherited_total_clock_le {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) :
    ∀u∈Icc (0:ℝ) 1,(M.sweepHf u:ℝ)+(M.sweepBf u:ℝ) ≤ T :=
  fun _ hu=>M.total_clock_le htotal hu

theorem inherited_zero_root_field {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hroot : M.h 0=0) : M.sweepHf 0=0 := by
  have he : M.sweepCoefficient 0 = 0 := by
    simp only [sweepCoefficient, omittedStrengthCoefficient,
      ite_eq_right (not_le.mpr M.data.hs.1)]
  apply NNReal.coe_injective
  rw [(M.inherited_clock_coe (by norm_num : (0:ℝ)∈Icc 0 1)).2,hroot,he]
  simp

theorem inheritedScalarMassProfile_mem {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) :
    M.inheritedScalarMassProfileBare hT htotal ∈ scalarProfiles := quantileMassProfile_mem _ _

theorem inheritedScalarMassProfile_right_continuous {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) (t : ℝ) :
    ContinuousWithinAt (M.inheritedScalarMassProfileBare hT htotal).val (Ici t) t :=
  quantileMassProfile_right_continuous _ _ _

theorem inherited_retained_scalar_pair_tendsto {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    (hroot : M.h 0=0)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) (u : PositiveMass) (hu : u∈us) :
    Tendsto (fun k => nativeOriginalScalarPairMean (finiteCutMasses us k)
      (retainedStarMixedClock n M.sweepBf M.sweepHf (finiteCutMasses us k))
      (retainedMassPrefixIndex u.val (finiteCutMasses us k))) atTop
      (𝓝 (scalarCovarianceResponse hT (M.inheritedScalarMassProfileBare hT htotal)
        (actualMixedClock (n+1) M.sweepBf M.sweepHf u.val))) :=
  general_retained_scalar_pair_tendsto n M.sweepBf M.sweepHf M.inherited_bf_monotone
    M.inherited_hf_monotone (M.inherited_zero_root_field hroot) hT
    (M.inherited_total_clock_le htotal) us hus u hu

theorem inherited_mixed_clock_eq_nativeScalarClock {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    actualMixedClock (n+1) M.sweepBf M.sweepHf u=
      comparisonNativeScalarClock (M.h u) (M.b u)
        (M.sweepCoefficient u)
        (M.sweepRadius u) (orderedPathS (n+1) M.sweepBf M.sweepHf u) := by
  unfold actualMixedClock comparisonNativeScalarClock
  rw [(M.inherited_clock_coe hu).1,(M.inherited_clock_coe hu).2]

theorem mass_mean_nonneg {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : 0 ≤ orderedPathS (n+1) M.sweepBf M.sweepHf u := by
  by_cases hu0 : u=0
  · subst u
    simp only [orderedPathS,orderedPathPair_zero,le_refl]
  · exact (orderedPath_SK_bounds (n+1) (by omega) M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).1

theorem inverse_radius_le_regular_cap {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) : M.sweepRadius u ≤ M.z+u/cl := by
  have hr:=M.sweepRadius_bounds0 u

  by_cases hus : u<M.data.s
  · rw [M.sweepRadius_low hus.le]
    exact M.hz.1.trans (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))
  · by_cases hz : M.z ≤ M.sweepRadius u
    · have H:=(M.regular (M.sweepRadius u) ⟨hz,hr.2⟩).1
      rw [M.sweepRadius_spec ⟨le_of_not_gt hus,hu.2⟩] at H

      have H': M.sweepRadius u ≤ u/cl := (le_div_iff₀ hcl).mpr (by nlinarith only [H])
      linarith [M.data.rmin_nonneg.trans M.hz.1]
    · exact (not_le.mp hz).le.trans (le_add_of_nonneg_right (div_nonneg hu.1 hcl.le))

theorem comparison_field_le_regular_cap {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.sweepCoefficient u*M.sweepRadius u ≤ M.lam*M.z+(M.lam/cl)*u := by
  have hr:=(M.sweepRadius_bounds0 u).1

  have H:=mul_le_mul_of_nonneg_right (M.coefficient_le_lam u) hr
  have H':=mul_le_mul_of_nonneg_left (M.inverse_radius_le_regular_cap hcl hu) M.hlam.le
  apply H.trans
  convert H' using 1
  ring

variable {t : ℝ}

theorem inherited_local_temperature_scalar_quantile_on {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (t : ℝ) {u : ℝ} (hu : 0 < u) :
    actualScalarClockQuantile t (n+1) M.sweepBf M.sweepHf u=
      actualMixedClock (n+1) M.sweepBf M.sweepHf u/t :=
  actualScalarClockQuantile_on (n+1) M.sweepBf M.sweepHf hu

theorem inherited_local_temperature_scalar_quantile_radius_abs_le {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (ht : 0 < t) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    |actualScalarClockQuantile t (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u| ≤
      (1+T/t)*|orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u|+
        (|M.b u-t| * orderedPathS (n+1) M.sweepBf M.sweepHf u+|M.h u|)/t := by
  have hs:=M.mass_mean_nonneg hu
  have herr : 0 ≤ (|M.b u-t| * orderedPathS (n+1) M.sweepBf M.sweepHf u+|M.h u|)/t:=by positivity
  by_cases hu0 : u=0
  · subst u
    simp only [actualScalarClockQuantile, le_refl, ite_true, orderedPathS,
      orderedPathPair_zero, zero_sub, abs_neg]
    simp only [orderedPathS, orderedPathPair_zero] at herr
    have hTr : 0 ≤ (T/t) * |M.sweepRadius 0| :=
      mul_nonneg (div_nonneg hT.le ht.le) (abs_nonneg _)
    nlinarith only [hTr, herr]
  · have hup : 0 < u:=lt_of_le_of_ne hu.1 (Ne.symm hu0)
    rw [actualScalarClockQuantile_on (n+1) M.sweepBf M.sweepHf hup,
      M.inherited_mixed_clock_eq_nativeScalarClock hu]
    let e:=M.sweepCoefficient u
    let S:=orderedPathS (n+1) M.sweepBf M.sweepHf u
    have he0 : 0 ≤ e:=M.coefficient_nonneg u
    have heb : e ≤ M.b u := by
      have H:=(M.clocks_admissible).2.2.1 u hu
      change 0 ≤ M.b u-M.sweepCoefficient u at H
      dsimp only [e]
      linarith
    have hh0:=M.hh0.trans (M.hh (by norm_num) hu hu.1)
    have heT : e ≤ T:=by linarith [htotal u hu]
    have hcoef : |1-e/t| ≤ 1+T/t:=by
      calc
        _ ≤ |(1:ℝ)|+|e/t|:=abs_sub _ _
        _ = 1+e/t:=by rw [abs_one,abs_div,abs_of_nonneg he0,abs_of_pos ht]
        _ ≤ 1+T/t:=add_le_add le_rfl (div_le_div_of_nonneg_right heT ht.le)
    have hid : comparisonNativeScalarClock (M.h u) (M.b u) e (M.sweepRadius u) S/t-M.sweepRadius u=
        (1-e/t)*(S-M.sweepRadius u)+((M.b u-t)*S+M.h u)/t:=by
      unfold comparisonNativeScalarClock; field_simp; ring
    change |comparisonNativeScalarClock (M.h u) (M.b u) e (M.sweepRadius u) S/t-M.sweepRadius u| ≤ _
    rw [hid]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    · rw [abs_div,abs_of_pos ht]
      apply div_le_div_of_nonneg_right _ ht.le
      simpa only [abs_mul,S,abs_of_nonneg hs] using abs_add_le ((M.b u-t)*S) (M.h u)

theorem inherited_local_temperature_scalar_quantile_radius_abs_le_of_eq4 {n : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (ht : 0 < t) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T)
    {u x Cb Ch Cs : ℝ} (hu : u∈Icc (0:ℝ) 1) (hCb : 0 ≤ Cb)
    (hb : |M.b u-t| ≤ Cb*x^2) (hh : |M.h u| ≤ Ch*x^3)
    (hs : orderedPathS (n+1) M.sweepBf M.sweepHf u ≤ Cs*x) :
    |actualScalarClockQuantile t (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u| ≤
      (1+T/t)*|orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u|+((Cb*Cs+Ch)/t)*x^3 := by
  apply (M.inherited_local_temperature_scalar_quantile_radius_abs_le hT ht htotal hu).trans
  apply add_le_add le_rfl
  have H:=mul_le_mul hb hs (M.mass_mean_nonneg hu) (mul_nonneg hCb (sq_nonneg x))
  have he : ((Cb*Cs+Ch)/t)*x^3=((Cb*x^2)*(Cs*x)+Ch*x^3)/t:=by ring
  rw [he]
  exact div_le_div_of_nonneg_right (add_le_add H hh) ht.le

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
