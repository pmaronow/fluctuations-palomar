module

public import ComparisonNativeOriginalLowErrorMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_abs_sqrt_sub_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a-Real.sqrt b| ≤ Real.sqrt |a-b| := by
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  by_cases hab : a ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have HH:=mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) (Real.sqrt_nonneg a)
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb]
  · rw [abs_of_nonneg (sub_nonneg.mpr (not_le.mp hab).le)]
    have HH:=mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (not_le.mp hab).le) (Real.sqrt_nonneg b)
    nlinarith [Real.sq_sqrt ha,Real.sq_sqrt hb]

theorem native_sqrt_integral_error_le_l1_sqrt
    {f g : ℝ→ℝ} {q A : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hf0 : ∀u∈Icc (0:ℝ) 1,0 ≤ f u) (hg0 : ∀u∈Icc (0:ℝ) 1,0 ≤ g u)
    (hA : (∫u in 0..1,|f u-g u|) ≤ A) :
    |(∫u in 0..q,Real.sqrt (f u))-(∫u in 0..q,Real.sqrt (g u))| ≤ Real.sqrt A := by
  have hsif:=native_intervalIntegrable_sqrt_of_intervalIntegrable hf
  have hsig:=native_intervalIntegrable_sqrt_of_intervalIntegrable hg
  have hiabs:=(hf.sub hg).abs
  have hsabs:=native_intervalIntegrable_sqrt_of_intervalIntegrable hiabs
  have hsub : uIcc (0:ℝ) q⊆uIcc (0:ℝ) 1 := by
    rw [uIcc_of_le hq.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hq.2
  have hsifq:=hsif.mono_set hsub
  have hsigq:=hsig.mono_set hsub
  have hsabsq:=hsabs.mono_set hsub
  have HCS:=interval_integral_sqrt_sq_le_length zero_le_one hiabs (fun u _=>abs_nonneg (f u-g u))
  simp only [sub_zero,one_mul] at HCS
  have Hroot : (∫u in 0..1,Real.sqrt |f u-g u|) ≤ Real.sqrt A :=
    Real.le_sqrt_of_sq_le (HCS.trans hA)
  have Hlocal : (∫u in 0..q,Real.sqrt |f u-g u|) ≤
      (∫u in 0..1,Real.sqrt |f u-g u|) :=
    intervalIntegral.integral_mono_interval le_rfl hq.1 hq.2
      (ae_of_all _ (fun u=>Real.sqrt_nonneg |f u-g u|)) hsabs
  rw [←intervalIntegral.integral_sub hsifq hsigq]
  apply (intervalIntegral.abs_integral_le_integral_abs hq.1).trans
  apply (intervalIntegral.integral_mono_on hq.1 (hsifq.sub hsigq).abs hsabsq _).trans
    (Hlocal.trans Hroot)
  intro u hu
  exact native_abs_sqrt_sub_sqrt_le (hf0 u ⟨hu.1,hu.2.trans hq.2⟩)
    (hg0 u ⟨hu.1,hu.2.trans hq.2⟩)

theorem physicalSampledOriginalLowError_integral_error (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh q : ℝ} (hm : PartitionMesh mesh 0 as) (hq : q∈Icc (0:ℝ) 1) :
    |(∫u in 0..q,Real.sqrt (physicalSampledOriginalLowErrorSecond n b h as ha u))-
      (∫u in 0..q,Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))| ≤
      Real.sqrt (3*mesh*physicalBApproximationConstant n b h) := by
  apply native_sqrt_integral_error_le_l1_sqrt hq
    (physicalSampledOriginalLowErrorSecond_intervalIntegrable n b h hb hh as ha)
    (physicalOrderedThermal_intervalIntegrable n b h hb hh)
    (fun u _=>physicalSampledOriginalLowErrorSecond_nonneg n b h as ha u) _
    (physicalSampledOriginalLowErrorSecond_l1_bound n b h hb hh as ha he hm)
  intro u hu
  by_cases hzero : u=0
  · subst u
    simp only [orderedPathB,orderedPathS,orderedPathPair_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,le_refl]
  · exact (orderedPath_SK_bounds (n+1) (by omega) b h hb hh
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero),hu.2⟩).2.2.1 |> sub_nonneg.mpr

theorem physicalSampledOriginalLowError_integral_tendsto (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0))
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    Tendsto (fun j=>∫u in 0..q,
      Real.sqrt (physicalSampledOriginalLowErrorSecond n b h (as j) (ho j) u)) atTop
      (𝓝 (∫u in 0..q,Real.sqrt (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have H:=((hmesh.const_mul 3).mul_const (physicalBApproximationConstant n b h)).sqrt
  simp only [mul_zero,zero_mul,Real.sqrt_zero] at H
  exact squeeze_zero (fun _=>abs_nonneg _)
    (fun j=>physicalSampledOriginalLowError_integral_error n b h hb hh (as j) (ho j)
      (he j) (hm j) hq) H

end OAI.SKFluctuations.LaplaceWindowFormalization
