module

public import ComparisonNativeActualScalarProfile
public import ComparisonNativeGeneralScalarPairLimit
public import ComparisonStationarityDensityScaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem comparison_compensated_total_clock_le {b h e r T : ℝ}
    (he : 0 ≤ e) (hr : r ≤ 1) (htotal : h+b ≤ T) :
    (h+e*r)+(b-e) ≤ T := by
  nlinarith [mul_le_mul_of_nonneg_left hr he]

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem inherited_bf_monotone {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn M.bf (Icc (0:ℝ) 1) := by
  have H := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
    M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact toNNReal_monotoneOn H.1

theorem inherited_hf_monotone {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn M.hf (Icc (0:ℝ) 1) := by
  have H := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne'
    M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  exact toNNReal_monotoneOn H.2.1

theorem inherited_clock_coe {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (M.bf u:ℝ)=M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u) ∧
    (M.hf u:ℝ)=M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u := by
  have hr := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hg := (laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
  have hgb := (laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
    (M.hlb.trans (M.hb (by norm_num) hu hu.1))
  have hh := M.hh0.trans (M.hh (by norm_num) hu hu.1)
  exact ⟨Real.coe_toNNReal _ (sub_nonneg.mpr hgb),
    Real.coe_toNNReal _ (add_nonneg hh (mul_nonneg hg hr.1))⟩

theorem inherited_total_clock_le {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) :
    ∀u∈Icc (0:ℝ) 1,(M.hf u:ℝ)+(M.bf u:ℝ) ≤ T := by
  intro u hu
  rw [(M.inherited_clock_coe hu).1,(M.inherited_clock_coe hu).2]
  exact comparison_compensated_total_clock_le
    (laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
    (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u).2 (htotal u hu)

theorem inherited_zero_root_field {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hroot : M.h 0=0) : M.hf 0=0 := by
  have hR : M.R 0=0 := comparisonSweepQuantile_zero M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha
  apply NNReal.coe_injective
  rw [(M.inherited_clock_coe (by norm_num : (0:ℝ)∈Icc 0 1)).2,hroot,hR]
  simp

def inheritedScalarMassProfile {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) : boundedMassProfiles :=
  actualMixedMassProfile hT (n+1) (by omega) M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone (M.inherited_total_clock_le htotal)

theorem inheritedScalarMassProfile_mem {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) :
    M.inheritedScalarMassProfile hT htotal ∈ scalarProfiles := quantileMassProfile_mem _ _

theorem inheritedScalarMassProfile_right_continuous {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) (t : ℝ) :
    ContinuousWithinAt (M.inheritedScalarMassProfile hT htotal).val (Ici t) t :=
  quantileMassProfile_right_continuous _ _ _

theorem inherited_retained_scalar_pair_tendsto {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    actualMixedClock (n+1) M.bf M.hf u=
      comparisonNativeScalarClock (M.h u) (M.b u)
        (laplaceComparisonStrength M.context.d M.lam (M.R u))
        (M.R u) (orderedPathS (n+1) M.bf M.hf u) := by
  unfold actualMixedClock comparisonNativeScalarClock
  rw [(M.inherited_clock_coe hu).1,(M.inherited_clock_coe hu).2]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
