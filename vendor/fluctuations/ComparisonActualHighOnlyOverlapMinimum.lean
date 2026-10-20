module

public import ComparisonActualHighWallDescendantSource
public import ComparisonShiftedNativeBandCarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

namespace ActualHighOnlyComparisonData
abbrev floor {n : ℕ} {delta : ℝ} (a : ActualHighOnlyComparisonData n delta) := a.k 1
end ActualHighOnlyComparisonData

structure ActualHighOnlyOverlapMinimum (n : ℕ) (m delta cl cu Az C0 Ct D Bclock : ℝ) where
  data : ActualHighOnlyComparisonData n delta
  lam : ℝ
  hlam : 0 < lam
  hld : lam ≤ data.d^2
  optimizer : ActualHighOnlyComparisonMinimum data lam
  xs : ℝ
  z : ℝ
  hxs : 0 < xs
  hscale : comparisonLowerScale n data.E data.d ≤ xs
  hz : z∈Icc (0:ℝ) 1
  hzxs : z ≤ Az*xs
  hdD : data.d ≤ D
  hupper : Real.sqrt (n:ℝ)*data.E ≤ data.d^2
  hlower : (n:ℝ)^(-(2:ℝ)/3+m)*data.d ≤ C0*data.E
  htest : (n:ℝ)*data.E^2 ≤ Ct*laplaceComparisonStrength data.d lam xs*xs^2
  regular : ∀r∈Icc z 1,cl*r ≤ optimizer.alpha.val.val r ∧ optimizer.alpha.val.val r ≤ cu*r
  clockBudget : (data.hf optimizer.alpha lam 1:ℝ)-(data.hf optimizer.alpha lam 0:ℝ) ≤ Bclock

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
abbrev context := a.data
abbrev alpha := a.optimizer.alpha
abbrev b := a.data.b
abbrev h := a.data.h
abbrev R := a.data.R a.alpha
abbrev bf := a.data.bf a.alpha a.lam
abbrev hf := a.data.hf a.alpha a.lam
abbrev coefficient := a.data.coefficient a.alpha a.lam

theorem hb : MonotoneOn a.b (Icc (0:ℝ) 1) := a.data.hb
theorem hh : MonotoneOn a.h (Icc (0:ℝ) 1) := a.data.hh
theorem hh0 : 0 ≤ a.h 0 := a.data.hh0
theorem hb0 : 0 ≤ a.b 0 := a.data.hb0
theorem lam_mem : a.lam∈Icc (0:ℝ) (a.data.d^2) := ⟨a.hlam.le,a.hld⟩
theorem bf_monotone : MonotoneOn a.bf (Icc (0:ℝ) 1) := a.data.bf_monotone a.alpha a.lam_mem
theorem hf_monotone : MonotoneOn a.hf (Icc (0:ℝ) 1) := a.data.hf_monotone a.alpha a.lam_mem

theorem high_clock_coe {u : ℝ} (hu : u∈Icc a.data.s 1) :
    (a.bf u:ℝ)=a.b u-laplaceComparisonStrength a.data.d a.lam (a.R u) ∧
      (a.hf u:ℝ)=a.h u+laplaceComparisonStrength a.data.d a.lam (a.R u)*a.R u := by
  have H:=a.data.clock_coe a.alpha a.lam_mem ⟨a.data.hs.1.trans hu.1,hu.2⟩
  simpa only [ActualHighOnlyComparisonData.coefficient,omittedStrengthCoefficient,ite_eq_left hu.1] using H

abbrev shiftedNativeModel (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    ShiftedNativeBandModel where
  rmin:=0
  u0:=a.data.s
  c:=a.data.k 1
  k:=a.data.k
  M:=a.data.M
  hr:=zero_le_one
  hu:=⟨a.data.hs.1,a.data.hs1⟩
  hc:=a.data.hc
  hk:=a.data.hk
  hkc:=a.data.hkc
  hm:=a.data.hm
  hM:=a.data.hM
  alpha:=a.alpha
  n:=n
  bf:=a.bf
  hf:=a.hf
  hbf:=a.bf_monotone
  hhf:=a.hf_monotone

theorem shiftedNativeModel_radius (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : ℝ) : a.shiftedNativeModel.R u=a.R u := rfl

theorem inverse_radius_le_source_mass (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    a.R u ≤ (Az+1/cl)*(a.xs+u) := by
  have hR:=omittedSweepQuantile_bounds zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
    a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha u
  by_cases hus : u<a.data.s
  · have HR : a.R u=0 := by
      have Hmono:=omittedSweepQuantile_monotone zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
        a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha hus.le
      have Hleft:=omittedSweepQuantile_left zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
        a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha
      change a.R u≤a.R a.data.s at Hmono
      change a.R a.data.s=0 at Hleft
      linarith [hR.1]
    rw [HR]
    exact mul_nonneg (by positivity) (add_nonneg a.hxs.le hu.1)
  · have huhi : u∈Icc a.data.s 1:=⟨le_of_not_gt hus,hu.2⟩
    have Hspec:=omittedSweepQuantile_spec zero_le_one ⟨a.data.hs.1,a.data.hs1⟩
      a.data.hc a.data.hk a.data.hkc a.data.hm a.data.hM a.alpha huhi
    by_cases hsmall : a.R u < a.z
    · have H:=a.hzxs
      have HH : 0 ≤ 1/cl:=by positivity
      nlinarith [a.hxs,hu.1]
    · have Hregular:=a.regular (a.R u) ⟨le_of_not_gt hsmall,hR.2⟩
      rw [Hspec] at Hregular
      have HR : a.R u ≤ u/cl := (le_div_iff₀ hcl).mpr (by nlinarith [Hregular.1])
      have HH:=mul_le_mul_of_nonneg_right (show 1/cl≤Az+1/cl by linarith) hu.1
      calc
        a.R u ≤ u/cl:=HR
        _=(1/cl)*u:=by ring
        _ ≤ (Az+1/cl)*u:=HH
        _ ≤ (Az+1/cl)*(a.xs+u):=mul_le_mul_of_nonneg_left (by linarith [a.hxs]) (by positivity)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
