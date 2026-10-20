module

public import ComparisonNativeOverlapRawAmplitude
public import VariableEndpointComparisonPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def controlFactor (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ → ℝ :=
  inverseControlFactor 0 (fun r =>
    inverseControlWeight a.alpha.val.val a.context.k a.context.M r*
      comparisonCapSlope a.context.N delta a.context.U a.context.L a.context.E a.context.d
        (a.alpha.val.val r))

theorem controlFactor_pos (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) : 0 < a.controlFactor r := inverseControlFactor_pos _ _ _

structure Potential (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) where
  H : ℝ → ℝ
  hH : AbsolutelyContinuousOnInterval H 0 1
  hD : ∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → HasDerivAt H
    (a.controlFactor r*radiusComparisonGradient (laplaceComparisonStrength a.context.d a.lam)
      a.alpha.val.val (orderedPathS n a.bf a.hf) (orderedPathB n a.bf a.hf) r) r
  hbang : ∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → H r < 0 →
    deriv a.alpha.val.val r = a.context.M (a.alpha.val.val r)
  hfloor : ∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → 0 < H r → deriv a.alpha.val.val r = a.context.k r
  hzero : ∀ᵐ r, r ∈ Icc (0 : ℝ) 1 → H r = 0 →
    radiusComparisonGradient (laplaceComparisonStrength a.context.d a.lam)
      a.alpha.val.val (orderedPathS n a.bf a.hf) (orderedPathB n a.bf a.hf) r = 0

theorem exists_potential (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hq : 2 ≤ a.context.N^delta) : Nonempty a.Potential := by
  let c := a.context
  have hLU : c.L ≤ c.U := min_le_left _ _
  have hfeas (beta : c.Profile) := comparisonVariableEndpoint_inverse_clocks_admissible
    c.hc c.hk c.hkc c.hm c.hM a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 beta
  have hmini (beta : c.Profile) :
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        (laplaceComparisonStrength c.d a.lam) (laplaceComparisonStrength_contDiff c.d a.lam).continuous
        n a.b a.h 0 a.alpha ≤
      inverseCompensatedPressure zero_le_one zero_le_one c.hc c.hk c.hkc c.hm c.hM
        (laplaceComparisonStrength c.d a.lam) (laplaceComparisonStrength_contDiff c.d a.lam).continuous
        n a.b a.h 0 beta := by
    rw [←comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM
        n c.hn a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha,
      ←comparisonVariableEndpointObjective_eq_inverse c.hc c.hk c.hkc c.hm c.hM
        n c.hn a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 beta]
    exact a.minimum beta
  obtain ⟨H,hH,hD,hbang,hzero⟩ := comparison_minimum_contact_potential c.hN c.hU c.hL hLU c.hE c.hd.le
    hq (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) (1/4))
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) (1/4)) n c.hn
    (laplaceComparisonStrength c.d a.lam) a.alpha (laplaceComparisonStrength_contDiff c.d a.lam)
    (fun r _ => laplaceComparisonStrength_pos c.d a.hlam r)
    (fun r _ => ⟨(laplaceComparisonStrength_logSlope_mem c.hd.ne' a.hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem c.hd.ne' a.hlam.ne' r).2.le⟩)
    a.b a.h (fun beta => (hfeas beta).1) (fun beta => (hfeas beta).2.1)
    (fun beta => (hfeas beta).2.2.1) (fun beta => (hfeas beta).2.2.2) hmini
  have hstrict := inverseConstraint_strictMonoOn c.hc c.hk c.hkc a.alpha.property
  have hapos (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) : a.alpha.val.val r ∈ Ioc (0 : ℝ) 1 := by
    have hh := hstrict (by norm_num) ⟨hr.1.le,hr.2⟩ hr.1
    rw [a.alpha.property.1] at hh
    exact ⟨hh,(a.alpha.val.property.1 r).2⟩
  have hpair (P) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :=
    comparisonVariableEndpoint_inverse_pair_eq c.hc c.hk c.hkc c.hm c.hM n c.hn
      a.b a.h c.hd.ne' a.hlam.le a.hlb a.hb a.hh a.hh0 a.alpha P (hapos r hr)
  refine ⟨⟨H,hH,?_,?_,?_,?_⟩⟩
  · filter_upwards [hD,volume.ae_ne (0 : ℝ)] with r hdr hr0 hr
    have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hr.1 hr0.symm,hr.2⟩
    have hs := hpair (orderedOverlap n) r hr'
    have hb2 := hpair (fun s t => (orderedOverlap n s t)^2) r hr'
    have hh := hdr hr
    simpa only [controlFactor,radiusComparisonGradient,orderedPathS,orderedPathB,hs,hb2] using hh
  · filter_upwards [hbang] with r hr hri hneg
    exact (hr hri).1 hneg
  · filter_upwards [hbang] with r hr hri hpos
    exact (hr hri).2 hpos
  · filter_upwards [hzero,volume.ae_ne (0 : ℝ)] with r hz hr0 hr hHr
    have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hr.1 hr0.symm,hr.2⟩
    have hs := hpair (orderedOverlap n) r hr'
    have hb2 := hpair (fun s t => (orderedOverlap n s t)^2) r hr'
    have hh := (hz hr hHr).1
    simpa only [radiusComparisonGradient,orderedPathS,orderedPathB,hs,hb2] using hh

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
