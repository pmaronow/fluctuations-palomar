module

public import ComparisonActualHighOnlyInverseClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def controlFactor (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ→ℝ :=
  inverseControlFactor 0 (fun r=>
    inverseControlWeight a.alpha.val.val a.data.k a.data.M r*
      comparisonCapSlope a.data.N delta (comparisonSmallMass a.data.N a.data.E)
        (comparisonConstraintLength a.data.N a.data.E a.data.d) a.data.E a.data.d
        (a.alpha.val.val r))

structure Potential (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) where
  H : ℝ→ℝ
  hH : AbsolutelyContinuousOnInterval H 0 1
  hD : ∀ᵐ r,r∈Icc 0 1 → HasDerivAt H
    (a.controlFactor r*radiusComparisonGradient (laplaceComparisonStrength a.data.d a.lam) a.alpha.val.val
      (orderedPathS n a.bf a.hf) (orderedPathB n a.bf a.hf) r) r
  hbang : ∀ᵐ r,r∈Icc 0 1 → H r<0 → deriv a.alpha.val.val r=a.data.M (a.alpha.val.val r)
  hfloor : ∀ᵐ r,r∈Icc 0 1 → 0<H r → deriv a.alpha.val.val r=a.data.k r
  hzero : ∀ᵐ r,r∈Icc 0 1 → H r=0 →
    radiusComparisonGradient (laplaceComparisonStrength a.data.d a.lam) a.alpha.val.val
      (orderedPathS n a.bf a.hf) (orderedPathB n a.bf a.hf) r=0 ∧
    orderedPathS n a.bf a.hf (a.alpha.val.val r)≤r ∧
    (orderedPathS n a.bf a.hf (a.alpha.val.val r)-r)^2≤
      orderedPathB n a.bf a.hf (a.alpha.val.val r)-
        (orderedPathS n a.bf a.hf (a.alpha.val.val r))^2

theorem exists_potential_high_only
    (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hs : a.data.s ≤ 1/4) : Nonempty a.Potential := by
  let w:=a.data
  have hr0 : (0:ℝ)∈Icc (0:ℝ) (1/4):=by norm_num
  have hs0 : w.s∈Icc (0:ℝ) (1/4):=⟨w.hs.1,hs⟩
  have hfeas (beta : w.Profile):=w.original_clocks_admissible_high_only beta a.lam_mem
  obtain ⟨H,hH,hD,hbang,hzero⟩:=comparison_minimum_contact_potential
    w.hN w.hU w.hL (min_le_left _ _) w.hE w.hd.le w.hq hr0 hs0 n w.hn
    (laplaceComparisonStrength w.d a.lam) a.alpha (laplaceComparisonStrength_contDiff w.d a.lam)
    (fun r _=>laplaceComparisonStrength_pos w.d a.hlam r)
    (fun r _=>⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' a.hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem w.hd.ne' a.hlam.ne' r).2.le⟩)
    w.b w.h (fun beta=>(hfeas beta).1) (fun beta=>(hfeas beta).2.1)
    (fun beta=>(hfeas beta).2.2.1) (fun beta=>(hfeas beta).2.2.2)
    a.optimizer.inverse_minimum
  obtain ⟨hbf,hhf⟩:=w.original_clock_eq_high_only a.alpha a.lam
  rw [hbf,hhf] at hD hzero
  refine ⟨⟨H,hH,?_,?_,?_,?_⟩⟩
  · exact hD
  · filter_upwards [hbang] with r hr hri hneg
    exact (hr hri).1 hneg
  · filter_upwards [hbang] with r hr hri hpos
    exact (hr hri).2 hpos
  · exact hzero

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
