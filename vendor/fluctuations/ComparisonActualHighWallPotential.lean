module

public import ComparisonActualHighWallOverlapAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def controlFactor (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ→ℝ :=
  inverseControlFactor a.data.rmin (fun r=>
    inverseControlWeight a.alpha.val.val a.data.k a.data.M r*
      comparisonCapSlope a.data.N delta (comparisonSmallMass a.data.N a.data.E)
        (comparisonConstraintLength a.data.N a.data.E a.data.d) a.data.E a.data.d
        (a.alpha.val.val r))

structure Potential (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) where
  H : ℝ→ℝ
  hH : AbsolutelyContinuousOnInterval H a.data.rmin 1
  hD : ∀ᵐ r,r∈Icc a.data.rmin 1 → HasDerivAt H
    (a.controlFactor r*radiusComparisonGradient a.data.g a.alpha.val.val
      (orderedPathS n a.bf a.hf) (orderedPathB n a.bf a.hf) r) r
  hbang : ∀ᵐ r,r∈Icc a.data.rmin 1 → H r<0 → deriv a.alpha.val.val r=a.data.M (a.alpha.val.val r)
  hfloor : ∀ᵐ r,r∈Icc a.data.rmin 1 → 0<H r → deriv a.alpha.val.val r=a.data.k r
  hzero : ∀ᵐ r,r∈Icc a.data.rmin 1 → H r=0 →
    radiusComparisonGradient a.data.g a.alpha.val.val
      (orderedPathS n a.bf a.hf) (orderedPathB n a.bf a.hf) r=0 ∧
    orderedPathS n a.bf a.hf (a.alpha.val.val r)≤r ∧
    (orderedPathS n a.bf a.hf (a.alpha.val.val r)-r)^2≤
      orderedPathB n a.bf a.hf (a.alpha.val.val r)-
        (orderedPathS n a.bf a.hf (a.alpha.val.val r))^2

theorem exists_potential
    (a : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : Nonempty a.Potential := by
  let w:=a.data
  have hr0 : w.rmin∈Icc (0:ℝ) (1/4) :=
    ⟨w.hrbounds.1.le,w.hrbounds.2.1.trans (by linarith [w.hd1])⟩
  have hs0 : w.s∈Icc (0:ℝ) (1/4) := ⟨w.hs.1.le,w.hs.2⟩
  obtain ⟨H,hH,hD,hbang,hzero⟩ := comparison_minimum_contact_potential
    w.hN w.hU w.hL (min_le_left _ _) w.hE w.hd.le w.hq hr0 hs0 n w.hn
    w.g a.alpha w.hg
    (fun r _=>laplaceComparisonStrength_pos w.d (sq_pos_of_pos w.hd) r)
    (fun r _=>⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' (sq_pos_of_pos w.hd).ne' r).1,
      (laplaceComparisonStrength_logSlope_mem w.hd.ne' (sq_pos_of_pos w.hd).ne' r).2.le⟩)
    (wallBareMatrix w.T w.epsilon w.theta w.s)
    (wallBareField w.T w.epsilon w.theta w.s w.tau w.d w.rmin)
    (fun beta=>(w.admissible beta).1) (fun beta=>(w.admissible beta).2.1)
    (fun beta=>(w.admissible beta).2.2.1) (fun beta=>(w.admissible beta).2.2.2)
    a.inverse_minimum
  refine ⟨⟨H,hH,?_,?_,?_,?_⟩⟩
  · exact hD
  · filter_upwards [hbang] with r hr hri hneg
    exact (hr hri).1 hneg
  · filter_upwards [hbang] with r hr hri hpos
    exact (hr hri).2 hpos
  · exact hzero

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
