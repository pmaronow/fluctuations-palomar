module

public import ComparisonNativeStarMinimumProjectionGeometry

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization NativeStarBuffer

theorem eventually_actual_minimum_original_projection_moment
    (k : ℕ) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct Ddepth c1 saving Cprof Lcount Cq H₀ : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCprof : 0 ≤ Cprof)
    (hLcount : 0 ≤ Lcount) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀)
    (hmargin : 2*saving < 3*m-delta-c1) :
    ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum n m delta cl cu Az C0 Ct Ddepth Bclock,
      ∀(as : List PositiveMass) (_ho : MassOrdered 0 as)
        (fork t : ℕ) (H v theta : ℝ),
      0 ≤ H  →  M.xs ≤ v  →  v ≤ 1  →  (n:ℝ)^(-c1) ≤ theta  →
      let q := completedPathClock n M.bf M.hf
      let steps := sampleClockSteps q 0 as
      Nonempty (OriginalStarProjectionGeometry steps fork t
        M.xs H v theta M.context.d M.lam M.context.E delta Cprof Lcount H₀ Bclock)  →
      (physicalRawRatio n (k+1) steps 0 M.xs
        (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ Cq  →
      physicalOverlapProjectionErrorMoment n (k+1) steps
        (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id fork t ≤
        ((n:ℝ)^(-saving)*v)^(2*(k+1)) := by
  filter_upwards [eventually_actual_minimum_star_projection k 0 Bclock hm hC0 hCt
    hCprof hLcount hCq hH₀ hmargin] with n hn
  intro M as ho fork t H v theta hH hxv hv1 htheta
  dsimp only
  rintro ⟨G⟩ hraw
  exact hn M (FeatureIndex n → ℝ) _ 0 G.D₀ H v theta G.duration_pos hH
    (sampleClockSteps_ordered _ _ ho) hxv hv1 htheta G.duration_floor G.anchor_upper
    _ id measurable_id fork t G.u G.cs G.a G.D G.a₀ G.Dshort
    G.central_le G.terminal_bound G.last_cut G.short_amplitude G.short_floor
    G.short_upper G.short_clock G.first_anchor G.layer_cuts G.layer_clocks
    G.anchors G.count (by simpa only [pow_zero,mul_one] using hraw)

end OAI.SKFluctuations
