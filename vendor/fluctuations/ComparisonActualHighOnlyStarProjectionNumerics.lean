module

public import ComparisonNativeStarMinimumCapSaving
public import ComparisonNativeStarMinimumProjection
public import ComparisonNativeStarMinimumProjectionMoment
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section
set_option linter.unusedVariables false

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

namespace ActualHighOnlyOverlapMinimum

theorem direct_test_strength_square_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hCt : 0 ≤ Ct) {v : ℝ} (hxv : M.xs ≤ v) (hv1 : v ≤ 1) :
    (1/(Ct+1))*(n:ℝ)*M.context.E^2 ≤
      laplaceComparisonStrength M.context.d M.lam v*v^2 := by
  have hv : 0 < v := M.hxs.trans_le hxv
  have hm := (laplaceComparisonStrength_monotonicities M.context.hd.ne' M.hlam
    (r₀:=0) le_rfl).2 ⟨M.hxs.le,hxv.trans hv1⟩ ⟨hv.le,hv1⟩ hxv
  have hg := laplaceComparisonStrength_pos M.context.d M.hlam v
  have hmul := mul_le_mul_of_nonneg_right hm M.hxs.le
  have hscale : laplaceComparisonStrength M.context.d M.lam M.xs*M.xs^2 ≤
      laplaceComparisonStrength M.context.d M.lam v*v^2 := by
    have hsecond := mul_le_mul_of_nonneg_left hxv (mul_nonneg hg.le hv.le)
    nlinarith
  have hbound : (n:ℝ)*M.context.E^2 ≤
      (Ct+1)*(laplaceComparisonStrength M.context.d M.lam v*v^2) := by
    have hfirst := mul_le_mul_of_nonneg_left hscale hCt
    nlinarith [M.htest,mul_nonneg hg.le (sq_nonneg v)]
  have H : ((n:ℝ)*M.context.E^2)/(Ct+1) ≤
      laplaceComparisonStrength M.context.d M.lam v*v^2 :=
    (div_le_iff₀ (by linarith : 0 < Ct+1)).mpr (by simpa only [mul_comm] using hbound)
  simpa only [div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using H

end ActualHighOnlyOverlapMinimum

theorem eventually_actual_minimum_star_cap_saving_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cprof : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCprof : 0 ≤ Cprof) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀v : ℝ,M.xs ≤ v → v ≤ 1 →
      M.context.M (Cprof*v)/
        ((n:ℝ)*laplaceComparisonStrength M.context.d M.lam v*v^4) ≤
      ((2*(Cprof+1)+(Cprof+1)^2)/((1/(Ct+1))*(1/C0)^3))*
        (n:ℝ)^(-(3*m-delta)) := by
  filter_upwards [eventually_comparison_star_cap_saving
    hm (by positivity : 0 < 1/C0) hCprof (by positivity : 0 < 1/(Ct+1))]
    with n hn
  intro M v hxv hv1
  have hlo : (1/C0)*(n:ℝ)^(-(2:ℝ)/3+m)*M.context.d ≤ M.context.E := by
    have H : ((n:ℝ)^(-(2:ℝ)/3+m)*M.context.d)/C0 ≤ M.context.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using H
  have hup : M.context.E ≤ M.context.d^2/Real.sqrt (n:ℝ) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr
    simpa only [mul_comm] using M.hupper
  exact hn M.context.d M.context.E v (laplaceComparisonStrength M.context.d M.lam v)
    M.context.hd M.context.hE hlo hup (M.hscale.trans hxv)
    (M.direct_test_strength_square_high_only hCt hxv hv1)

end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_star_projection_high_only (k dq : ℕ)
    (Bclock : ℝ) {m delta cl cu Az C0 Ct Ddepth c₁ saving Cprof Lcount Cq H₀ : ℝ}
    (hm : 0 < m) (hC0 : 0<C0) (hCt : 0≤Ct) (hCprof : 0≤Cprof)
    (hLcount : 0≤Lcount) (hCq : 0≤Cq) (hH₀ : 0≤H₀)
    (hmargin : 2*saving<3*m-delta-c₁) :
    ∀ᶠ n : ℕ in atTop,
    ∀ M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct Ddepth Bclock,
    ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (c D₀ H v theta : ℝ),
      0<D₀ → 0≤H → OrderedSteps c steps → M.xs≤v → v≤1 →
      (n:ℝ)^(-c₁)≤theta →
      laplaceComparisonStrength M.context.d M.lam v*theta*v/
        (3*M.context.M (Cprof*v)*Real.log (n:ℝ))≤D₀ →
      H≤H₀/v →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ] (z : P→FeatureIndex n→ℝ) (hz : Measurable z)
      (fork t u : ℕ) (cs : List (ℝ×ℕ)) (a D : Fin cs.length→ℝ) (a₀ Dshort : ℝ),
      t ≤ u → u ≤ steps.length+1 → lastLayerCut cs u=steps.length+1 →
      0<a₀ → D₀≤Dshort → Dshort≤Bclock →
      PhysicalProjectionClock n steps fork t u a₀ Dshort →
      M.xs+physicalCutMass c steps u≤H*a₀^2 →
      (∀j,cutPredecessor cs u j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1) →
      (∀j,0<a j ∧ D₀≤D j ∧ D j≤Bclock ∧
        PhysicalProjectionClock n steps fork (cutPredecessor cs u j) (cs.get j).2 (a j) (D j)) →
      (∀i j,i≤j.succ → M.xs+physicalCutMass c steps (overlapComponentEnd cs u i)≤H*(a j)^2) →
      ((cs.length+2:ℕ):ℝ)≤Lcount*Real.log (n:ℝ) →
      (physicalRawRatio n (k+1) steps c M.xs μ z hz)^2≤Cq*(Real.log (n:ℝ))^dq →
      physicalOverlapProjectionErrorMoment n (k+1) steps μ z hz fork t≤
        ((n:ℝ)^(-saving)*v)^(2*(k+1)) := by
  let R : ℝ := (2*(Cprof+1)+(Cprof+1)^2)/((1/(Ct+1))*(1/C0)^3)
  let C : ℝ := 12*Lcount^4*(projectionLpConstant k)^2*Cq*H₀*R
  filter_upwards [eventually_actual_minimum_star_cap_saving_high_only Bclock hm hC0 hCt hCprof,
    eventually_physical_projection_error_short_and_later k (dq+9) Bclock C hmargin,
    eventually_gt_atTop (1:ℕ)] with n hcap hproj hn
  intro M P _ steps c D₀ H v theta hD₀ hH hs hxv hv1 htheta hduration hanchor
    μ _ z hz fork t u cs a D a₀ Dshort htu hu hlast ha₀ hDshort hDB hshort hfirst
    hends hclock hscale hcount hQ
  have hN1 : 1<(n:ℝ) := by exact_mod_cast hn
  have hN : 0<(n:ℝ) := zero_lt_one.trans hN1
  have hv : 0<v := M.hxs.trans_le hxv
  have hg : 0<laplaceComparisonStrength M.context.d M.lam v := laplaceComparisonStrength_pos M.context.d M.hlam v
  have htheta0 : 0<theta := (Real.rpow_pos_of_pos hN (-c₁)).trans_le htheta
  have hlog0 : 0<Real.log (n:ℝ) := Real.log_pos hN1
  have hE := M.context.hE
  have hd := M.context.hd
  have hM : 0<M.context.M (Cprof*v) := by
    change 0<comparisonCap n delta (comparisonSmallMass n M.context.E)
      (comparisonConstraintLength n M.context.E M.context.d) M.context.E M.context.d (Cprof*v)
    have hU : 0<comparisonSmallMass n M.context.E := by
      unfold comparisonSmallMass
      positivity
    have hLc := comparisonConstraintLength_pos hN M.context.hE M.context.hd
    unfold comparisonCap
    positivity
  have hbase := physical_projection_base_of_native_geometry k dq hN hlog0
    (Nat.cast_nonneg (cs.length+2)) hLcount hCq hH₀ hH hM hg htheta0 hv
    hcount hQ hanchor hduration
  have hactual := hcap M v hxv hv1
  have hR : 0≤R := by dsimp [R]; positivity
  have hratio : M.context.M (Cprof*v)/
      ((n:ℝ)*laplaceComparisonStrength M.context.d M.lam v*v^4)/theta ≤
        R*(n:ℝ)^(-(3*m-delta-c₁)) := by
    have h1 := div_le_div_of_nonneg_right hactual htheta0.le
    have h2 := div_le_div_of_nonneg_left
      (by positivity : 0≤R*(n:ℝ)^(-(3*m-delta)))
      (Real.rpow_pos_of_pos hN (-c₁)) htheta
    apply h1.trans (h2.trans_eq _)
    rw [mul_div_assoc,←Real.rpow_sub hN]
    congr 1
    ring_nf
  have hbudget : ((cs.length+2:ℕ):ℝ)^4*
      (4*(projectionLpConstant k)^2*(Real.log (n:ℝ))^4*
        (physicalRawRatio n (k+1) steps c M.xs μ z hz)^2*H/((n:ℝ)*D₀)) ≤
      C*(Real.log (n:ℝ))^(dq+9)*(n:ℝ)^(-(3*m-delta-c₁))*v^2 := by
    apply hbase.trans
    have H := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio
        (by positivity : 0≤(12*Lcount^4*(projectionLpConstant k)^2*Cq*H₀)*(Real.log (n:ℝ))^(dq+9)))
      (sq_nonneg v)
    simpa only [C,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using H
  exact hproj P steps c D₀ M.xs H v hD₀ M.hxs hH hs μ z hz fork t u cs a D a₀ Dshort
    htu hu hlast ha₀ hDshort hDB hshort hfirst hends hclock hscale hbudget

end OAI.SKFluctuations

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization NativeStarBuffer

theorem eventually_actual_minimum_original_projection_moment_high_only
    (k : ℕ) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct Ddepth c1 saving Cprof Lcount Cq H₀ : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCprof : 0 ≤ Cprof)
    (hLcount : 0 ≤ Lcount) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀)
    (hmargin : 2*saving < 3*m-delta-c1) :
    ∀ᶠ n : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct Ddepth Bclock,
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
  filter_upwards [eventually_actual_minimum_star_projection_high_only k 0 Bclock hm hC0 hCt
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
