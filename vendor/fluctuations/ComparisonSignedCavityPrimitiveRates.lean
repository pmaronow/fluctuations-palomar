module

public import ComparisonSignedCavityRootCauchy
public import CavityProjectedResamplingClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem eventually_native_incoming_projection_fourth_from_primitives
    (dq : ℕ) (B Cq H₀ c₀ : ℝ) (hCq : 0 ≤ Cq) (hH₀ : 0 ≤ H₀) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop, ∀ (as : List PositiveMass) (b : ℝ)
      (ho : MassOrdered b as) (q : ℕ→RestCoordinate n→ℝ≥0)
      (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)),
      nativeIncomingNewSlot p ≠ nativeIncomingOldSlot p →
    ∀ (P : Type) [MeasurableSpace P]
      (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
      (center a D D₀ xs H r W v : ℝ),
      0<a → 0<D₀ → D₀ ≤ D → D ≤ B → 0<xs → 0 ≤ H → 0<r → 0<W → 0<v →
      (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
      PhysicalProjectionClock n (clockSteps as (fun j=>restFiniteVariance n (q j)))
        0 (nativeIncomingPairSplit p) (as.length+1) a D →
      xs+physicalCutMass b (clockSteps as (fun j=>restFiniteVariance n (q j))) 0 ≤ H*a^2 →
      (physicalRawRatio n 2 (clockSteps as (fun j=>restFiniteVariance n (q j))) b xs μ
        (fun z=>restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx))^2 ≤ 
          Cq*(Real.log (n:ℝ))^dq →
      H ≤ H₀*W/v^2 → c₀*W^3/Real.log (n:ℝ) ≤ D₀ →
    (∫ z, nativeIncomingProjectionFourth n q (x z) center p ∂μ) ≤ 
      ((n:ℝ)/(n+1 : ℕ))^4*(2*(n:ℝ)^(-delta)*savedProjectedScale r W v)^4 := by
  filter_upwards [eventually_physical_root_projected_from_primitives 1 dq B Cq H₀ c₀
    hCq hH₀ hc₀ hgap, eventually_gt_atTop (0:ℕ)] with n hphysical hn
  intro as b ho q p hst P _ μ _ x hx center a D D₀ xs H r W v
    ha hD₀ hD hDB hxs hH hr hW hv hlow hclock hscale hraw hanchor hduration
  rw [native_incoming_projection_fourth_integral_eq_resampling n hn ho q μ x hx center p hst]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hc : PhysicalProjectionClock n
      (clockSteps as (fun j=>restFiniteVariance n (q j)))
      0 (nativeIncomingPairSplit p)
      ((clockSteps as (fun j=>restFiniteVariance n (q j))).length+1) a D := by
    simpa only [length_clockSteps] using hclock
  simpa only [show 1+1=2 by norm_num,show 2*2=4 by norm_num] using
    hphysical P (clockSteps as (fun j=>restFiniteVariance n (q j))) a b D D₀ xs H r W v
      ha hD₀ hD hDB hxs hH hr hW hv hlow (clockSteps_ordered ho _) μ
      (fun z=>restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx)
      (nativeIncomingPairSplit p) hc hscale hraw hanchor hduration

theorem eventually_native_incoming_anchor_fourth_from_primitives
    (B ca c : ℝ) (hca : 0<ca) (hc : 0<c)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop, ∀ (as : List PositiveMass) (b : ℝ)
      (ho : MassOrdered b as) (E : ClockTree (Spin n) as)
      (H : E.Assignment→ℝ) (s : E.Slot) (q : ℕ→RestCoordinate n→ℝ≥0)
      (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n×Bool) as)),
      nativeIncomingNewSlot p ≠ nativeIncomingOldSlot p →
    ∀ (pre skip : List (GaussianStep (FeatureIndex n))) (a D pH sj r W v : ℝ),
      (clockSteps as (fun j=>restFiniteVariance n (q j))).take (nativeIncomingPairSplit p)=
        skip++pre →
      0<a → 0<D → D ≤ B → 0 ≤ pH → 0 ≤ sj → 0<r → 0<W → 0<v →
      ca*v ≤ a → c*W^3/Real.log (n:ℝ) ≤ D → (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
      OrderedSteps a
        (pre++(clockSteps as (fun j=>restFiniteVariance n (q j))).drop (nativeIncomingPairSplit p)) →
    ∀ (P : Type) [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
      (x : P→RestCoordinate n→ℝ) (hx : Measurable x)
      (d : Fin pre.length→ℝ), (∀ j,0 ≤ d j) → (∑ j,d j=D) →
      (∀ j i,(hierarchyClocks pre j (Sum.inl i):ℝ)=d j) →
      (∫ z,E.expect (restWeight n) (restFeature n) q (fun σ=>|H σ|^8) (x z) ∂μ) ≤ pH^8 →
      physicalOverlapMoment n 2 (clockSteps as (fun j=>restFiniteVariance n (q j))) μ
        (fun z=>restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx) 0 ≤ sj^4 →
    (∫ z,nativeIncomingAnchorFourth n E H s q (x z) p ∂μ) ≤ 
      ((n:ℝ)/(n+1 : ℕ))^4*
        (2*(n:ℝ)^(-delta)*pH*savedWeightedExteriorScale r W v sj)^4 := by
  filter_upwards [eventually_physical_weighted_exterior_resampling_from_primitives 0 B ca c
    hca hc hgap, eventually_gt_atTop (0:ℕ)] with n hphysical hn
  intro as b ho E H s q p hst pre skip a D pH sj r W v hprefix
    ha hD hDB hpH hsj hr hW hv hmass hclock hlow hpre P _ μ _ x hx d hd hdD hdclock hH hraw
  let steps := clockSteps as (fun j=>restFiniteVariance n (q j))
  let R := fun z=>restFiniteState n (x z)
  have hR : Measurable R := (restFiniteState_measurable n).comp hx
  let E' := E.realize (fun j=>restFiniteVariance n (q j))
  let H' := fun σ=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (q j))).symm σ)
  let s' := E.slotEquiv (fun j=>restFiniteVariance n (q j)) s
  let tail := steps.drop (nativeIncomingPairSplit p)
  have hs : OrderedSteps b ((skip++pre)++tail) := by
    rw [←hprefix]
    simpa only [tail,steps,List.take_append_drop] using clockSteps_ordered ho
      (fun j=>restFiniteVariance n (q j))
  have hH' : (∫ z,E'.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>|H' σ|^8) (R z) ∂μ) ≤ pH^8 := by
    simpa only [restFinite_clockTree_expect n hn,ClockTree.expect_realize] using hH
  rw [native_incoming_anchor_fourth_integral_eq_resampling n hn ho E H s q μ x hx p hst,hprefix]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hrates := hphysical P steps E' H' s' tail pre skip a b b D pH sj r W v
    ha hD hDB hpH hsj hr hW hv hmass hclock hlow hpre hs (clockSteps_ordered ho _)
    μ R R hR hR d hd hdD hdclock
  simpa only [show 0+1=1 by norm_num,show 8*1=8 by norm_num,
    show 2*1=2 by norm_num,show 4*1=4 by norm_num] using hrates hH' hraw

end OAI.SKFluctuations.Cavity
