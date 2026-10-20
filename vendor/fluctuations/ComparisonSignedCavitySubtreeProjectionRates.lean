module

public import ComparisonSignedCavitySubtreeProjectedFourth
public import ComparisonSignedCavityObservedInnovationWitness

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_native_subtree_exterior_fourth_from_primitives
    (B ca c₀ : ℝ) (hca : 0<ca) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (as es : List PositiveMass) (aD aE : ℝ)
      (_hoD : MassOrdered aD as) (_hoE : MassOrdered aE es)
      (T : ClockTree (Spin n) as) (sD tD : T.Slot)
      (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
      (qE qD : ℕ→RestCoordinate n→ℝ≥0),
      sD≠tD→
    ∀ (pre skip : List (GaussianStep (FeatureIndex n))) (a D pH sj r W v : ℝ),
      (clockSteps as (fun j=>restFiniteVariance n (qD j))).take (T.splitIndex sD tD)=
        skip++pre→
      0<a→0<D→D ≤ B→0 ≤ pH→0 ≤ sj→0<r→0<W→0<v→
      ca*v ≤ a→c₀*W^3/Real.log (n:ℝ) ≤ D→(n:ℝ)^(-(1:ℝ)/6+m) ≤ r→
      OrderedSteps a
        (pre++(clockSteps as (fun j=>restFiniteVariance n (qD j))).drop (T.splitIndex sD tD))→
    ∀ (P : Type) [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
      (xE xD : P→RestCoordinate n→ℝ) (hxE : Measurable xE) (_hxD : Measurable xD)
      (d : Fin pre.length→ℝ),
      (∀ j,0 ≤ d j)→(∑ j,d j=D)→
      (∀ j i,(hierarchyClocks pre j (Sum.inl i):ℝ)=d j)→
      (∫ z,E.expect (restWeight n) (restFeature n) qE (fun σ=>|H σ|^8) (xE z) ∂μ) ≤ pH^8→
      physicalOverlapMoment n 2 (clockSteps es (fun j=>restFiniteVariance n (qE j))) μ
        (fun z=>restFiniteState n (xE z)) ((restFiniteState_measurable n).comp hxE) 0 ≤ sj^4→
      (∫ z,nativeSubtreeExteriorProjectionFourth n T sD tD E H s qE qD (xE z) (xD z) ∂μ) ≤
        ((n:ℝ)/(n+1 : ℕ))^4*
          (2*(n:ℝ)^(-delta)*pH*savedWeightedExteriorScale r W v sj)^4 := by
  filter_upwards [eventually_physical_weighted_exterior_resampling_from_primitives 0 B ca c₀
    hca hc₀ hgap,eventually_gt_atTop (0:ℕ)] with n hphysical hn
  intro as es aD aE hoD hoE T sD tD E H s qE qD hst pre skip a D pH sj r W v hprefix
    ha hD hDB hpH hsj hr hW hv hmass hclock hlow hpre P _ μ _ xE xD hxE hxD d hd hdD hdclock hH hraw
  let steps:=clockSteps as (fun j=>restFiniteVariance n (qD j))
  let ext:=clockSteps es (fun j=>restFiniteVariance n (qE j))
  let R:=fun z=>restFiniteState n (xD z)
  let RE:=fun z=>restFiniteState n (xE z)
  have hR : Measurable R:=(restFiniteState_measurable n).comp hxD
  have hRE : Measurable RE:=(restFiniteState_measurable n).comp hxE
  let E':=E.realize (fun j=>restFiniteVariance n (qE j))
  let H':=fun σ=>H ((E.assignmentEquiv (fun j=>restFiniteVariance n (qE j))).symm σ)
  let s':=E.slotEquiv (fun j=>restFiniteVariance n (qE j)) s
  let tail:=steps.drop (T.splitIndex sD tD)
  have hs : OrderedSteps aD ((skip++pre)++tail) := by
    rw [←hprefix]
    simpa only [tail,steps,List.take_append_drop] using clockSteps_ordered hoD
      (fun j=>restFiniteVariance n (qD j))
  have hH' : (∫ z,E'.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>|H' σ|^8) (RE z) ∂μ) ≤ pH^8 := by
    simpa only [restFinite_clockTree_expect n hn,ClockTree.expect_realize] using hH
  rw [native_subtree_exterior_fourth_eq_physical_resampling n hn hoD T sD tD hoE E H s
    qE qD μ xE xD hxE hxD hst,hprefix]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have he:=hphysical P ext E' H' s' tail pre skip a aD aE D pH sj r W v
    ha hD hDB hpH hsj hr hW hv hmass hclock hlow hpre hs (clockSteps_ordered hoE _)
    μ RE R hRE hR d hd hdD hdclock hH' hraw
  simpa only [show 0+1=1 by norm_num,show 8*1=8 by norm_num,
    show 2*1=2 by norm_num,show 4*1=4 by norm_num] using he

theorem eventually_native_subtree_exterior_fourth_of_field_window
    (B ca c₀ : ℝ) (hca : 0<ca) (hc₀ : 0<c₀)
    {m delta : ℝ} (hgap : 2*delta<6*m) :
    ∀ᶠ n : ℕ in atTop,∀ (as es : List PositiveMass) (aD aE : ℝ)
      (hoD : MassOrdered aD as) (hoE : MassOrdered aE es)
      (T : ClockTree (Spin n) as) (sD tD : T.Slot)
      (E : ClockTree (Spin n) es) (H : E.Assignment→ℝ) (s : E.Slot)
      (qE qD : ℕ→RestCoordinate n→ℝ≥0),sD≠tD→
    ∀(i₀ : Fin n) (start : ℕ) (a pH sj r W v : ℝ),
      let steps:=clockSteps as (fun j=>restFiniteVariance n (qD j))
      let pre:=cutSlice steps start (T.splitIndex sD tD)
      let duration:=physicalFieldDuration (fun st=>st.2 (Sum.inl i₀)) pre
      start ≤ T.splitIndex sD tD→
      (∀st∈steps,∀i : Fin n,st.2 (Sum.inl i)=st.2 (Sum.inl i₀))→
      0<a→0<duration→duration ≤ B→0 ≤ pH→0 ≤ sj→0<r→0<W→0<v→
      a ≤ physicalCutMass aD steps start→
      ca*v ≤ a→c₀*W^3/Real.log (n:ℝ) ≤ duration→(n:ℝ)^(-(1:ℝ)/6+m) ≤ r→
    ∀ (P : Type) [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
      (xE xD : P→RestCoordinate n→ℝ) (hxE : Measurable xE) (hxD : Measurable xD),
      (∫ z,E.expect (restWeight n) (restFeature n) qE (fun σ=>|H σ|^8) (xE z) ∂μ) ≤ pH^8→
      physicalOverlapMoment n 2 (clockSteps es (fun j=>restFiniteVariance n (qE j))) μ
        (fun z=>restFiniteState n (xE z)) ((restFiniteState_measurable n).comp hxE) 0 ≤ sj^4→
      (∫ z,nativeSubtreeExteriorProjectionFourth n T sD tD E H s qE qD (xE z) (xD z) ∂μ) ≤
        ((n:ℝ)/(n+1 : ℕ))^4*
          (2*(n:ℝ)^(-delta)*pH*savedWeightedExteriorScale r W v sj)^4 := by
  filter_upwards [eventually_native_subtree_exterior_fourth_from_primitives B ca c₀ hca hc₀ hgap]
    with n hn
  intro as es aD aE hoD hoE T sD tD E H s qE qD hst i₀ start a pH sj r W v
  dsimp only
  intro hstart hhom ha hpos hB hpH hsj hr hW hv hmass hcaV hclock hlow P _ μ _ xE xD hxE hxD hH hraw
  let steps:=clockSteps as (fun j=>restFiniteVariance n (qD j))
  let pre:=cutSlice steps start (T.splitIndex sD tD)
  have hprefix : steps.take (T.splitIndex sD tD)=steps.take start++pre := by
    simpa only [pre,cutSlice,Nat.add_sub_of_le hstart] using
      List.take_add (l:=steps) (i:=start) (j:=T.splitIndex sD tD-start)
  have hord : OrderedSteps a (pre++steps.drop (T.splitIndex sD tD)) := by
    rw [cutSlice_append_drop steps hstart]
    exact (orderedSteps_drop_cutMass steps (clockSteps_ordered hoD _) start).lower ha.le hmass
  obtain ⟨d,hd,hds,hdclock⟩:=physical_homogeneous_field_finite_clock n pre i₀ (by
    intro st hst i
    exact hhom st (List.mem_of_mem_drop (List.mem_of_mem_take hst)) i)
  exact hn as es aD aE hoD hoE T sD tD E H s qE qD hst pre (steps.take start)
    a _ pH sj r W v hprefix ha hpos hB hpH hsj hr hW hv hcaV hclock hlow hord
    P μ xE xD hxE hxD d hd hds hdclock hH hraw

end OAI.SKFluctuations.Cavity
