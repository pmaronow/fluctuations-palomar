module

public import PhysicalBWindowBand
public import PhysicalWindowTraceAggregation
public import MassDurationSubgrid
public import WallBandCostAlgebra

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def physicalRootedCellSquareTrace (n : ℕ) (q₀ : FeatureIndex n → ℝ≥0)
    (steps : List (GaussianStep (FeatureIndex n))) (band : List PositiveMass)
    (a : ℝ) (offset : ℕ) : ℝ :=
  massCellSum band a (fun j => ∫ p, physicalCutSourceSquareTrace n steps id (offset+j) p
    ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)

theorem physicalAdjacentBFieldBands_le (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (q : ℝ → FeatureIndex (n+1) → ℝ≥0)
    (before target future : List PositiveMass) (tail : List (GaussianStep (FeatureIndex (n+1))))
    {a b g M mesh : ℝ} (hbefore : MassOrdered 0 before)
    (hendBefore : partitionEnd 0 before=a) (htarget : MassOrdered a target)
    (hendTarget : partitionEnd a target=b) (hfuture : MassOrdered b future)
    (ha0 : 0 < a) (hwidth : b < partitionEnd b future) (hg : 0 < g)
    (hmesh0 : 0 ≤ mesh)
    (hmeshTarget : ∀ (w:ℝ≥0), w ∈ sampleMassDurations a target → (w:ℝ) ≤ mesh)
    (hmeshFuture : ∀ (w:ℝ≥0), w ∈ sampleMassDurations b future → (w:ℝ) ≤ mesh)
    (hfield : ∀ st ∈ sampleClockSteps q 0 (before++target) ++ sampleClockSteps q b future,
      ∀ j, st.2 (Sum.inl j)=st.2 (Sum.inl 0))
    (hslopeTarget : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) (sampleMassDurations a target) (sampleClockSteps q a target))
    (hslopeFuture : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) (sampleMassDurations b future) (sampleClockSteps q b future)) :
    let full := ((sampleClockSteps q 0 (before++target) ++ sampleClockSteps q b future)++tail)
    ∀ (ha : OrderedSteps 0 full),
    physicalPathSecondMoment (n+1) full (q 0)
      (sampleClockSteps q 0 (before++target) ++ sampleClockSteps q b future).length ≤ M →
    massCellSum target a (fun j => rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1))
      (q 0) (fun σ τ => (orderedOverlap (n+1) σ τ)^2) full (before.length+j)) ≤
      (b-a)*(4*M^2+(112/3:ℝ)*(partitionEnd b future-b)⁻¹^2*
        ((2*M/(((n+1:ℕ):ℝ)*g)+2*mesh*M)/a))+
        2*(2*M/(((n+1:ℕ):ℝ)*g)+2*mesh*M)/a^2 := by
  dsimp only
  intro ha hmean
  let common := sampleClockSteps q 0 before
  let left := sampleClockSteps q a target
  let right := sampleClockSteps q b future
  let full := ((sampleClockSteps q 0 (before++target)++right)++tail)
  let H := 2*M/(((n+1:ℕ):ℝ)*g)+2*mesh*M
  have hab : a ≤ b := hendTarget ▸ massOrdered_start_le_end target htarget
  have hb0 : 0 < b := ha0.trans_le hab
  have hbeforeTarget : MassOrdered 0 (before++target) :=
    hbefore.append_end (hendBefore.symm ▸ htarget)
  have hendBeforeTarget : partitionEnd 0 (before++target)=b := by
    rw [partitionEnd_append,hendBefore,hendTarget]
  have hepre : sampleClockSteps q 0 (before++target)=common++left := by
    rw [sampleClockSteps_append,hendBefore]
  have hefull : full=(common++left)++(right++tail) := by
    simp only [full,hepre,List.append_assoc]
  have haTarget : OrderedSteps 0 ((common++left)++(right++tail)) := hefull ▸ ha
  have hmeanTarget : physicalPathSecondMoment (n+1) ((common++left)++(right++tail))
      (q 0) (common++left).length ≤ M := by
    rw [← hefull]
    apply (physicalPathSecondMoment_mono (n+1) full ha (q 0) _ _).trans hmean
    · rw [hepre]
      simp only [List.length_append]
      omega
    · simp only [full,right,List.length_append]
      omega
  have hM0 : 0 ≤ M := (physicalPathSecondMoment_nonneg (n+1) _ _ _).trans hmean
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hfieldTarget : ∀ st ∈ common++left, ∀ j, st.2 (Sum.inl j)=st.2 (Sum.inl 0) := by
    intro st hst j
    apply hfield st _ j
    rw [hepre]
    exact List.mem_append_left _ hst
  have hzero : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) (List.replicate common.length 0) common := by
    induction common with
    | nil => exact List.Forall₂.nil
    | cons st common ih =>
      simp only [List.length_cons,List.replicate_succ]
      exact List.Forall₂.cons (by simp) ih
  have hweights : ∀ (w:ℝ≥0), w ∈ List.replicate common.length 0 ++ sampleMassDurations a target →
      (w:ℝ) ≤ mesh := by
    intro w hw
    rcases List.mem_append.mp hw with hw|hw
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp hw
      exact hmesh0
    · exact hmeshTarget w hw
  have htraceTarget : physicalRootedCellSquareTrace (n+1) (q 0)
      ((common++left)++(right++tail)) target a before.length ≤ H := by
    unfold physicalRootedCellSquareTrace
    rw [← physicalBoundaryCap_massCellSum (n+1) q before target htarget (right++tail) haTarget]
    simpa only [H,common,left,Nat.cast_add,Nat.cast_one] using
      physicalFiniteCapBoundaryTrace_rooted_le_pathSecondMoment n d e (q 0) _ _ (right++tail)
        haTarget hmesh0 hweights hg hfieldTarget (List.rel_append hzero hslopeTarget) hmeanTarget
  have htrace : physicalRootedCellSquareTrace (n+1) (q 0) full target a before.length ≤ H := by
    rw [hefull]
    exact htraceTarget
  let J := physicalIntervalCells full (before++target).length ((before++target).length+future.length)
  let r := physicalCutIndexRadius full
  have hr : Monotone r := physicalCutIndexRadius_monotone full
  have hrc : ∀ j, physicalWindowCellMass full 0 J j ≠ 0 → r j.castSucc<r j.succ :=
    fun j _ => physicalCutIndexRadius_cell_strict full j
  have hv : 0 < physicalWindowMass full 0 J :=
    physicalWindowMass_internal_pos q (before++target) future tail hendBeforeTarget hwidth
  have hmass : physicalWindowMass full 0 J=partitionEnd b future-b :=
    physicalWindowMass_internal_eq q (before++target) future tail hendBeforeTarget
  have hS := physicalIntervalWindow_secondMoment_le_end (n+1) q (before++target) future tail ha hmean
  have henergy : (∫ p, physicalSusceptibilityMassIntegral (n+1) full id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass full 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) full) ≤ H/a := by
    have he := physicalRootedRadiusWindowSusceptibility_internal_le_cap n d e q (before++target)
      future tail hb0 hendBeforeTarget hfuture ha hg hmesh0 hmeshFuture hfield hslopeFuture hmean r hr hrc
    apply he.trans
    exact div_le_div_of_nonneg_left hH0 ha0 hab
  have hcut (j : ℕ) (hj : j<target.length) : a ≤ physicalCutMass 0 full (before.length+j) := by
    rw [hefull,physicalSampledCutMass_internal q before target (right++tail) hendBefore j hj.le]
    exact (partitionPoint_mem target htarget _).1
  have hi (i : ℕ) (hi : i<target.length) (j : Fin (full.length+1)) (hj : j∈J) :
      before.length+i ≤ j.val := by
    have hh := (mem_physicalIntervalCells full _ _ j).mp hj
    simp only [List.length_append] at hh
    omega
  have hk (j : ℕ) (hj : j<target.length) : before.length+j ≤ full.length := by
    simp only [full,List.length_append,sampleClockSteps_length]
    omega
  have hB := physicalRootLevelB_massCellSum_le_window_and_square (n+1) full ha (q 0) target htarget
    before.length hk J hv r hr hrc hi ha0 hcut (div_nonneg hH0 ha0.le) hS henergy htrace
  simpa only [hmass,hendTarget] using hB

end OAI.SKFluctuations.LaplaceWindowFormalization
