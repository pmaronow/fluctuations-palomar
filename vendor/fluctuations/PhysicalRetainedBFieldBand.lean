module

public import PhysicalAdjacentBFieldBands
public import RetainedThreeCuts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalRetainedAdjacentBFieldBands_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (B F : ℝ → ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) {mesh G M : ℝ}
    (hm : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (a b c : PositiveMass) (ha : a∈as) (hb : b∈as) (hc : c∈as)
    (hab : a.val<b.val) (hbc : b.val<c.val) (hG : 0<G)
    (hslopeTarget : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      G*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (sampleMassDurations a.val (retainedMassBand a.val b.val as))
      (sampleClockSteps (completedPathClock (n+1) B F) a.val (retainedMassBand a.val b.val as)))
    (hslopeFuture : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      G*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (sampleMassDurations b.val (retainedMassBand b.val c.val (retainedMassAfter a.val as)))
      (sampleClockSteps (completedPathClock (n+1) B F) b.val
        (retainedMassBand b.val c.val (retainedMassAfter a.val as))))
    (hmean : physicalPathSecondMoment (n+1)
      (sampleClockSteps (completedPathClock (n+1) B F) 0 as)
      (completedPathClock (n+1) B F 0)
      (splitClockSteps c.val (sampleClockSteps (completedPathClock (n+1) B F) 0 as)).1.length ≤ M) :
    (∫ u in a.val..b.val, physicalSampledB n B F as ho u) ≤
      (b.val-a.val)*(4*M^2+(112/3:ℝ)*(c.val-b.val)⁻¹^2*
        ((2*M/(((n+1:ℕ):ℝ)*G)+2*mesh*M)/a.val))+
        2*(2*M/(((n+1:ℕ):ℝ)*G)+2*mesh*M)/a.val^2 := by
  let q := completedPathClock (n+1) B F
  let before := retainedMassBefore a.val as
  let target := retainedMassBand a.val b.val as
  let future := retainedMassBand b.val c.val (retainedMassAfter a.val as)
  let after := retainedMassTail b.val c.val (retainedMassAfter a.val as)
  obtain ⟨hbefore,htarget,hfuture,hafter,henda,hendb,hendc⟩ :=
    retainedMass_four_ordered as ho a b c ha hb hc hab hbc
  obtain ⟨hmeshTarget,hmeshFuture⟩ :=
    retainedMass_four_duration_mesh as ho hm a b c ha hb hc hab hbc
  have he : before++target++future++after=as := retainedMass_four_append a.val b.val c.val as
  have hclock : ((sampleClockSteps q 0 (before++target)++sampleClockSteps q b.val future)++
      sampleClockSteps q c.val after)=sampleClockSteps q 0 as := by
    rw [sampleClockSteps_append,henda]
    exact retainedMass_four_sampleClockSteps q as ho a b c ha hb hc hab hbc
  have hlength : (sampleClockSteps q 0 (before++target)++sampleClockSteps q b.val future).length=
      (splitClockSteps c.val (sampleClockSteps q 0 as)).1.length := by
    rw [retainedMass_four_splitClockSteps_length q as ho a b c ha hb hc hab hbc]
    simp only [List.length_append,sampleClockSteps_length,before,target,future]
  have hfield : ∀ st∈sampleClockSteps q 0 (before++target)++sampleClockSteps q b.val future,
      ∀ j, st.2 (Sum.inl j)=st.2 (Sum.inl 0) := by
    have hend : partitionEnd 0 (before++target)=b.val := by
      rw [partitionEnd_append,henda,hendb]
    rw [← hend,← sampleClockSteps_append]
    exact sampledFieldClock_aligned (n+1) (by omega) B F _ 0
  have hmean' : physicalPathSecondMoment (n+1)
      ((sampleClockSteps q 0 (before++target)++sampleClockSteps q b.val future)++
        sampleClockSteps q c.val after) (q 0)
      (sampleClockSteps q 0 (before++target)++sampleClockSteps q b.val future).length ≤ M := by
    rw [hclock,hlength]
    exact hmean
  have hh := physicalAdjacentBFieldBands_le n d e q before target future
    (sampleClockSteps q c.val after) hbefore henda htarget hendb hfuture a.2
    (hendc.symm ▸ hbc) hG hmesh0 hmeshTarget hmeshFuture hfield hslopeTarget hslopeFuture
    (hclock.symm ▸ sampleClockSteps_ordered q as ho) hmean'
  rw [hclock,hendc] at hh
  have hafter' : MassOrdered b.val (future++after) :=
    hfuture.append_end (hendc.symm ▸ hafter)
  have he' : before++target++(future++after)=as := by simpa only [List.append_assoc] using he
  have hi := physicalSampledB_internal_band_eq_cutSum n B F before target (future++after)
    hbefore henda htarget hendb hafter' (he'.symm ▸ ho)
  simp only [he'] at hi
  rw [hi]
  exact hh

end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalOrderedPathB_adjacent_field_band_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (B F : ℝ → ℝ≥0)
    (hB : MonotoneOn B (Icc (0:ℝ) 1)) (hF : MonotoneOn F (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hu : ∀ u∈us, u.val≤1)
    (a b c : PositiveMass) (ha : a∈us) (hb : b∈us) (hc : c∈us)
    (hab : a.val<b.val) (hbc : b.val<c.val) {G M : ℝ} (hG : 0<G)
    (hslopeTarget : ∀ k, List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      G*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (sampleMassDurations a.val (retainedMassBand a.val b.val (finiteCutMasses us k)))
      (sampleClockSteps (completedPathClock (n+1) B F) a.val
        (retainedMassBand a.val b.val (finiteCutMasses us k))))
    (hslopeFuture : ∀ k, List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      G*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (sampleMassDurations b.val
        (retainedMassBand b.val c.val (retainedMassAfter a.val (finiteCutMasses us k))))
      (sampleClockSteps (completedPathClock (n+1) B F) b.val
        (retainedMassBand b.val c.val (retainedMassAfter a.val (finiteCutMasses us k)))))
    (hmean : orderedPathS (n+1) B F c.val < M) :
    (∫ u in a.val..b.val, orderedPathB (n+1) B F u) ≤
      (b.val-a.val)*(4*M^2+(112/3:ℝ)*(c.val-b.val)⁻¹^2*
        ((2*M/(((n+1:ℕ):ℝ)*G))/a.val))+
        2*(2*M/(((n+1:ℕ):ℝ)*G))/a.val^2 := by
  let mesh : ℕ → ℝ := fun k => (((k+1:ℕ):ℝ))⁻¹
  let H : ℕ → ℝ := fun k => 2*M/(((n+1:ℕ):ℝ)*G)+2*mesh k*M
  let bound : ℕ → ℝ := fun k =>
    (b.val-a.val)*(4*M^2+(112/3:ℝ)*(c.val-b.val)⁻¹^2*(H k/a.val))+
      2*H k/a.val^2
  have hmeans := physicalRetainedSecondMoment_eventually_uniform (n+1) (by omega) B F hB hF
    (finiteCutMasses us) mesh (finiteCutMasses_ordered us hu) (finiteCutMasses_mesh us hu)
    (finiteCutMasses_end us hu) uniformMasses_mesh_tendsto c (hu c hc)
    (fun k => finiteCutMasses_nodes us k hc) hmean
  have hfinite : ∀ᶠ k in atTop,
      (∫ u in a.val..b.val, physicalSampledB n B F (finiteCutMasses us k)
        (finiteCutMasses_ordered us hu k) u) ≤ bound k := by
    filter_upwards [hmeans] with k hk
    exact physicalRetainedAdjacentBFieldBands_le n d e B F _ (finiteCutMasses_ordered us hu k)
      (finiteCutMasses_mesh us hu k) (by positivity) a b c
      (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hb) (finiteCutMasses_nodes us k hc)
      hab hbc hG (hslopeTarget k) (hslopeFuture k) (hk _ le_rfl).le
  have hH : Tendsto H atTop (𝓝 (2*M/(((n+1:ℕ):ℝ)*G))) := by
    simpa only [H,mul_zero,zero_mul,add_zero] using
      (tendsto_const_nhds.add ((uniformMasses_mesh_tendsto.const_mul 2).mul_const M))
  have hbound : Tendsto bound atTop
      (𝓝 ((b.val-a.val)*(4*M^2+(112/3:ℝ)*(c.val-b.val)⁻¹^2*
        ((2*M/(((n+1:ℕ):ℝ)*G))/a.val))+
        2*(2*M/(((n+1:ℕ):ℝ)*G))/a.val^2)) := by
    exact ((tendsto_const_nhds.add ((hH.div_const a.val).const_mul
      ((112/3:ℝ)*(c.val-b.val)⁻¹^2))).const_mul (b.val-a.val)).add
      ((hH.const_mul 2).div_const (a.val^2))
  exact physicalOrderedPathB_canonical_band_le n B F hB hF us hu bound a.2.le hab.le (hu b hb)
    hfinite hbound

end OAI.SKFluctuations.LaplaceWindowFormalization
