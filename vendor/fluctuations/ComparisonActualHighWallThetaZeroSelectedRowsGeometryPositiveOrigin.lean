module

public import ComparisonActualHighWallThetaZeroSelectedRowsGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.retainedRows_cell_eventually_positive_origin (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg r : ℝ}
    (hag : Q.data.rmin ≤ ag) (hzg : zg ≤ 1) (hr : r∈Ioo ag zg) (hrD : r∉Dcuts)
    (hsel : r∈NativeSelectedMask.fixedSupport (fun t=>(c t).left) (fun t=>(c t).right) P.H) :
    let m:=Q.shiftedNativeModel
    ∀ᶠj in atTop,∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),
      i∈P.retainedRows c Dcuts ag zg (as j) ∧ i.val<(as j).length ∧
      r∈Ioc (m.R (partitionPoint 0 (as j) i.val)) (m.R (partitionPoint 0 (as j) (i.val+1))) := by
  dsimp only
  let m:=Q.shiftedNativeModel
  let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
  obtain ⟨h0,hN,_,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
  have HC:=NativeSelectedMask.shifted_selected_cell_eventually (fun t=>(c t).left)
    (fun t=>(c t).right) P.H Dcuts p (fun j=>(as j).length) _ h0 hN hdiam ht
    ⟨lt_of_le_of_lt hag hr.1,hr.2.trans_le hzg⟩ hrD hsel
  filter_upwards [HC,NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht
    (Ioo ag zg) isOpen_Ioo hr] with j hj hb
  obtain ⟨i,hi,hrow,hri⟩:=hj
  let ii : Fin ((sampleClockSteps m.q 0 (as j)).length+1):=
    ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hi⟩
  have hl:=hb i hi hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))
  have hu:=hb i hi hri (right_mem_Icc.mpr (hri.1.le.trans hri.2))
  have hs : m.u0 ≤ partitionPoint 0 (as j) i:=
    (m.R_high_mass (lt_of_le_of_lt hag hl.1)).le
  have hp : 0<pathMassDifferences (sampleClockSteps m.q 0 (as j)) 0 ii:=by
    rw [pathMassDifferences_eq_cutMass,
      physicalCutMass_sampleClockSteps m.q 0 (as j) i hi.le,
      physicalCutMass_sampleClockSteps m.q 0 (as j) (i+1) (by omega),sub_pos]
    by_contra hn
    exact (not_lt_of_ge (m.R_monotone (le_of_not_gt hn))) (hri.1.trans_le hri.2)
  exact ⟨ii,(P.retainedRows_mem c Dcuts ag zg (as j) ii).mpr
    ⟨hi,hrow,hp,hs,hl.1.le,hu.2.le⟩,hi,hri⟩

theorem Potential.retainedRows_support_eventually_positive_origin (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg r : ℝ}
    (hag : Q.data.rmin ≤ ag) (hzg : zg ≤ 1)
    (hrD : r∉Dcuts) (hrz : ∀t,r≠(c t).right) (hrag : r≠ag) (hrzg : r≠zg) :
    let m:=Q.shiftedNativeModel
    ∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i))
        (P.retainedRows c Dcuts ag zg (as j)) ↔ r∈P.retainedSupport c ag zg) := by
  dsimp only
  let m:=Q.shiftedNativeModel
  let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
  by_cases hband : r∈Ioo ag zg
  · by_cases hsel : r∈NativeSelectedMask.fixedSupport (fun t=>(c t).left) (fun t=>(c t).right) P.H
    · filter_upwards [P.retainedRows_cell_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim
        hag hzg hband hrD hsel] with j hj
      obtain ⟨i,hi,_,hri⟩:=hj
      exact ⟨fun _=>⟨hband,hsel⟩,fun _=>⟨i,hi,hri⟩⟩
    · obtain ⟨_,_,hp,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
      have hselExt : r∉NativeSelectedMask.fixedSupport (fun t=>(c t).left)
          (fun t=>(c t).right) P.extendedH := by
        simpa only [NativeSelectedMask.fixedSupport,mem_ofPred_eq,
          P.extendedH_eq ⟨hag.trans hband.1.le,hband.2.le.trans hzg⟩] using hsel
      filter_upwards [NativeSelectedMask.outside_cell_eventually (fun t=>(c t).left)
        (fun t=>(c t).right) P.extendedH P.extendedH_continuous.continuousOn Dcuts p
        (fun j=>(as j).length) _ (fun j i _=>hp j i) hdiam ht hselExt hrz] with j hj
      constructor
      · rintro ⟨i,hi,hri⟩
        have hh:=(P.retainedRows_mem c Dcuts ag zg (as j) i).mp hi
        have hrowExt : NativeSelectedMask.rowSelected (fun t=>(c t).left)
            (fun t=>(c t).right) P.extendedH id (p j) Dcuts i.val := by
          refine ⟨hh.2.1.1,?_⟩
          rcases hh.2.1.2 with HC|⟨t,ht,hH⟩
          · exact Or.inl HC
          · exact Or.inr ⟨t,ht,by rw [P.extendedH_eq
              ⟨(m.R_bounds _).1.trans ht.1,ht.2.trans (m.R_bounds _).2⟩];exact hH⟩
        exact False.elim (hj ⟨i.val,hh.1,hrowExt,hri⟩)
      · exact fun h=>False.elim (hsel h.2)
  · apply Eventually.of_forall
    intro j
    constructor
    · rintro ⟨i,hi,hri⟩
      have hh:=(P.retainedRows_mem c Dcuts ag zg (as j) i).mp hi
      have hrr : r∈Ioo ag zg:=⟨lt_of_le_of_ne (hh.2.2.2.2.1.trans hri.1.le) hrag.symm,
        lt_of_le_of_ne (hri.2.trans hh.2.2.2.2.2) hrzg⟩
      exact False.elim (hband hrr)
    · exact fun h=>False.elim (hband h.1)

theorem Potential.retainedRows_support_ae_positive_origin (P : Q.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ}
    (hag : Q.data.rmin ≤ ag) (hzg : zg ≤ 1) :
    let m:=Q.shiftedNativeModel
    ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i))
        (P.retainedRows c Dcuts ag zg (as j)) ↔ r∈P.retainedSupport c ag zg) := by
  dsimp only
  have hD : ∀ᵐr : ℝ,r∉Dcuts:=by apply ae_iff.mpr;simpa using Dcuts.measure_zero volume
  have hz : ∀ᵐr : ℝ,∀t,r≠(c t).right:=ae_all_iff.mpr (fun t=>volume.ae_ne _)
  filter_upwards [ae_restrict_of_ae hD,ae_restrict_of_ae hz,
    ae_restrict_of_ae (volume.ae_ne ag),ae_restrict_of_ae (volume.ae_ne zg)] with r hrD hrz hra hrb
  exact P.retainedRows_support_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg hrD hrz hra hrb
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
