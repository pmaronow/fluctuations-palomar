module

public import ComparisonActualHighWallThetaZeroRetainedRowsBasics
public import ComparisonActualHighWallSelectedMask

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.retained_grid (P : Q.Potential)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    let m:=Q.shiftedNativeModel
    let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
    (∀j,p j 0=Q.data.rmin) ∧ (∀j,p j (as j).length=1) ∧
    (∀j i,p j i∈Icc (0:ℝ) 1) ∧
    (∀j i,i<(as j).length→p j (i+1)-p j i ≤ mesh j/m.c) ∧
    Tendsto (fun j=>mesh j/m.c) atTop (𝓝 0) := by
  dsimp only
  let m:=Q.shiftedNativeModel
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    simpa only [partitionPoint,partitionValues_zero,id_eq] using m.R_before m.hu.1
  · intro j
    simpa only [partitionPoint_length,he j] using m.R_one
  · intro j i
    exact ⟨Q.data.hrbounds.1.le.trans (m.R_bounds _).1,(m.R_bounds _).2⟩
  · intro j i _
    exact Q.data.sampled_radius_step_le Q.alpha (as j) (ho j) (hm0 j) (hmesh j) i
  · simpa only [zero_div] using hlim.div_const m.c

theorem Potential.retainedRows_cell_eventually (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg r : ℝ}
    (hag : Q.data.rmin < ag) (hzg : zg ≤ 1) (hr : r∈Ioo ag zg) (hrD : r∉Dcuts)
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
    ⟨hag.trans hr.1,hr.2.trans_le hzg⟩ hrD hsel
  filter_upwards [HC,NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht
    (Ioo ag zg) isOpen_Ioo hr] with j hj hb
  obtain ⟨i,hi,hrow,hri⟩:=hj
  let ii : Fin ((sampleClockSteps m.q 0 (as j)).length+1):=
    ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hi⟩
  have hl:=hb i hi hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))
  have hu:=hb i hi hri (right_mem_Icc.mpr (hri.1.le.trans hri.2))
  have hs : m.u0 ≤ partitionPoint 0 (as j) i:=
    (m.R_high_mass (hag.trans hl.1)).le
  have hp : 0<pathMassDifferences (sampleClockSteps m.q 0 (as j)) 0 ii:=by
    rw [pathMassDifferences_eq_cutMass,
      physicalCutMass_sampleClockSteps m.q 0 (as j) i hi.le,
      physicalCutMass_sampleClockSteps m.q 0 (as j) (i+1) (by omega),sub_pos]
    by_contra hn
    exact (not_lt_of_ge (m.R_monotone (le_of_not_gt hn))) (hri.1.trans_le hri.2)
  exact ⟨ii,(P.retainedRows_mem c Dcuts ag zg (as j) ii).mpr
    ⟨hi,hrow,hp,hs,hl.1.le,hu.2.le⟩,hi,hri⟩

def Potential.extendedH (P : Q.Potential) (r : ℝ) : ℝ :=
  P.H (projIcc Q.data.rmin 1 Q.data.hr r)

theorem Potential.extendedH_continuous (P : Q.Potential) : Continuous P.extendedH :=
  by
    have HC : ContinuousOn P.H (Icc Q.data.rmin 1):=by simpa only [uIcc_of_le Q.data.hr] using P.hH.continuousOn
    exact (continuousOn_iff_continuous_domRestrict.mp HC).comp continuous_projIcc

theorem Potential.extendedH_eq (P : Q.Potential) {r : ℝ} (hr : r∈Icc Q.data.rmin 1) :
    P.extendedH r=P.H r := by simp only [extendedH,projIcc_of_mem _ hr]

theorem Potential.retainedSupport_measurable (P : Q.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval Q P) {ag zg : ℝ} (hag : Q.data.rmin ≤ ag) (hzg : zg ≤ 1) :
    MeasurableSet (P.retainedSupport c ag zg) := by
  have HE : P.retainedSupport c ag zg=
      Ioo ag zg∩NativeSelectedMask.fixedSupport (fun t=>(c t).left) (fun t=>(c t).right) P.extendedH := by
    ext r
    by_cases hr : r∈Ioo ag zg
    · simp only [retainedSupport,mem_inter_iff,hr,true_and,NativeSelectedMask.fixedSupport,
        mem_ofPred_eq,P.extendedH_eq ⟨hag.trans hr.1.le,hr.2.le.trans hzg⟩]
    · simp only [retainedSupport,mem_inter_iff,hr,false_and]
  rw [HE]
  exact comparisonConstructedSupport_measurable _ _ _ P.extendedH_continuous.continuousOn
    (Q.data.hrbounds.1.le.trans hag) hzg

theorem Potential.retainedRows_support_eventually (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg r : ℝ}
    (hag : Q.data.rmin < ag) (hzg : zg ≤ 1)
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
    · filter_upwards [P.retainedRows_cell_eventually c Dcuts as mesh ho he hmesh hm0 hlim
        hag hzg hband hrD hsel] with j hj
      obtain ⟨i,hi,_,hri⟩:=hj
      exact ⟨fun _=>⟨hband,hsel⟩,fun _=>⟨i,hi,hri⟩⟩
    · obtain ⟨_,_,hp,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
      have hselExt : r∉NativeSelectedMask.fixedSupport (fun t=>(c t).left)
          (fun t=>(c t).right) P.extendedH := by
        simpa only [NativeSelectedMask.fixedSupport,mem_ofPred_eq,
          P.extendedH_eq ⟨hag.le.trans hband.1.le,hband.2.le.trans hzg⟩] using hsel
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

theorem Potential.retainedRows_support_ae (P : Q.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ}
    (hag : Q.data.rmin < ag) (hzg : zg ≤ 1) :
    let m:=Q.shiftedNativeModel
    ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i))
        (P.retainedRows c Dcuts ag zg (as j)) ↔ r∈P.retainedSupport c ag zg) := by
  dsimp only
  have hD : ∀ᵐr : ℝ,r∉Dcuts:=by apply ae_iff.mpr;simpa using Dcuts.measure_zero volume
  have hz : ∀ᵐr : ℝ,∀t,r≠(c t).right:=ae_all_iff.mpr (fun t=>volume.ae_ne _)
  filter_upwards [ae_restrict_of_ae hD,ae_restrict_of_ae hz,
    ae_restrict_of_ae (volume.ae_ne ag),ae_restrict_of_ae (volume.ae_ne zg)] with r hrD hrz hra hrb
  exact P.retainedRows_support_eventually c Dcuts as mesh ho he hmesh hm0 hlim hag hzg hrD hrz hra hrb
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
