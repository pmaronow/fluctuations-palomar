module

public import ComparisonActualHighWallSelectedCapEndpoints
public import ComparisonShiftedNativeColumnAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.retained_contact_witness_eventually (P : a.Potential)
    {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) (Ks : ℕ→ℕ)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (as j)).length+1)))
    (unit : (j : ℕ)→Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (as j)).length+1)→Fin (Ks j))
    (hJ : ∀j,J j⊆P.retainedRows c Dcuts ag zg (as j))
    (hclass : ∀j,∀i∈J j,∀k∈J j,unit j k=unit j i→
      wholeUnit P.negativeSet (a.shiftedNativeModel.rowRadius (as j) k)=
        wholeUnit P.negativeSet (a.shiftedNativeModel.rowRadius (as j) i))
    {r : ℝ} (hHr : P.H r=0) (hra : ∀t,r≠(c t).left) (hrz : ∀t,r≠(c t).right)
    (hcell : ∀ᶠj in atTop,r∈NativeSelectedMask.finiteSupport
      (fun i=>a.shiftedNativeModel.R (partitionPoint 0 (as j) i)) (J j)) :
    ∀ᶠj in atTop,a.shiftedNativeModel.contactCellWitness (as j) (J j) (unit j)
      P.H P.negativeSet r := by
  let m:=a.shiftedNativeModel
  let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
  have hout:=NativeSelectedMask.contact_cells_eventually_outside_retained
    (fun t=>(c t).left) (fun t=>(c t).right) P.H (fun t=>(c t).negative)
    p (fun j=>(as j).length) _ hdiam ht hHr hra hrz
  filter_upwards [hcell,hout] with j hj houtj
  obtain ⟨i,hi,hri⟩:=hj
  have hid:=(P.retainedRows_mem c Dcuts ag zg (as j) i).mp (hJ j hi)
  refine ⟨i,hi,hid.1,hri,?_⟩
  intro hiU k hk hki
  have hkd:=(P.retainedRows_mem c Dcuts ag zg (as j) k).mp (hJ j hk)
  have hsame : wholeUnit P.negativeSet (p j k.val)=wholeUnit P.negativeSet (p j i.val):=by
    have HC:=hclass j i hi k hk hki
    change wholeUnit P.negativeSet (m.rowRadius (as j) k)=wholeUnit P.negativeSet (m.rowRadius (as j) i) at HC
    simpa only [m.rowRadius_eq_partitionPoint] using HC
  have H:=NativeSelectedMask.same_unit_row_meets_contact
    (fun t=>(c t).left) (fun t=>(c t).right) P.H P.negativeSet (p j) Dcuts hwhole
    (show NativeSelectedMask.rowSelected (fun t=>(c t).left) (fun t=>(c t).right)
      P.H id (p j) Dcuts k.val from hkd.2.1) (houtj i.val hid.1 hri) hsame
  change ∃t∈Icc (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 (as j)) k.val))
    (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 (as j)) (k.val+1))),P.H t=0
  rw [physicalCutMass_sampleClockSteps m.q 0 (as j) k.val hkd.1.le,
    physicalCutMass_sampleClockSteps m.q 0 (as j) (k.val+1) (by omega)]
  exact H

theorem Potential.retainedBin_column_geometry (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : a.data.rmin< ag) (hzg : zg≤1)
    (hleft : ∀t,ag≤(c t).left) (hright : ∀t,(c t).right≤ zg)
    (bins : ℕ) (hbins : 0< bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (labels : ι→Fin bins)
    (hlabels : ∀j t,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=labels t)
    (b : Fin bins) (l u : ℝ)
    (hgeom : ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>a.shiftedNativeModel.R (partitionPoint 0 (as j) i))
        (P.retainedBin c Dcuts ag zg (as j) bins (w j) b) ↔r∈P.retainedSupport c ag zg∩Ioo l u)) :
    let m:=a.shiftedNativeModel
    let J:=fun j=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
    let C:=fun j=>P.retainedBinCoordinates c Dcuts ag zg (as j) (ho j) bins (w j) b
    let A:=(Ioo ag zg∩P.contactSet)∩Ioo l u
    (∀ᵐr∂volume.restrict A,∀ᶠj in atTop,m.contactCellWitness (as j) (J j) (C j).unit P.H P.negativeSet r) ∧
    (∀ᵐr∂volume.restrict (Ioo ag zg),∀t : {t : ι //labels t=b},r∈Ioo (c t.val).left (c t.val).right→
      ∀ᶠj in atTop,∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),i∈J j∧i.val<(as j).length∧
        (C j).unit i=(C j).unit (P.retainedCapFirst c Dcuts ag zg (as j) bins (w j) t.val b)∧
        r∈Ioc (m.R (partitionPoint 0 (as j) i.val)) (m.R (partitionPoint 0 (as j) (i.val+1)))) ∧
    (∀ᵐr∂volume.restrict (Ioo ag zg),(∀t : {t : ι //labels t=b},r∉Ioo (c t.val).left (c t.val).right)→
      r∉A→Tendsto (fun j=>m.unitColumn (as j) (J j) (C j).unit (fun _=>1) r) atTop (𝓝 0)) := by
  dsimp only
  let m:=a.shiftedNativeModel
  let J:=fun j=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
  let C:=fun j=>P.retainedBinCoordinates c Dcuts ag zg (as j) (ho j) bins (w j) b
  let A:=(Ioo ag zg∩P.contactSet)∩Ioo l u
  let F:=P.retainedSupport c ag zg∩Ioo l u
  have hA : MeasurableSet A:=(measurableSet_Ioo.inter P.contactSet_measurable).inter measurableSet_Ioo
  have hband : Ioo ag zg⊆Ioo (0:ℝ) 1:=fun r hr=>
    ⟨a.data.hrbounds.1.le.trans_lt (hag.trans hr.1),hr.2.trans_le hzg⟩
  have hindex j i (hi:i∈J j) := ((P.retainedRows_mem c Dcuts ag zg (as j) i).mp
    (P.retainedBin_subset c Dcuts ag zg (as j) bins (w j) b hi)).1
  have hD : ∀ᵐr : ℝ,r∉Dcuts:=by apply ae_iff.mpr;simpa using Dcuts.measure_zero volume
  have hga : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔r∈F):=
    ae_mono (Measure.restrict_mono hband le_rfl) hgeom
  refine ⟨?_,?_,?_⟩
  · have hAA : A⊆Ioo (0:ℝ) 1:=fun r hr=>hband hr.1.1
    have hgeomA:=ae_mono (Measure.restrict_mono hAA le_rfl) hgeom
    have hla : ∀ᵐr : ℝ,∀t,r≠(c t).left:=ae_all_iff.mpr (fun t=>volume.ae_ne _)
    have hlz : ∀ᵐr : ℝ,∀t,r≠(c t).right:=ae_all_iff.mpr (fun t=>volume.ae_ne _)
    filter_upwards [hgeomA,ae_restrict_mem hA,ae_restrict_of_ae hla,ae_restrict_of_ae hlz] with r hr hrA hra hrz
    apply P.retained_contact_witness_eventually c hwhole Dcuts ag zg as mesh ho he hmesh hm0 hlim
      (fun j=>(C j).K) J (fun j=>(C j).unit)
      (fun j=>P.retainedBin_subset c Dcuts ag zg (as j) bins (w j) b)
      (fun j i hi k hk hki=>((C j).classes k hk i hi).mp hki)
      hrA.1.2.2 hra hrz
    exact hr.mono (fun j hj=>hj.mpr ⟨⟨hrA.1.1,Or.inr hrA.1.2.2⟩,hrA.2⟩)
  · filter_upwards [ae_restrict_of_ae hD] with r hrD
    intro t hrt
    have hlabel j:=(hlabels j t.val).trans t.property
    filter_upwards [P.retainedCapRows_cell_eventually c Dcuts as mesh ho he hmesh hm0 hlim
      hag hzg bins hbins w hwhole t.val b hlabel (hleft t.val) (hright t.val) hrt hrD] with j hj
    obtain ⟨i,hi,hil,hri⟩:=hj
    have hc:=Finset.mem_filter.mp hi
    have hu:=P.retainedCap_unit_class_iff c Dcuts ag zg (as j) (ho j) bins (w j) hwhole t.val b
      ⟨i,hi⟩ i hc.1
    exact ⟨i,hc.1,hil,hu.mpr hc.2,hri⟩
  · have hp:=(m.binary_column_L1_of_support_eventually as ho (fun j=>(C j).K) J
      (fun j=>(C j).unit) hindex F hga).1
    filter_upwards [hp,hga,ae_restrict_of_ae hD,ae_restrict_mem measurableSet_Ioo] with r hrp hrg hrD hrband
    intro hncap hnA
    have hnF : r∉F:=by
      intro hrF
      rcases hrF.1.2 with ⟨t,hrt⟩|hrzero
      · have hc:=P.retainedBin_cap_support_eventually c Dcuts as mesh ho he hmesh hm0 hlim
          hag hzg hleft hright bins hbins w hwhole labels hlabels t b hrt hrD
        have HL : ∀ᶠj : ℕ in atTop,labels t=b:=by
          filter_upwards [hrg,hc] with j hj hcap
          exact hcap.mp (hj.mpr hrF)
        exact hncap ⟨t,HL.exists.choose_spec⟩ hrt
      · exact hnA ⟨⟨hrF.1.1,⟨⟨hag.le.trans hrband.1.le,hrband.2.le.trans hzg⟩,hrzero⟩⟩,hrF.2⟩
    simpa only [Set.indicator_of_notMem hnF] using hrp

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
