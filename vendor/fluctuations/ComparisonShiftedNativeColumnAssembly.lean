module

public import ComparisonShiftedNativeContactColumnConvergence
public import ComparisonShiftedNativeSideColumnLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 16000000
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem sideColumn_full_L1_from_uniform_cumulative (hr0 : 0≤ m.rmin) {τ : Type*}
    [Fintype τ] [DecidableEq τ]
    {ag zg δ : ℝ} (hag : m.rmin < ag) (hzg : zg ≤ 1) (hδ : 0 < δ)
    (A : Set ℝ) (hA : MeasurableSet A) (hAband : A ⊆ Ioo ag zg)
    (H : ℝ → ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U ⊆ Icc m.rmin 1)
    (hneg : ∀r ∈ U,H r < 0)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hmeshlim : Tendsto mesh atTop (𝓝 0)) (K : ℕ → ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hhigh : ∀j,∀i∈J j,m.u0≤ partitionPoint 0 (as j) i.val)
    (unit : ∀j,Fin ((sampleClockSteps m.q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (hstart : ∀j,x j 0=0)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),
      physicalSelectedUnitMass (sampleClockSteps m.q 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set (Fin ((sampleClockSteps m.q 0 (as j)).length+1))))
    (hwidths : ∀j,2*δ ≤ x j (K j)) (hwidthMax : ∀j,x j (K j) ≤ 1)
    (hpos : ∀j,∀i ∈ J j,0 < pathMassDifferences (sampleClockSteps m.q 0 (as j)) 0 i)
    (hclass : ∀jnet,∀i ∈ J jnet,∀j ∈ J jnet,unit jnet i=unit jnet j ↔
      WholeUnitSideKernel.wholeUnit U (m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 (as jnet)) i.val))=
      WholeUnitSideKernel.wholeUnit U (m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 (as jnet)) j.val)))
    (hcell : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      m.contactCellWitness (as j) (J j) (unit j) H U r)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>m.selectedCDF (as j) (ho j) (J j)) atTop (𝓝 f))
    (a z l rr : τ → ℝ) (capUnit : ∀j,τ → Fin (K j))
    (hlr : ∀i,l i < rr i)
    (hleft : ∀i,Tendsto (fun j=>x j (capUnit j i).val) atTop (𝓝 (l i)))
    (hright : ∀i,Tendsto (fun j=>x j ((capUnit j i).val+1)) atTop (𝓝 (rr i)))
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (a i) (z i)) (Ioo (a j) (z j))))
    (hcontact : ∀i,Disjoint (Ioo (a i) (z i)) A)
    (hcapcell : ∀ᵐ r ∂volume.restrict (Ioo ag zg),∀t,r ∈ Ioo (a t) (z t) →
      ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),
        i ∈ J j ∧ i.val < (as j).length ∧ unit j i=capUnit j t ∧
        r ∈ Ioc (m.R (partitionPoint 0 (as j) i.val))
          (m.R (partitionPoint 0 (as j) (i.val+1))))
    (hoff : ∀ᵐ r ∂volume.restrict (Ioo ag zg),(∀t,r ∉ Ioo (a t) (z t)) → r ∉ A →
      Tendsto (fun j=>m.unitColumn (as j)
        (J j) (unit j) (fun _=>1) r) atTop (𝓝 0)) :
    let width := f ⟨1,by simp⟩
    let w := fun r=>pointSideColumn δ width (comparisonContactLimitCoordinate f r)
    let moving := fun j=>m.unitColumn (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val)
    let fixed := fixedCapContactWeight a z (fun i=>sideSquareColumnLR δ width (l i) (rr i)) A w
    Tendsto (fun j=>x j (K j)) atTop (𝓝 width) ∧ 2*δ ≤ width ∧
    (∀ᵐ r ∂volume.restrict (Ioo ag zg),Tendsto (fun j=>moving j r) atTop (𝓝 (fixed r))) ∧
    Tendsto (fun j=>∫r in Ioo ag zg,|moving j r-fixed r|) atTop (𝓝 0) ∧
    Tendsto (fun j=>∫r in Ioo ag zg,
      |deriv m.alpha.val.val r*moving j r-deriv m.alpha.val.val r*fixed r|) atTop (𝓝 0) ∧
    (∫r in A,deriv m.alpha.val.val r*w r) ≤ 2*Real.log (width/δ) := by
  dsimp only
  have hnative := m.contactColumn_convergence_of_uniform_cumulative hr0 hag hzg hδ A hA hAband H hopen hU hneg as mesh ho hend
    hmesh hmeshlim K J hhigh unit x hstart hx hmass horder hwidths hpos hclass hcell f huniform
  dsimp only at hnative
  have hcontactpoint : ∀ᵐ r ∂volume.restrict (Ioo ag zg),r ∈ A →
      Tendsto (fun j=>m.unitColumn (as j)
        (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val) r)
        atTop (𝓝 (pointSideColumn δ (f ⟨1,by simp⟩) (comparisonContactLimitCoordinate f r))) :=
    ae_mono Measure.restrict_le_self ((ae_restrict_iff' hA).mp hnative.2.2.1)
  have hfull := m.sideColumn_full_L1_of_geometry as ho
    K J unit x (fun j=>x j (K j)) capUnit hδ hnative.2.1 hag hzg hstart (fun _=>rfl)
    hwidths hwidthMax hx hnative.1 a z l rr hlr hleft hright A
    (fun r=>pointSideColumn δ (f ⟨1,by simp⟩) (comparisonContactLimitCoordinate f r))
    hdisjoint hcontact (by
      filter_upwards [hcapcell,hcontactpoint,hoff] with r hcap hcon hout
      exact ⟨hcap,hcon,hout⟩)
  exact ⟨hnative.1,hnative.2.1,hfull.1,hfull.2.1,hfull.2.2,hnative.2.2.2.2⟩

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
