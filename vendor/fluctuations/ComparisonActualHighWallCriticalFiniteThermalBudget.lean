module

public import ComparisonActualHighWallCriticalLocalCapThermalCover
public import ComparisonActualHighWallCriticalLocalOrdinaryCover
public import ComparisonActualHighWallCriticalBroadDyadicCount

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.critical_finite_cap_thermal_le_budget
    (P : a.Potential) {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval a P) (A : Set ℝ)
    (hA : MeasurableSet A) (hAD : A ⊆ Ioo a.data.rmin 1)
    {lo hi O B : ℝ} (hU : comparisonSmallMass a.data.N a.data.E ≤ lo)
    (hstart : 32*a.data.s < lo)
    (hscale : ∀ r ∈ A, lo ≤ a.alpha.val.val r ∧ a.alpha.val.val r ≤ hi)
    (hOrd : ∀ j : CriticalCompleteMassDyad a lo hi,
      (∫ u in 0..1, (P.ordinaryGroup c A 16 j.val).indicator
        (fun _ => 1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤ O)
    (hBroad : ∀ p : CriticalRelevantBroadSlice c A,
      (∫ u in 0..1, (actualCriticalBroadSlice c p.val).indicator
        (fun _ => 1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤ B) :
    (∫ u in 0..1, (A ∩ ((⋃ i, Ioo (c i).left (c i).right) ∪ P.contactSet)).indicator
      (fun _ => 1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      2*O*(Fintype.card (CriticalCompleteMassDyad a lo hi))+
      B*(Fintype.card (CriticalRelevantBroadSlice c A))+
      (∫ u in 0..min (8*a.criticalMassCoverBase) 1,
        a.shiftedNativeModel.thermal u) := by
  let m := a.shiftedNativeModel
  let J := CriticalCompleteMassDyad a lo hi
  let R := CriticalRelevantBroadSlice c A
  let contact := A ∩ P.contactSet
  let comp := criticalRelevantComparableCapUnion c A
  have hc : MeasurableSet contact := hA.inter P.contactSet_measurable
  have hcomp : MeasurableSet comp := MeasurableSet.iUnion (fun _ => measurableSet_Ioo)
  have hcontact :
      (∫ u in 0..1, contact.indicator (fun _ => 1) (m.R u)*m.thermal u) ≤
      ∑ j : J, ∫ u in 0..1, (P.ordinaryGroup c A 16 j.val).indicator
        (fun _ => 1) (m.R u)*m.thermal u :=
    m.thermal_mask_le_finite_cover contact hc
      (fun j : J => P.ordinaryGroup c A 16 j.val)
      (fun j => P.ordinaryGroup_measurable c A 16 j.val)
      (P.critical_contact_mem_ordinary_group c A hAD hU hstart hscale)
  have hcomparable :
      (∫ u in 0..1, comp.indicator (fun _ => 1) (m.R u)*m.thermal u) ≤
      ∑ j : J, ∫ u in 0..1, (P.ordinaryGroup c A 16 j.val).indicator
        (fun _ => 1) (m.R u)*m.thermal u :=
    m.thermal_mask_le_finite_cover comp hcomp
      (fun j : J => P.ordinaryGroup c A 16 j.val)
      (fun j => P.ordinaryGroup_measurable c A 16 j.val)
      (P.critical_relevant_comparable_mem_ordinary_group c A hscale)
  have hf := critical_local_finite_cap_thermal_cover c A hA
  have ho := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hOrd j)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hBroad p)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ho hb
  change (∫ u in 0..1, contact.indicator (fun _ => 1) (m.R u)*m.thermal u) ≤ _ at hcontact
  change (∫ u in 0..1, comp.indicator (fun _ => 1) (m.R u)*m.thermal u) ≤ _ at hcomparable
  have hOcount : (∑ j : J, ∫ u in 0..1, (P.ordinaryGroup c A 16 j.val).indicator
      (fun _ => 1) (m.R u)*m.thermal u) ≤ O*(Fintype.card J) := by
    exact ho.trans_eq (mul_comm (Fintype.card J : ℝ) O)
  have hBcount : (∑ p : R, ∫ u in 0..1, (actualCriticalBroadSlice c p.val).indicator
      (fun _ => 1) (m.R u)*m.thermal u) ≤ B*(Fintype.card R) := by
    exact hb.trans_eq (mul_comm (Fintype.card R : ℝ) B)
  dsimp only [J, R, contact, comp, m] at hf hcontact hcomparable hOcount hBcount
  linarith only [hf, hcontact, hcomparable, hOcount, hBcount]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
