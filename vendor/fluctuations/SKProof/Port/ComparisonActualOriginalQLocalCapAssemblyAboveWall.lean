module

public import SKProof.Port.ComparisonActualOriginalQLocalCapThermalAboveWall
public import SKProof.Port.ComparisonActualOriginalQLocalCapAssembly
public import SKProof.Port.ComparisonActualOriginalQLocalOrdinaryCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.local_finite_cap_thermal_le_dyadic_sum_above_wall (P : a.Potential)
    {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P)
    (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1)
    {lo hi : ℝ} (hU : a.data.U≤lo) (hstart : 32*a.data.s<lo) (hwall : 8*a.positiveOriginMassCoverBase<lo)
    (hscale : ∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)).indicator
      (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤
      2*(∑j:LocalCompleteMassDyad a lo hi,∫u in 0..1,
        (P.ordinaryGroup c A 16 j.val).indicator (fun _=>1)
          (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)+
      (∑p:RelevantBroadSlice c A,∫u in 0..1,(actualBroadSlice c p.val).indicator
        (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) := by
  have hf:=local_finite_cap_thermal_cover_above_wall c A hA hAD lo
    (fun r hr=>(hscale r hr).1) hwall
  have hc:=a.shiftedNativeModel.thermal_mask_le_finite_cover (A∩P.contactSet)
    (hA.inter P.contactSet_measurable)
    (fun j:LocalCompleteMassDyad a lo hi=>P.ordinaryGroup c A 16 j.val)
    (fun j=>P.ordinaryGroup_measurable c A 16 j.val)
    (P.contact_mem_ordinary_group c A hAD hU hstart hscale)
  have ho:=a.shiftedNativeModel.thermal_mask_le_finite_cover (relevantComparableCapUnion c A)
    (MeasurableSet.iUnion (fun _=>measurableSet_Ioo))
    (fun j:LocalCompleteMassDyad a lo hi=>P.ordinaryGroup c A 16 j.val)
    (fun j=>P.ordinaryGroup_measurable c A 16 j.val)
    (P.relevant_comparable_mem_ordinary_group c A hscale)
  linarith

theorem Potential.local_cap_contact_thermal_of_finite_budgets_above_wall (P : a.Potential)
    (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1)
    {lo hi O B : ℝ} (hU : a.data.U≤lo) (hstart : 32*a.data.s<lo) (hwall : 8*a.positiveOriginMassCoverBase<lo) (hO : 0≤O) (hB : 0≤B)
    (hscale : ∀r∈A,lo≤a.alpha.val.val r ∧ a.alpha.val.val r≤hi)
    (hOrd : ∀F:Finset (ordConnectedSection P.negativeSet),∀j:LocalCompleteMassDyad a lo hi,
      (∫u in 0..1,(P.ordinaryGroup (P.capFamily F) A 16 j.val).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤O)
    (hBroad : ∀F:Finset (ordConnectedSection P.negativeSet),∀p:RelevantBroadSlice (P.capFamily F) A,
      (∫u in 0..1,(actualBroadSlice (P.capFamily F) p.val).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤B) :
    (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator (fun _=>1)
      (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤
      (2*O+4*B)*(Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1) := by
  obtain ⟨F,_,_,hlim⟩:=P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  have HF:=P.local_finite_cap_thermal_le_dyadic_sum_above_wall (P.capFamily (F j)) A hA hAD hU hstart hwall hscale
  have HO:=Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hOrd (F j) p)
  have HB:=Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hBroad (F j) p)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at HO HB
  have hcountO : (Fintype.card (LocalCompleteMassDyad a lo hi):ℝ)≤
      Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1:=by
    exact_mod_cast local_complete_mass_dyad_card_le_log (a:=a) lo hi
  have hcountB : (Fintype.card (RelevantBroadSlice (P.capFamily (F j)) A):ℝ)≤
      4*(Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1):=by
    exact_mod_cast relevant_broad_slice_card_le_original_log (P.capFamily (F j)) A
      (P.capFamily_disjoint (F j))
  have hmulO:=mul_le_mul_of_nonneg_right hcountO hO
  have hmulB:=mul_le_mul_of_nonneg_right hcountB hB
  nlinarith

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
