module

public import ComparisonActualHighWallOrdinaryCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.capFamily
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (t : F) :
    ShiftedCapInterval a P where
  left:=NativeCapExhaustion.left P.negativeSet F t
  right:=NativeCapExhaustion.right P.negativeSet F t
  hleft:=(NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).1 t |>.1
  hlt:=(NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).1 t |>.2.1
  hright:=(NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).1 t |>.2.2
  negative:=by
    intro r hr
    have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
      (ordConnectedSection_subset t.val.property)
    exact (ordConnectedComponent_subset (HH.2.2.2.2.1.symm ▸ hr)).2

theorem Potential.capFamily_union
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) :
    (⋃t : F,Ioo (P.capFamily F t).left (P.capFamily F t).right)=wholeCapFiniteUnion P.negativeSet F := by
  ext r
  constructor
  · intro hr
    obtain ⟨t,ht⟩:=mem_iUnion.mp hr
    have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
      (ordConnectedSection_subset t.val.property)
    exact mem_iUnion₂.mpr ⟨t.val,t.property,HH.2.2.2.2.1.symm ▸ ht⟩
  · intro hr
    obtain ⟨t,ht,hr⟩:=mem_iUnion₂.mp hr
    have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
      (ordConnectedSection_subset t.property)
    exact mem_iUnion.mpr ⟨⟨t,ht⟩,HH.2.2.2.2.1 ▸ hr⟩

theorem Potential.capFamily_disjoint
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) :
    Pairwise (fun s t : F=>Disjoint (Ioo (P.capFamily F s).left (P.capFamily F s).right)
      (Ioo (P.capFamily F t).left (P.capFamily F t).right)) :=
  (NativeCapExhaustion.endpoints P.negativeSet_open P.negativeSet_subset F).2

theorem Potential.capFamily_contacts
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (t : F) :
    (P.H (P.capFamily F t).left=0 ∨ (P.capFamily F t).left=a.data.rmin) ∧
      (P.H (P.capFamily F t).right=0 ∨ (P.capFamily F t).right=1) := by
  obtain ⟨c,hl,hr,_,hcases⟩:=P.negative_component_endpoints
    (ordConnectedSection_subset t.val.property)
  change (P.H (sInf _)=0 ∨ sInf _=a.data.rmin) ∧ (P.H (sSup _)=0 ∨ sSup _=1)
  simpa only [hl,hr] using hcases

theorem Potential.cap_contact_thermal_exhaustion
    {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) :
    ∃F : ℕ→Finset (ordConnectedSection P.negativeSet),Monotone F ∧
      (∀t : ordConnectedSection P.negativeSet,∃j,t∈F j) ∧
      Tendsto (fun j=>∫u in 0..1,
        (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) atTop
        (𝓝 (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
          (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)) := by
  have hH : ContinuousOn P.H (Icc a.data.rmin 1):=by
    simpa only [uIcc_of_le a.data.hr] using P.hH.continuousOn
  obtain ⟨F,hF,hcover,hlim⟩:=a.shiftedNativeModel.cap_thermal_exhaustion P.negativeSet_open
    P.negativeSet_subset P.H hH A hA
  have hfixed j u :
      (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left P.negativeSet (F j))
        (NativeCapExhaustion.right P.negativeSet (F j)) P.H).indicator (fun _=>(1:ℝ))
          (a.shiftedNativeModel.R u)=
      (A∩((⋃t : F j,Ioo (P.capFamily (F j) t).left (P.capFamily (F j) t).right)∪P.contactSet)).indicator
        (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u):=by
    rw [NativeCapExhaustion.fixedSupport_eq P.negativeSet_open P.negativeSet_subset,
      P.capFamily_union (F j)]
    have hr:=a.shiftedNativeModel.R_bounds u
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,hr,true_and]
  have hfull u :
      (A∩(P.negativeSet∪{r | P.H r=0})).indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)=
      (A∩(P.negativeSet∪P.contactSet)).indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u):=by
    have hr:=a.shiftedNativeModel.R_bounds u
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,contactSet,
      mem_preimage,mem_singleton_iff,hr,true_and]
  simp_rw [hfixed,hfull] at hlim
  exact ⟨F,hF,hcover,hlim⟩

theorem local_mass_dyad_card_le_log
    (a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock) (lo hi : ℝ) :
    Fintype.card (LocalShiftedMassDyad a lo hi)≤
      Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1 := by
  have H : Fintype.card (LocalShiftedMassDyad a lo hi)≤
      Fintype.card (comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E)):=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have HH : (comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E)).card≤
      Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1:=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  exact H.trans (by simpa only [Fintype.card_coe] using HH)

theorem Potential.outer_cap_contact_thermal_of_finite_group_budgets
    {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo a.data.rmin 1)
    {lo hi K O : ℝ} (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : a.cavityCapTravel≤ a.xs) (houter : 2*cu*(Az+1)*a.xs≤ lo)
    (hU : comparisonSmallMass a.data.N a.data.E≤(cl/(2*cu))*lo)
    (hstart : 2*a.data.s≤(cl/(4*cu))*lo) (hK : 4≤ K) (hKcap : 4*cu/cl≤ K)
    (hscale : ∀r∈A,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) (hO : 0≤ O)
    (hOrd : ∀F : Finset (ordConnectedSection P.negativeSet),∀j : LocalShiftedMassDyad a lo hi,
      (∫u in 0..1,(P.ordinaryGroup (P.capFamily F) A K j.val).indicator
        (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤ O) :
    (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
      (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤
      O*(Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1) := by
  obtain ⟨F,_,_,hlim⟩:=P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  have H:=P.outer_finite_cap_thermal_le_ordinary_sum (P.capFamily (F j)) A hA hAD
    hcl hcu hAz htravel houter hU hstart hK hKcap hscale
  have HS:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hOrd (F j) i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at HS
  have HC : (Fintype.card (LocalShiftedMassDyad a lo hi):ℝ)≤
      Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1:=by
    exact_mod_cast local_mass_dyad_card_le_log a lo hi
  exact H.trans (HS.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right HC hO))

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
