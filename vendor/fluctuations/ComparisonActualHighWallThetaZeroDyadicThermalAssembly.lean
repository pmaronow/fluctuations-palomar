module

public import ComparisonActualHighWallThetaZeroCapExhaustion
public import ComparisonActualHighWallThetaZeroOrdinaryCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem local_mass_dyad_card_le_log
    (Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (lo hi : ℝ) :
    Fintype.card (LocalShiftedMassDyad Q lo hi)≤
      Nat.ceil (Real.log (1/comparisonSmallMass Q.data.N Q.data.E)/Real.log 2)+1 := by
  have H : Fintype.card (LocalShiftedMassDyad Q lo hi)≤
      Fintype.card (comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)):=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have HH : (comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)).card≤
      Nat.ceil (Real.log (1/comparisonSmallMass Q.data.N Q.data.E)/Real.log 2)+1:=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  exact H.trans (by simpa only [Fintype.card_coe] using HH)

theorem Potential.outer_cap_contact_thermal_of_finite_group_budgets
    {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo Q.data.rmin 1)
    {lo hi K O : ℝ} (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : Q.cavityCapTravel≤ Q.xs) (houter : 2*cu*(Az+1)*Q.xs≤ lo)
    (hU : comparisonSmallMass Q.data.N Q.data.E≤(cl/(2*cu))*lo)
    (hstart : 2*Q.data.s≤(cl/(4*cu))*lo) (hK : 4≤ K) (hKcap : 4*cu/cl≤ K)
    (hscale : ∀r∈A,lo≤ Q.alpha.val.val r ∧ Q.alpha.val.val r≤ hi) (hO : 0≤ O)
    (hOrd : ∀F : Finset (ordConnectedSection P.negativeSet),∀j : LocalShiftedMassDyad Q lo hi,
      (∫u in 0..1,(P.ordinaryGroup (P.capFamily F) A K j.val).indicator
        (fun _=>1) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)≤ O) :
    (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
      (fun _=>1) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)≤
      O*(Nat.ceil (Real.log (1/comparisonSmallMass Q.data.N Q.data.E)/Real.log 2)+1) := by
  obtain ⟨F,_,_,hlim⟩:=P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  have H:=P.outer_finite_cap_thermal_le_ordinary_sum (P.capFamily (F j)) A hA hAD
    hcl hcu hAz htravel houter hU hstart hK hKcap hscale
  have HS:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hOrd (F j) i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at HS
  have HC : (Fintype.card (LocalShiftedMassDyad Q lo hi):ℝ)≤
      Nat.ceil (Real.log (1/comparisonSmallMass Q.data.N Q.data.E)/Real.log 2)+1:=by
    exact_mod_cast local_mass_dyad_card_le_log Q lo hi
  exact H.trans (HS.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right HC hO))

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
