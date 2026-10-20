module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs
public import ComparisonActualQIntermediateDyadCountDirectDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem eq7_inner_post_dyad_card_le_log (h : ℝ)
    (hN : 1 ≤ Q.data.N) (hlog : 1 ≤ Real.log Q.data.N) :
    (Fintype.card (Eq7InnerPostDyad Q h) : ℝ) ≤
      (1/Real.log 2+2)*Real.log Q.data.N := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  let f : Eq7InnerPostDyad Q h → comparisonMassDyadicIndices U :=
    fun j => j.val.val
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hsub : Fintype.card (Eq7InnerPostDyad Q h) ≤
      Fintype.card (comparisonMassDyadicIndices U) :=
    Fintype.card_le_of_injective f hf
  have hcount : (comparisonMassDyadicIndices U).card ≤
      Nat.ceil (Real.log (1/U)/Real.log 2)+1 :=
    (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have H : (Fintype.card (Eq7InnerPostDyad Q h) : ℝ) ≤
      (Nat.ceil (Real.log (1/U)/Real.log 2):ℝ)+1 := by
    exact_mod_cast hsub.trans (by simpa only [Fintype.card_coe] using hcount)
  exact H.trans (by simpa only [U] using Q.intermediate_mass_log_count_le hN hlog)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
