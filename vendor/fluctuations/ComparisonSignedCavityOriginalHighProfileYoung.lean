module

public import ComparisonSignedCavityGLongitudinalOriginalBudget
public import ComparisonSignedCavityActualResourceFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass}

theorem native_forkCost_young (T : ClockTree S as) (f : ℕ→ℝ) (z : ℝ) :
    2*z*T.forkCost f ≤ ((T.leaves:ℝ)-1)*z^2+T.forkCost (fun j=>(f j)^2) := by
  induction T generalizing f with
  | leaf=>simp [forkCost,leaves]
  | step b T ih=>simpa only [forkCost,leaves] using ih (fun j=>f (1+j))
  | fork T V ihT ihV=>
    have H:=sq_nonneg (z-f 0)
    simp only [forkCost,leaves,Nat.cast_add]
    nlinarith [ihT f,ihV f]

theorem native_edgeBudget_young (ho : MassOrdered 0 as) (f : ℕ→ℝ) (z : ℝ) :
    2*z*edgeBudget 0 as f ≤ z^2+edgeBudget 0 as (fun j=>(f j)^2) := by
  suffices H : ∀(a : ℝ) (bs : List PositiveMass),MassOrdered a bs →
      ∀f : ℕ→ℝ,2*z*edgeBudget a bs f ≤ (1-a)*z^2+edgeBudget a bs (fun j=>(f j)^2) by
    simpa only [sub_zero,one_mul] using H 0 as ho f
  intro a bs
  induction bs generalizing a with
  | nil=>
    intro ha f
    have H:=mul_nonneg (sub_nonneg.mpr ha.2) (sq_nonneg (z-f 0))
    simp only [edgeBudget]
    nlinarith
  | cons b bs ih=>
    intro ha f
    have H:=mul_nonneg (sub_nonneg.mpr ha.2.1) (sq_nonneg (z-f 0))
    have HI:=ih b.val ha.2.2 (fun j=>f (1+j))
    simp only [edgeBudget]
    nlinarith

theorem native_distinct_pair_profile_product_le (T : ClockTree S as)
    (ho : MassOrdered 0 as) (f : ℕ→ℝ) (s t : T.Slot) (hst : s≠t) :
    f (T.splitIndex s t)*(T.forkCost f+edgeBudget 0 as f) ≤
      ((T.leaves:ℝ)+1)*(T.forkCost (fun j=>(f j)^2)+edgeBudget 0 as (fun j=>(f j)^2)) := by
  let z:=f (T.splitIndex s t)
  have HF:=native_forkCost_young T f z
  have HE:=native_edgeBudget_young ho f z
  have HS:=T.split_le_forkCost (fun j=>sq_nonneg (f j)) s t hst
  have HL : 0 ≤ (T.leaves:ℝ):=Nat.cast_nonneg _
  have Hsq:=mul_le_mul_of_nonneg_left HS HL
  have HF2:=T.forkCost_nonneg (fun j=>sq_nonneg (f j))
  have HE2:=edgeBudget_nonneg ho (fun j=>sq_nonneg (f j))
  have Hextra:=mul_nonneg HL (add_nonneg HF2 HE2)
  dsimp only [z] at HF HE Hsq
  nlinarith

end OAI.SKFluctuations.Hierarchy.ClockTree
