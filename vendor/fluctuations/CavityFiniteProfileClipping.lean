module

public import CavityAllDiagonalCancellation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

 theorem splitIndex_le_clockLength {as : List PositiveMass} (T : ClockTree S as)
    (s t : T.Slot) : T.splitIndex s t ≤ as.length := by
  induction T with
  | leaf => exact le_rfl
  | step a T ih => simpa only [splitIndex,List.length_cons,Nat.add_comm 1] using Nat.succ_le_succ (ih s t)
  | fork T V ihT ihV => cases s <;> cases t <;> first | exact ihT _ _ | exact ihV _ _ | exact Nat.zero_le _

 def clipDirection (N : ℕ) (D : ℕ → ι → ℝ) (j : ℕ) : ι → ℝ :=
   if j ≤ N then D j else 0

 theorem coordinateProfile_clip_below (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (N : ℕ) (D : ℕ → ι → ℝ) {j : ℕ} (hj : j ≤ N) :
    ReplicaTree.coordinateProfile φ (clipDirection N D) j = ReplicaTree.coordinateProfile φ D j := by
  funext σ τ
  simp only [ReplicaTree.coordinateProfile,clipDirection,if_pos hj]

 theorem coordinateProfile_clip_above (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (N : ℕ) (D : ℕ → ι → ℝ) {j : ℕ} (hj : ¬j ≤ N) :
    ReplicaTree.coordinateProfile φ (clipDirection N D) j = 0 := by
  funext σ τ
  simp only [ReplicaTree.coordinateProfile,clipDirection,if_neg hj,Pi.zero_apply,
    zero_mul,Finset.sum_const_zero]

 theorem disorderProfileJets_eq_clipDirections (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (Ds : List (ℕ → ι → ℝ))
    (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
      disorderProfileJets w φ v q x
        ((Ds.map (clipDirection as.length)).map (ReplicaTree.coordinateProfile φ)) T P := by
  induction Ds generalizing T with
  | nil => rfl
  | cons D Ds ih =>
    simp only [List.map_cons,disorderProfileJets]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    have Htest : profilePairTest P (ReplicaTree.coordinateProfile φ D) p r =
        profilePairTest P (ReplicaTree.coordinateProfile φ (clipDirection as.length D)) p r := by
      funext σ
      simp only [profilePairTest,coordinateProfile_clip_below φ as.length D
        (r.tree.splitIndex_le_clockLength _ _)]
    rw [ih r.tree,Htest]

 theorem disorderOffDiagonalJets_eq_clipDirections (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (Ds : List (ℕ → ι → ℝ))
    (T : ClockTree S as) (P : T.Assignment → ℝ) :
    disorderOffDiagonalJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P =
      disorderOffDiagonalJets w φ v q x
        ((Ds.map (clipDirection as.length)).map (ReplicaTree.coordinateProfile φ)) T P := by
  induction Ds generalizing T with
  | nil => rfl
  | cons D Ds ih =>
    simp only [List.map_cons,disorderOffDiagonalJets]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    have Htest : profilePairTest P (ReplicaTree.coordinateProfile φ D) p r =
        profilePairTest P (ReplicaTree.coordinateProfile φ (clipDirection as.length D)) p r := by
      funext σ
      simp only [profilePairTest,coordinateProfile_clip_below φ as.length D
        (r.tree.splitIndex_le_clockLength _ _)]
    rw [ih r.tree,Htest]

 theorem clipDirection_bounded (N : ℕ) (Ds : List (ℕ → ι → ℝ)) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀ D ∈ Ds, ∀ j, j ≤ N → ∀ i, |D j i| ≤ B) :
    ∀ D ∈ Ds.map (clipDirection N), ∀ j i, |D j i| ≤ B := by
  intro D hD j i
  obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hD
  by_cases hj : j ≤ N
  · simpa only [clipDirection,if_pos hj] using hDs L hL j hj i
  · simpa only [clipDirection,if_neg hj,Pi.zero_apply,abs_zero] using hB

end OAI.SKFluctuations.Hierarchy.ClockTree
