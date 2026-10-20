module

public import ComparisonSignedCavityMixedForest

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

def nativeFreshAtSlot : {as : List PositiveMass} → (T : ClockTree S as) →
    ℝ → T.Slot → ℕ → MarkedPlacement T
  | _,.leaf,a,_,_ => MarkedPlacement.fresh .leaf (a-1)
  | _,.step b T,a,_,0 => MarkedPlacement.fresh (T.step b) (a-b.val)
  | _,.step b T,_,s,j+1 => (nativeFreshAtSlot T b.val s j).step b
  | _,.fork T V,a,_,0 => MarkedPlacement.fresh (T.fork V) (-a)
  | _,.fork T V,a,s,j+1 => match (s : T.Slot ⊕ V.Slot) with
    | Sum.inl c => (nativeFreshAtSlot T a c (j+1)).left V
    | Sum.inr c => (nativeFreshAtSlot V a c (j+1)).right T

theorem nativeFreshAtSlot_mem {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (j : ℕ) : nativeFreshAtSlot T a s j ∈ T.markedAttach a := by
  induction T generalizing a j with
  | leaf => exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)
  | step b T ih =>
    cases j with
    | zero => exact List.mem_cons_self
    | succ j => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_,ih b.val s j,rfl⟩)
  | fork T V ihT ihV =>
    cases j with
    | zero => exact List.mem_cons_self
    | succ j => cases s with
      | inl s => exact List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_map.mpr ⟨_,ihT a s (j+1),rfl⟩))
      | inr s => exact List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_map.mpr ⟨_,ihV a s (j+1),rfl⟩))

theorem nativeFreshAtSlot_old_splits {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (j : ℕ) :
    Function.Injective (nativeFreshAtSlot T a s j).embed ∧
      ∀ c d,(nativeFreshAtSlot T a s j).tree.splitIndex
        ((nativeFreshAtSlot T a s j).embed c) ((nativeFreshAtSlot T a s j).embed d)=T.splitIndex c d :=
  T.markedAttach_embed_preserves a _ (nativeFreshAtSlot_mem T a s j)

theorem nativeFreshAtSlot_distinct {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (j : ℕ) (c : T.Slot) :
    (nativeFreshAtSlot T a s j).mark ≠ (nativeFreshAtSlot T a s j).embed c := by
  induction T generalizing a j with
  | leaf => exact Sum.inr_ne_inl
  | step b T ih =>
    cases j with
    | zero => exact Sum.inr_ne_inl
    | succ j => exact ih b.val s j c
  | fork T V ihT ihV =>
    cases j with
    | zero => exact Sum.inr_ne_inl
    | succ j => cases s with
      | inl s => cases c with
        | inl c => exact fun he=>ihT a s (j+1) c (Sum.inl.inj he)
        | inr c => exact Sum.inl_ne_inr
      | inr s => cases c with
        | inl c => exact Sum.inr_ne_inl
        | inr c => exact fun he=>ihV a s (j+1) c (Sum.inr.inj he)

theorem nativeFreshAtSlot_split {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (j : ℕ) (c : T.Slot) :
    (nativeFreshAtSlot T a s j).tree.splitIndex
      (nativeFreshAtSlot T a s j).mark ((nativeFreshAtSlot T a s j).embed c)=
      min j (T.splitIndex s c) := by
  induction T generalizing a j with
  | leaf => simp only [nativeFreshAtSlot,MarkedPlacement.fresh,splitIndex,
      Sum.elim_inr,Sum.elim_inl,Nat.min_zero]
  | step b T ih =>
    cases j with
    | zero => simp only [nativeFreshAtSlot,MarkedPlacement.fresh,splitIndex,
        Sum.elim_inr,Sum.elim_inl,Nat.zero_min]
    | succ j =>
      change 1+(nativeFreshAtSlot T b.val s j).tree.splitIndex
        (nativeFreshAtSlot T b.val s j).mark ((nativeFreshAtSlot T b.val s j).embed c)=
          min (j+1) (1+T.splitIndex s c)
      rw [ih b.val s j c]
      omega
  | fork T V ihT ihV =>
    cases j with
    | zero => simp only [nativeFreshAtSlot,MarkedPlacement.fresh,splitIndex,
        Sum.elim_inr,Sum.elim_inl,Nat.zero_min]
    | succ j => cases s with
      | inl s => cases c with
        | inl c => exact ihT a s (j+1) c
        | inr c => simp only [nativeFreshAtSlot,MarkedPlacement.left,splitIndex,
            Sum.map_inr,Sum.elim_inl,Sum.elim_inr,Nat.min_zero]
      | inr s => cases c with
        | inl c => simp only [nativeFreshAtSlot,MarkedPlacement.right,splitIndex,
            Sum.map_inl,Sum.elim_inl,Sum.elim_inr,Nat.min_zero]
        | inr c => exact ihV a s (j+1) c

theorem nativeFreshAtSlot_outside_old_blocks {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (s : T.Slot) {star U : ℕ} (hstar : star<U)
    (c : T.Slot) :
    (nativeFreshAtSlot T a s star).tree.splitIndex (nativeFreshAtSlot T a s star).mark
      ((nativeFreshAtSlot T a s star).embed c)<U := by
  rw [nativeFreshAtSlot_split]
  exact (Nat.min_le_left _ _).trans_lt hstar

theorem nativeFreshAtSlot_high_relative_star {as : List PositiveMass}
    (T : ClockTree S as) (a : ℝ) (s c : T.Slot) {star U : ℕ}
    (hstar : star<U) (hhigh : U ≤ T.splitIndex s c) :
    (nativeFreshAtSlot T a s star).tree.splitIndex (nativeFreshAtSlot T a s star).mark
      ((nativeFreshAtSlot T a s star).embed c)=star := by
  rw [nativeFreshAtSlot_split,Nat.min_eq_left (hstar.le.trans hhigh)]

variable [Fintype S] [Nonempty S]

theorem nativeFreshAtSlot_old_root_marginal {n : ℕ} {w : S→ℝ} (hw : ∀ σ,0<w σ)
    (φ : S→(Fin (n+1)→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (s : T.Slot) (j : ℕ)
    (q0 : Fin (n+1)→ℝ) (q : ℕ→Fin (n+1)→ℝ) (P : T.Assignment→ℝ)
    (x : Fin (n+1)→ℝ) :
    (nativeFreshAtSlot T a s j).tree.rootExpect w φ
      (fun σ=>P ((nativeFreshAtSlot T a s j).restrict σ)) q0 q x = T.rootExpect w φ P q0 q x :=
  T.markedAttach_rootPreserves hw φ ho _ (nativeFreshAtSlot_mem T a s j) q0 q P x

theorem nativeFreshAtSlot_old_disorder_marginal {ι : Type*} [Fintype ι] [Nonempty ι]
    {w : S→ℝ} (hw : ∀ σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (s : T.Slot) (j : ℕ) (v : ι→ℝ) (q : ℕ→ι→ℝ) (P : T.Assignment→ℝ) (x : ι→ℝ) :
    (nativeFreshAtSlot T 0 s j).tree.disorderExpect w φ v q
      (fun σ=>P ((nativeFreshAtSlot T 0 s j).restrict σ)) x=T.disorderExpect w φ v q P x := by
  let e := finiteJetEquiv ι
  let z := (coordinateEquiv e).symm x
  have H := nativeFreshAtSlot_old_root_marginal hw (reindexFeature e φ)
    T ho s j (fun i=>q 0 (e i)-v (e i))
    (fun k i=>q (k+1) (e i)-q k (e i)) P z
  rw [(nativeFreshAtSlot T 0 s j).tree.rootExpect_eq_disorderExpect hw _ ho _
      (fun i=>v (e i)) (fun k i=>q k (e i)),
    T.rootExpect_eq_disorderExpect hw _ ho _ (fun i=>v (e i)) (fun k i=>q k (e i)),
    (nativeFreshAtSlot T 0 s j).tree.disorderExpect_reindex e w φ v q,
    T.disorderExpect_reindex e w φ v q,ContinuousLinearEquiv.apply_symm_apply] at H
  exact H

end OAI.SKFluctuations.Hierarchy.ClockTree
