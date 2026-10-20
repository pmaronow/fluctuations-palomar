module

public import ComparisonSignedCavityTrunkProjection
public import CavityCutBlocks

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

structure NativeRetainedSubtreeClone {as : List PositiveMass} (T : ClockTree S as) where
  tree : ClockTree S as
  oldEmbed : T.Slot → tree.Slot
  newEmbed : T.Slot → tree.Slot
  oldRestrict : tree.Assignment → T.Assignment
  newRestrict : tree.Assignment → T.Assignment
  old_at : ∀ σ s,T.atSlot (oldRestrict σ) s = tree.atSlot σ (oldEmbed s)
  new_at : ∀ σ s,T.atSlot (newRestrict σ) s = tree.atSlot σ (newEmbed s)

namespace NativeRetainedSubtreeClone

def unchanged {as : List PositiveMass} (T : ClockTree S as) : NativeRetainedSubtreeClone T :=
  ⟨T,id,id,id,id,fun _ _ => rfl,fun _ _ => rfl⟩

def root {as : List PositiveMass} (T : ClockTree S as) : NativeRetainedSubtreeClone T :=
  ⟨T.fork T,Sum.inl,Sum.inr,Prod.fst,Prod.snd,fun _ _ => rfl,fun _ _ => rfl⟩

def step {as : List PositiveMass} {T : ClockTree S as}
    (p : NativeRetainedSubtreeClone T) (b : PositiveMass) :
    NativeRetainedSubtreeClone (T.step b) :=
  ⟨p.tree.step b,p.oldEmbed,p.newEmbed,p.oldRestrict,p.newRestrict,p.old_at,p.new_at⟩

def left {as : List PositiveMass} {T : ClockTree S as}
    (p : NativeRetainedSubtreeClone T) (V : ClockTree S as) :
    NativeRetainedSubtreeClone (T.fork V) where
  tree := p.tree.fork V
  oldEmbed := Sum.map p.oldEmbed id
  newEmbed := Sum.map p.newEmbed id
  oldRestrict := fun σ => (p.oldRestrict σ.1,σ.2)
  newRestrict := fun σ => (p.newRestrict σ.1,σ.2)
  old_at := by intro σ s;cases s with
    | inl s => exact p.old_at σ.1 s
    | inr s => rfl
  new_at := by intro σ s;cases s with
    | inl s => exact p.new_at σ.1 s
    | inr s => rfl

def right {as : List PositiveMass} {V : ClockTree S as}
    (p : NativeRetainedSubtreeClone V) (T : ClockTree S as) :
    NativeRetainedSubtreeClone (T.fork V) where
  tree := T.fork p.tree
  oldEmbed := Sum.map id p.oldEmbed
  newEmbed := Sum.map id p.newEmbed
  oldRestrict := fun σ => (σ.1,p.oldRestrict σ.2)
  newRestrict := fun σ => (σ.1,p.newRestrict σ.2)
  old_at := by intro σ s;cases s with
    | inl s => rfl
    | inr s => exact p.old_at σ.2 s
  new_at := by intro σ s;cases s with
    | inl s => rfl
    | inr s => exact p.new_at σ.2 s

end NativeRetainedSubtreeClone

def nativeCloneBlockAtSlot : {as : List PositiveMass} → (T : ClockTree S as) →
    T.Slot → ℕ → NativeRetainedSubtreeClone T
  | _,.leaf,_,0 => NativeRetainedSubtreeClone.root .leaf
  | _,.leaf,_,_+1 => NativeRetainedSubtreeClone.unchanged .leaf
  | _,.step b T,_,0 => NativeRetainedSubtreeClone.root (T.step b)
  | _,.step b T,s,j+1 => (nativeCloneBlockAtSlot T s j).step b
  | _,.fork T V,_,0 => NativeRetainedSubtreeClone.root (T.fork V)
  | _,.fork T V,s,j+1 => match (s : T.Slot ⊕ V.Slot) with
    | Sum.inl s => (nativeCloneBlockAtSlot T s (j+1)).left V
    | Sum.inr s => (nativeCloneBlockAtSlot V s (j+1)).right T

theorem nativeCloneBlockAtSlot_within_copy_splits {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ) (c d : T.Slot) :
    (nativeCloneBlockAtSlot T s j).tree.splitIndex
      ((nativeCloneBlockAtSlot T s j).oldEmbed c) ((nativeCloneBlockAtSlot T s j).oldEmbed d) =
      T.splitIndex c d ∧
    (nativeCloneBlockAtSlot T s j).tree.splitIndex
      ((nativeCloneBlockAtSlot T s j).newEmbed c) ((nativeCloneBlockAtSlot T s j).newEmbed d) =
      T.splitIndex c d := by
  induction T generalizing j with
  | leaf => cases j <;> exact ⟨rfl,rfl⟩
  | step b T ih =>
    cases j with
    | zero => exact ⟨rfl,rfl⟩
    | succ j =>
      exact ⟨congrArg (1+·) (ih s j c d).1,congrArg (1+·) (ih s j c d).2⟩
  | fork T V ihT ihV =>
    cases j with
    | zero => exact ⟨rfl,rfl⟩
    | succ j => cases s with
      | inl s => cases c with
        | inl c => cases d with
          | inl d => exact ihT s (j+1) c d
          | inr d => exact ⟨rfl,rfl⟩
        | inr c => cases d with
          | inl d => exact ⟨rfl,rfl⟩
          | inr d => exact ⟨rfl,rfl⟩
      | inr s => cases c with
        | inl c => cases d with
          | inl d => exact ⟨rfl,rfl⟩
          | inr d => exact ⟨rfl,rfl⟩
        | inr c => cases d with
          | inl d => exact ⟨rfl,rfl⟩
          | inr d => exact ihV s (j+1) c d

theorem nativeCloneBlockAtSlot_cross_split {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ) (c d : T.Slot) :
    (nativeCloneBlockAtSlot T s j).tree.splitIndex
      ((nativeCloneBlockAtSlot T s j).oldEmbed c) ((nativeCloneBlockAtSlot T s j).newEmbed d) =
      if j ≤ T.splitIndex s c ∧ j ≤ T.splitIndex s d then j else T.splitIndex c d := by
  induction T generalizing j with
  | leaf =>
    cases j <;> simp [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.root,
      NativeRetainedSubtreeClone.unchanged,splitIndex]
  | step b T ih =>
    cases j with
    | zero => simp only [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.root,
        splitIndex,Sum.elim_inl,Sum.elim_inr,Nat.zero_le,and_self,ite_true]
    | succ j =>
      change 1+(nativeCloneBlockAtSlot T s j).tree.splitIndex
        ((nativeCloneBlockAtSlot T s j).oldEmbed c) ((nativeCloneBlockAtSlot T s j).newEmbed d) =
        if j+1 ≤ 1+T.splitIndex s c ∧ j+1 ≤ 1+T.splitIndex s d then j+1 else 1+T.splitIndex c d
      rw [ih]
      split_ifs <;> omega
  | fork T V ihT ihV =>
    cases j with
    | zero => simp only [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.root,
        splitIndex,Sum.elim_inl,Sum.elim_inr,Nat.zero_le,and_self,ite_true]
    | succ j => cases s with
      | inl s => cases c with
        | inl c => cases d with
          | inl d => exact ihT s (j+1) c d
          | inr d => simp [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.left,splitIndex]
        | inr c => cases d with
          | inl d => simp [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.left,splitIndex]
          | inr d => simp [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.left,splitIndex]
      | inr s => cases c with
        | inl c => cases d with
          | inl d => simp [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.right,splitIndex]
          | inr d => simp [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.right,splitIndex]
        | inr c => cases d with
          | inl d => simp [nativeCloneBlockAtSlot,NativeRetainedSubtreeClone.right,splitIndex]
          | inr d => exact ihV s (j+1) c d

theorem nativeCloneBlockAtSlot_exterior_shared {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ) (c : T.Slot)
    (hc : T.splitIndex s c < j) :
    (nativeCloneBlockAtSlot T s j).oldEmbed c = (nativeCloneBlockAtSlot T s j).newEmbed c := by
  induction T generalizing j with
  | leaf => cases j with
    | zero => have H : 0 < 0 := hc;omega
    | succ j => cases s;cases c;rfl
  | step b T ih =>
    cases j with
    | zero => omega
    | succ j =>
      exact ih s j c (by change 1+T.splitIndex s c < j+1 at hc;omega)
  | fork T V ihT ihV =>
    cases j with
    | zero => omega
    | succ j => cases s with
      | inl s => cases c with
        | inl c => exact congrArg Sum.inl (ihT s (j+1) c hc)
        | inr c => rfl
      | inr s => cases c with
        | inl c => rfl
        | inr c => exact congrArg Sum.inr (ihV s (j+1) c hc)

theorem nativeCloneBlockAtSlot_inside_disjoint {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ) (c d : T.Slot)
    (hc : j ≤ T.splitIndex s c) (hd : j ≤ T.splitIndex s d) :
    (nativeCloneBlockAtSlot T s j).oldEmbed c ≠ (nativeCloneBlockAtSlot T s j).newEmbed d := by
  induction T generalizing j with
  | leaf => cases j with
    | zero => exact Sum.inl_ne_inr
    | succ j => have H : j+1 ≤ 0 := hc;omega
  | step b T ih =>
    cases j with
    | zero => exact Sum.inl_ne_inr
    | succ j =>
      have hc' : j ≤ T.splitIndex s c := by change j+1 ≤ 1+T.splitIndex s c at hc;omega
      have hd' : j ≤ T.splitIndex s d := by change j+1 ≤ 1+T.splitIndex s d at hd;omega
      exact ih s j c d hc' hd'
  | fork T V ihT ihV =>
    cases j with
    | zero => exact Sum.inl_ne_inr
    | succ j => cases s with
      | inl s => cases c with
        | inl c => cases d with
          | inl d => exact fun H => ihT s (j+1) c d hc hd (Sum.inl.inj H)
          | inr d => have H : j+1 ≤ 0 := hd;omega
        | inr c => have H : j+1 ≤ 0 := hc;omega
      | inr s => cases c with
        | inl c => have H : j+1 ≤ 0 := hc;omega
        | inr c => cases d with
          | inl d => have H : j+1 ≤ 0 := hd;omega
          | inr d => exact fun H => ihV s (j+1) c d hc hd (Sum.inr.inj H)

theorem nativeCloneBlockAtSlot_exterior_low_lt {as : List PositiveMass}
    (T : ClockTree S as) (s c o : T.Slot) (j : ℕ)
    (hc : j ≤ T.splitIndex s c) (ho : T.splitIndex s o < j) :
    T.splitIndex o c < j := by
  by_contra H
  have hco : j ≤ T.splitIndex c o := by rw [T.splitIndex_symm];omega
  exact (not_le.mpr ho) (T.splitIndex_cut_trans j s c o hc hco)

theorem nativeCloneBlockAtSlot_embed_injective {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ) :
    Function.Injective (nativeCloneBlockAtSlot T s j).oldEmbed ∧
      Function.Injective (nativeCloneBlockAtSlot T s j).newEmbed := by
  induction T generalizing j with
  | leaf => cases j with
    | zero => exact ⟨Sum.inl_injective,Sum.inr_injective⟩
    | succ j => exact ⟨Function.injective_id,Function.injective_id⟩
  | step b T ih =>
    cases j with
    | zero => exact ⟨Sum.inl_injective,Sum.inr_injective⟩
    | succ j => exact ih s j
  | fork T V ihT ihV =>
    cases j with
    | zero => exact ⟨Sum.inl_injective,Sum.inr_injective⟩
    | succ j => cases s with
      | inl s => exact ⟨(ihT s (j+1)).1.sumMap Function.injective_id,
          (ihT s (j+1)).2.sumMap Function.injective_id⟩
      | inr s => exact ⟨Function.injective_id.sumMap (ihV s (j+1)).1,
          Function.injective_id.sumMap (ihV s (j+1)).2⟩

theorem nativeCloneBlockAtSlot_exterior_observation_shared {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (j : ℕ) (c : T.Slot)
    (hc : T.splitIndex s c < j)
    (σ : (nativeCloneBlockAtSlot T s j).tree.Assignment) :
    T.atSlot ((nativeCloneBlockAtSlot T s j).oldRestrict σ) c =
      T.atSlot ((nativeCloneBlockAtSlot T s j).newRestrict σ) c := by
  rw [(nativeCloneBlockAtSlot T s j).old_at σ c,
    (nativeCloneBlockAtSlot T s j).new_at σ c,
    nativeCloneBlockAtSlot_exterior_shared T s j c hc]

theorem nativeCloneBlockAtSlot_boundary_geometry {as : List PositiveMass}
    (T : ClockTree S as) (s c o : T.Slot) (j : ℕ)
    (hc : j ≤ T.splitIndex s c) (ho : T.splitIndex s o < j) :
    let p := nativeCloneBlockAtSlot T s j
    p.oldEmbed o = p.newEmbed o ∧
    p.tree.splitIndex (p.oldEmbed o) (p.oldEmbed c) = T.splitIndex o c ∧
    p.tree.splitIndex (p.oldEmbed o) (p.newEmbed c) = T.splitIndex o c ∧
    p.tree.splitIndex (p.oldEmbed c) (p.newEmbed c) = j := by
  dsimp only
  have hout := nativeCloneBlockAtSlot_exterior_shared T s j o ho
  refine ⟨hout,(nativeCloneBlockAtSlot_within_copy_splits T s j o c).1,?_,?_⟩
  · rw [nativeCloneBlockAtSlot_cross_split,ite_eq_right]
    exact fun H => (not_le.mpr ho) H.1
  · rw [nativeCloneBlockAtSlot_cross_split,ite_eq_left ⟨hc,hc⟩]

theorem nativeCloneBlockAtSlot_resampling_slots {as : List PositiveMass}
    (T : ClockTree S as) (s c o : T.Slot) (j : ℕ)
    (hc : j ≤ T.splitIndex s c) (ho : T.splitIndex s o < j) :
    let p := nativeCloneBlockAtSlot T s j
    p.oldEmbed o ≠ p.oldEmbed c ∧ p.oldEmbed o ≠ p.newEmbed c ∧
    p.oldEmbed c ≠ p.newEmbed c ∧
    p.tree.splitIndex (p.oldEmbed o) (p.oldEmbed c) =
      p.tree.splitIndex (p.oldEmbed o) (p.newEmbed c) ∧
    p.tree.splitIndex (p.oldEmbed o) (p.oldEmbed c) <
      p.tree.splitIndex (p.oldEmbed c) (p.newEmbed c) := by
  dsimp only
  have hout := nativeCloneBlockAtSlot_exterior_shared T s j o ho
  have hinj := nativeCloneBlockAtSlot_embed_injective T s j
  have hneq : o ≠ c := by intro H;subst o;omega
  have HG := nativeCloneBlockAtSlot_boundary_geometry T s c o j hc ho
  refine ⟨fun H => hneq (hinj.1 H),fun H => hneq (hinj.2 (hout.symm.trans H)),
    nativeCloneBlockAtSlot_inside_disjoint T s j c c hc hc,?_,?_⟩
  · exact HG.2.1.trans HG.2.2.1.symm
  · rw [HG.2.1,HG.2.2.2]
    exact nativeCloneBlockAtSlot_exterior_low_lt T s c o j hc ho

variable {ι : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem nativeRetainedClone_fork_expect_external_left (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) {as : List PositiveMass}
    (T V : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (P : (T.fork V).Assignment → ℝ) (x : ι → ℝ) :
    (T.fork V).expect w φ q P x =
      ∑ τ,V.weight w φ q τ x*T.expect w φ q (fun σ => P (σ,τ)) x := by
  simp only [expect,weight_fork,Fintype.sum_prod_type,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem nativeRetainedClone_root_marginals {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (T : ClockTree S as) {a : ℝ} (ha : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (NativeRetainedSubtreeClone.root T).tree.expect w φ q
      (fun σ => P ((NativeRetainedSubtreeClone.root T).oldRestrict σ)) x = T.expect w φ q P x ∧
    (NativeRetainedSubtreeClone.root T).tree.expect w φ q
      (fun σ => P ((NativeRetainedSubtreeClone.root T).newRestrict σ)) x = T.expect w φ q P x := by
  constructor
  · change (T.fork T).expect w φ q (fun σ => P σ.1) x = _
    rw [expect_fork]
    simp_rw [T.expect_const hw φ ha q]
  · change (T.fork T).expect w φ q (fun σ => P σ.2) x = _
    rw [expect_fork]
    change T.expect w φ q (fun _ => T.expect w φ q P x) x = T.expect w φ q P x
    exact T.expect_const hw φ ha q _ x

theorem nativeCloneBlockAtSlot_expect_marginals {as : List PositiveMass}
    {w : S → ℝ} (hw : ∀ σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (T : ClockTree S as) {a : ℝ} (ha : MassOrdered a as) (s : T.Slot) (j : ℕ)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (nativeCloneBlockAtSlot T s j).tree.expect w φ q
      (fun σ => P ((nativeCloneBlockAtSlot T s j).oldRestrict σ)) x = T.expect w φ q P x ∧
    (nativeCloneBlockAtSlot T s j).tree.expect w φ q
      (fun σ => P ((nativeCloneBlockAtSlot T s j).newRestrict σ)) x = T.expect w φ q P x := by
  induction T generalizing a j q x with
  | leaf => cases j with
    | zero => exact nativeRetainedClone_root_marginals hw φ .leaf ha q P x
    | succ j => exact ⟨rfl,rfl⟩
  | step b T ih =>
    cases j with
    | zero => exact nativeRetainedClone_root_marginals hw φ (T.step b) ha q P x
    | succ j =>
      constructor
      · change ((nativeCloneBlockAtSlot T s j).tree.step b).expect w φ q
          (fun σ => P ((nativeCloneBlockAtSlot T s j).oldRestrict σ)) x = _
        rw [expect_step hw φ b _ ha.2.2,expect_step hw φ b _ ha.2.2]
        congr 1
        funext y
        exact (ih ha.2.2 s j (fun k => q (k+1)) P y).1
      · change ((nativeCloneBlockAtSlot T s j).tree.step b).expect w φ q
          (fun σ => P ((nativeCloneBlockAtSlot T s j).newRestrict σ)) x = _
        rw [expect_step hw φ b _ ha.2.2,expect_step hw φ b _ ha.2.2]
        congr 1
        funext y
        exact (ih ha.2.2 s j (fun k => q (k+1)) P y).2
  | fork T V ihT ihV =>
    cases j with
    | zero => exact nativeRetainedClone_root_marginals hw φ (T.fork V) ha q P x
    | succ j => cases s with
      | inl s =>
        constructor
        · change ((nativeCloneBlockAtSlot T s (j+1)).tree.fork V).expect w φ q
            (fun σ => P ((nativeCloneBlockAtSlot T s (j+1)).oldRestrict σ.1,σ.2)) x = _
          rw [nativeRetainedClone_fork_expect_external_left,nativeRetainedClone_fork_expect_external_left]
          apply Finset.sum_congr rfl
          intro τ _
          congr 1
          exact (ihT ha s (j+1) q (fun σ => P (σ,τ)) x).1
        · change ((nativeCloneBlockAtSlot T s (j+1)).tree.fork V).expect w φ q
            (fun σ => P ((nativeCloneBlockAtSlot T s (j+1)).newRestrict σ.1,σ.2)) x = _
          rw [nativeRetainedClone_fork_expect_external_left,nativeRetainedClone_fork_expect_external_left]
          apply Finset.sum_congr rfl
          intro τ _
          congr 1
          exact (ihT ha s (j+1) q (fun σ => P (σ,τ)) x).2
      | inr s =>
        constructor
        · change (T.fork (nativeCloneBlockAtSlot V s (j+1)).tree).expect w φ q
            (fun (σ : T.Assignment × (nativeCloneBlockAtSlot V s (j+1)).tree.Assignment) =>
              P (σ.1,(nativeCloneBlockAtSlot V s (j+1)).oldRestrict σ.2)) x = _
          rw [expect_fork,expect_fork]
          unfold expect
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
          exact (ihV ha s (j+1) q (fun τ => P (σ,τ)) x).1
        · change (T.fork (nativeCloneBlockAtSlot V s (j+1)).tree).expect w φ q
            (fun (σ : T.Assignment × (nativeCloneBlockAtSlot V s (j+1)).tree.Assignment) =>
              P (σ.1,(nativeCloneBlockAtSlot V s (j+1)).newRestrict σ.2)) x = _
          rw [expect_fork,expect_fork]
          unfold expect
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
          exact (ihV ha s (j+1) q (fun τ => P (σ,τ)) x).2

def nativeRetainedCloneRootMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (Q : T.Assignment → T.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  T.expect w φ q (fun σ => T.expect w φ q (Q σ) x) x

def nativeRetainedCloneCutMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ]ℝ) :
    {as : List PositiveMass} → (T : ClockTree S as) → T.Slot → ℕ →
    (ℕ → ι → ℝ≥0) → (T.Assignment → T.Assignment → ℝ) → (ι → ℝ) → ℝ
  | _,.leaf,_,0,q,Q,x => nativeRetainedCloneRootMean w φ .leaf q Q x
  | _,.leaf,_,_+1,q,Q,x => ClockTree.leaf.expect w φ q (fun σ => Q σ σ) x
  | _,.step b T,_,0,q,Q,x => nativeRetainedCloneRootMean w φ (T.step b) q Q x
  | _::as,.step b T,s,j+1,q,Q,x =>
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun k => q (k+1))))
        (nativeRetainedCloneCutMean w φ T s j (fun k => q (k+1)) Q) x
  | _,.fork T V,_,0,q,Q,x => nativeRetainedCloneRootMean w φ (T.fork V) q Q x
  | _,.fork T V,s,j+1,q,Q,x => match (s : T.Slot ⊕ V.Slot) with
    | Sum.inl s => ∑ τ,V.weight w φ q τ x*
        nativeRetainedCloneCutMean w φ T s (j+1) q (fun σ σ' => Q (σ,τ) (σ',τ)) x
    | Sum.inr s => ∑ σ,T.weight w φ q σ x*
        nativeRetainedCloneCutMean w φ V s (j+1) q (fun τ τ' => Q (σ,τ) (σ,τ')) x

omit [Nonempty S] in
theorem nativeRetainedCloneRootMean_eq_clone (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → ι → ℝ≥0) (Q : T.Assignment → T.Assignment → ℝ) (x : ι → ℝ) :
    nativeRetainedCloneRootMean w φ T q Q x =
      (NativeRetainedSubtreeClone.root T).tree.expect w φ q
        (fun σ => Q ((NativeRetainedSubtreeClone.root T).oldRestrict σ)
          ((NativeRetainedSubtreeClone.root T).newRestrict σ)) x := by
  exact (expect_fork w φ T T q (fun σ => Q σ.1 σ.2) x).symm

theorem nativeRetainedCloneCutMean_eq_clone {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (s : T.Slot) (j : ℕ)
    (q : ℕ → ι → ℝ≥0) (Q : T.Assignment → T.Assignment → ℝ) (x : ι → ℝ) :
    nativeRetainedCloneCutMean w φ T s j q Q x =
      (nativeCloneBlockAtSlot T s j).tree.expect w φ q
        (fun σ => Q ((nativeCloneBlockAtSlot T s j).oldRestrict σ)
          ((nativeCloneBlockAtSlot T s j).newRestrict σ)) x := by
  induction T generalizing a j q x with
  | leaf => cases j with
    | zero => exact nativeRetainedCloneRootMean_eq_clone w φ .leaf q Q x
    | succ j => rfl
  | step b T ih =>
    cases j with
    | zero => exact nativeRetainedCloneRootMean_eq_clone w φ (T.step b) q Q x
    | succ j =>
      change shiftedMean _ _ _ _ x =
        ((nativeCloneBlockAtSlot T s j).tree.step b).expect w φ q
          (fun σ => Q ((nativeCloneBlockAtSlot T s j).oldRestrict σ)
            ((nativeCloneBlockAtSlot T s j).newRestrict σ)) x
      rw [expect_step hw φ b _ ha.2.2]
      congr 1
      funext y
      exact ih ha.2.2 s j (fun k => q (k+1)) Q y
  | fork T V ihT ihV =>
    cases j with
    | zero => exact nativeRetainedCloneRootMean_eq_clone w φ (T.fork V) q Q x
    | succ j => cases s with
      | inl s =>
        change (∑ τ,V.weight w φ q τ x*nativeRetainedCloneCutMean w φ T s (j+1)
          q (fun σ σ' => Q (σ,τ) (σ',τ)) x) =
          ((nativeCloneBlockAtSlot T s (j+1)).tree.fork V).expect w φ q
            (fun σ => Q ((nativeCloneBlockAtSlot T s (j+1)).oldRestrict σ.1,σ.2)
              ((nativeCloneBlockAtSlot T s (j+1)).newRestrict σ.1,σ.2)) x
        rw [nativeRetainedClone_fork_expect_external_left]
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT ha s (j+1) q (fun σ σ' => Q (σ,τ) (σ',τ)) x
      | inr s =>
        change (∑ σ,T.weight w φ q σ x*nativeRetainedCloneCutMean w φ V s (j+1)
          q (fun τ τ' => Q (σ,τ) (σ,τ')) x) =
          (T.fork (nativeCloneBlockAtSlot V s (j+1)).tree).expect w φ q
            (fun (σ : T.Assignment × (nativeCloneBlockAtSlot V s (j+1)).tree.Assignment) =>
              Q (σ.1,(nativeCloneBlockAtSlot V s (j+1)).oldRestrict σ.2)
                (σ.1,(nativeCloneBlockAtSlot V s (j+1)).newRestrict σ.2)) x
        rw [expect_fork]
        unfold expect
        apply Finset.sum_congr rfl
        intro σ _
        congr 1
        exact ihV ha s (j+1) q (fun τ τ' => Q (σ,τ) (σ,τ')) x

theorem nativeRetainedCloneCut_disorderLaw {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (s : T.Slot) (j : ℕ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (Q : T.Assignment → T.Assignment → ℝ) (x : ι → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i-v i)))
      (nativeRetainedCloneCutMean w φ T s j
        (cumulativeIncrements (q 0) (fun k => q (k+1))) Q) x =
    (nativeCloneBlockAtSlot T s j).tree.disorderExpect w φ v q
      (fun σ => Q ((nativeCloneBlockAtSlot T s j).oldRestrict σ)
        ((nativeCloneBlockAtSlot T s j).newRestrict σ)) x := by
  rw [(nativeCloneBlockAtSlot T s j).tree.disorderExpect_integral hw φ ha]
  congr 1
  funext y
  exact nativeRetainedCloneCutMean_eq_clone hw φ T ha s j _ Q y

theorem nativeCloneBlockAtSlot_disorder_marginals {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (s : T.Slot) (j : ℕ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (nativeCloneBlockAtSlot T s j).tree.disorderExpect w φ v q
      (fun σ => P ((nativeCloneBlockAtSlot T s j).oldRestrict σ)) x = T.disorderExpect w φ v q P x ∧
    (nativeCloneBlockAtSlot T s j).tree.disorderExpect w φ v q
      (fun σ => P ((nativeCloneBlockAtSlot T s j).newRestrict σ)) x = T.disorderExpect w φ v q P x := by
  constructor
  · rw [(nativeCloneBlockAtSlot T s j).tree.disorderExpect_integral hw φ ha,
      T.disorderExpect_integral hw φ ha]
    congr 1
    funext y
    exact (nativeCloneBlockAtSlot_expect_marginals hw φ T ha s j _ P y).1
  · rw [(nativeCloneBlockAtSlot T s j).tree.disorderExpect_integral hw φ ha,
      T.disorderExpect_integral hw φ ha]
    congr 1
    funext y
    exact (nativeCloneBlockAtSlot_expect_marginals hw φ T ha s j _ P y).2

end OAI.SKFluctuations.Hierarchy.ClockTree
