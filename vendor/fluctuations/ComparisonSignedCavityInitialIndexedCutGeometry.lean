module

public import ComparisonSignedCavityInitialIndexedCutRows
public import ComparisonSignedCavityWholeLawHolder

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Hierarchy
variable {S : Type}
set_option maxHeartbeats 18000000

def nativeInitialEraseMarkedCoefficient {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) : MarkedPlacement T := {p with coeff:=0}

theorem native_initial_indexed_cut_reference {as : List PositiveMass}
    (T : ClockTree S as) (i : ℕ) (a : ℝ) (p : MarkedPlacement T)
    (hp : p∈nativeInitialIndexedCutRows T i a) :
    ∃r∈T.markedAttach a,nativeInitialEraseMarkedCoefficient p=nativeInitialEraseMarkedCoefficient r := by
  induction T generalizing i a with
  | leaf=>
    have Hp : p=MarkedPlacement.fresh .leaf a:=List.mem_singleton.mp hp
    subst p
    refine ⟨MarkedPlacement.fresh .leaf (a-1),by simp [markedAttach],?_⟩
    rfl
  | step b T ih=>
    cases i with
    | zero=>
      have Hp : p=MarkedPlacement.fresh (T.step b) a:=List.mem_singleton.mp hp
      subst p
      exact ⟨MarkedPlacement.fresh (T.step b) (a-b.val),List.mem_cons_self,rfl⟩
    | succ i=>
      rcases List.mem_cons.mp hp with H|H
      · subst p
        exact ⟨MarkedPlacement.fresh (T.step b) (a-b.val),List.mem_cons_self,rfl⟩
      · obtain ⟨p₀,hp₀,rfl⟩:=List.mem_map.mp H
        obtain ⟨r,hr,heq⟩:=ih i b.val p₀ hp₀
        refine ⟨r.step b,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨r,hr,rfl⟩),?_⟩
        change (nativeInitialEraseMarkedCoefficient p₀).step b=(nativeInitialEraseMarkedCoefficient r).step b
        rw [heq]
  | fork T V ihT ihV=>
    rcases List.mem_cons.mp hp with H|H
    · subst p
      exact ⟨MarkedPlacement.fresh (T.fork V) (-a),List.mem_cons_self,rfl⟩
    · rcases List.mem_append.mp H with H|H
      · obtain ⟨p₀,hp₀,rfl⟩:=List.mem_map.mp H
        obtain ⟨r,hr,heq⟩:=ihT i a p₀ hp₀
        refine ⟨r.left V,List.mem_cons_of_mem _ (List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨r,hr,rfl⟩))),?_⟩
        change (nativeInitialEraseMarkedCoefficient p₀).left V=(nativeInitialEraseMarkedCoefficient r).left V
        rw [heq]
      · obtain ⟨p₀,hp₀,rfl⟩:=List.mem_map.mp H
        obtain ⟨r,hr,heq⟩:=ihV i a p₀ hp₀
        refine ⟨r.right T,List.mem_cons_of_mem _ (List.mem_append.mpr
          (Or.inr (List.mem_map.mpr ⟨r,hr,rfl⟩))),?_⟩
        change (nativeInitialEraseMarkedCoefficient p₀).right T=(nativeInitialEraseMarkedCoefficient r).right T
        rw [heq]

theorem native_initial_indexed_cut_embed_preserves {as : List PositiveMass}
    (T : ClockTree S as) (i : ℕ) (a : ℝ) (p : MarkedPlacement T)
    (hp : p∈nativeInitialIndexedCutRows T i a) :
    Function.Injective p.embed ∧ ∀s t,p.tree.splitIndex (p.embed s) (p.embed t)=T.splitIndex s t := by
  obtain ⟨r,hr,heq⟩:=native_initial_indexed_cut_reference T i a p hp
  change Function.Injective (nativeInitialEraseMarkedCoefficient p).embed ∧
    ∀s t,(nativeInitialEraseMarkedCoefficient p).tree.splitIndex
      ((nativeInitialEraseMarkedCoefficient p).embed s) ((nativeInitialEraseMarkedCoefficient p).embed t)=T.splitIndex s t
  rw [heq]
  exact T.markedAttach_embed_preserves a r hr

theorem native_initial_indexed_cut_new_spin {as : List PositiveMass}
    (T : ClockTree S as) (i : ℕ) (a : ℝ) (p : MarkedPlacement T)
    (hp : p∈nativeInitialIndexedCutRows T i a) (s : T.Slot) :
    p.mark≠p.embed s ∧ p.tree.splitIndex (p.embed s) p.mark ≤ i := by
  induction T generalizing i a with
  | leaf=>
    have Hp : p=MarkedPlacement.fresh .leaf a:=List.mem_singleton.mp hp
    subst p
    simp only [MarkedPlacement.fresh,splitIndex]
    exact ⟨Sum.inr_ne_inl,Nat.zero_le _⟩
  | step b T ih=>
    cases i with
    | zero=>
      have Hp : p=MarkedPlacement.fresh (T.step b) a:=List.mem_singleton.mp hp
      subst p
      simp only [MarkedPlacement.fresh,splitIndex]
      exact ⟨Sum.inr_ne_inl,le_rfl⟩
    | succ i=>
      rcases List.mem_cons.mp hp with H|H
      · subst p
        simp only [MarkedPlacement.fresh,splitIndex]
        exact ⟨Sum.inr_ne_inl,Nat.zero_le _⟩
      · obtain ⟨p₀,hp₀,rfl⟩:=List.mem_map.mp H
        have H:=ih i b.val p₀ hp₀ s
        exact ⟨H.1,by simpa only [MarkedPlacement.step,splitIndex,Nat.add_comm 1] using Nat.add_le_add_left H.2 1⟩
  | fork T V ihT ihV=>
    rcases List.mem_cons.mp hp with H|H
    · subst p
      simp only [MarkedPlacement.fresh,splitIndex]
      exact ⟨Sum.inr_ne_inl,Nat.zero_le _⟩
    · rcases List.mem_append.mp H with H|H
      · obtain ⟨p₀,hp₀,rfl⟩:=List.mem_map.mp H
        cases s with
        | inl s=>
          have H:=ihT i a p₀ hp₀ s
          exact ⟨fun h=>H.1 (Sum.inl.inj h),H.2⟩
        | inr s=>exact ⟨Sum.inl_ne_inr,Nat.zero_le _⟩
      · obtain ⟨p₀,hp₀,rfl⟩:=List.mem_map.mp H
        cases s with
        | inl s=>exact ⟨Sum.inr_ne_inl,Nat.zero_le _⟩
        | inr s=>
          have H:=ihV i a p₀ hp₀ s
          exact ⟨fun h=>H.1 (Sum.inr.inj h),H.2⟩

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem native_initial_indexed_cut_disorder_preserves {w : S→ℝ} (hw : ∀σ,0<w σ)
    (φ : S→(ι→ℝ)→L[ℝ]ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (i : ℕ) (p : MarkedPlacement T)
    (hp : p∈nativeInitialIndexedCutRows T i 0) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (P : T.Assignment→ℝ) (x : ι→ℝ) :
    p.tree.disorderExpect w φ v q (fun σ=>P (p.restrict σ)) x=T.disorderExpect w φ v q P x := by
  obtain ⟨r,hr,heq⟩:=native_initial_indexed_cut_reference T i 0 p hp
  change (nativeInitialEraseMarkedCoefficient p).tree.disorderExpect w φ v q
    (fun σ=>P ((nativeInitialEraseMarkedCoefficient p).restrict σ)) x=T.disorderExpect w φ v q P x
  rw [heq]
  exact T.markedAttach_disorderPreserves_actual hw φ ho r hr v q P x

end OAI.SKFluctuations.Hierarchy.ClockTree
