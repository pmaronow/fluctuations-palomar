module

public import SKConstants.RectangleBound
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants

theorem rectangle_cover_of_unique {ι ρ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype ρ]
    (left right : ρ → Finset ι)
    (hStrict : ∀ u : ρ, ∀ i ∈ left u, ∀ j ∈ right u, i < j)
    (hUnique : ∀ i j : ι, i < j →
      ∃! u : ρ, i ∈ left u ∧ j ∈ right u) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset ρ))
      (fun u => left u ×ˢ right u) ∧
    (Finset.univ : Finset ρ).biUnion (fun u => left u ×ˢ right u) =
      Finset.univ.filter (fun p : ι × ι => p.1 < p.2) := by
  classical
  constructor
  · intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro p hpu hpv
    have hu := Finset.mem_product.mp hpu
    have hv := Finset.mem_product.mp hpv
    have hij : p.1 < p.2 := hStrict u p.1 hu.1 p.2 hu.2
    obtain ⟨w, hw, hOnly⟩ := hUnique p.1 p.2 hij
    exact huv ((hOnly u hu).trans (hOnly v hv).symm)
  · ext p
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_filter]
    constructor
    · rintro ⟨u, hu⟩
      exact hStrict u p.1 hu.1 p.2 hu.2
    · intro hij
      obtain ⟨u, hu, _⟩ := hUnique p.1 p.2 hij
      exact ⟨u, hu⟩

theorem rectangle_cover_map_orderIso {ι κ ρ : Type*}
    [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ] [Fintype ρ]
    (left right : ρ → Finset ι) (e : ι ≃o κ)
    (hStrict : ∀ u : ρ, ∀ i ∈ left u, ∀ j ∈ right u, i < j)
    (hUnique : ∀ i j : ι, i < j →
      ∃! u : ρ, i ∈ left u ∧ j ∈ right u) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset ρ))
      (fun u => (left u).map e.toEmbedding ×ˢ (right u).map e.toEmbedding) ∧
    (Finset.univ : Finset ρ).biUnion
        (fun u => (left u).map e.toEmbedding ×ˢ (right u).map e.toEmbedding) =
      Finset.univ.filter (fun p : κ × κ => p.1 < p.2) := by
  classical
  apply rectangle_cover_of_unique
  · intro u i hi j hj
    rcases Finset.mem_map.mp hi with ⟨i', hi', rfl⟩
    rcases Finset.mem_map.mp hj with ⟨j', hj', rfl⟩
    exact e.strictMono (hStrict u i' hi' j' hj')
  · intro i j hij
    have hij' : e.symm i < e.symm j := e.symm.strictMono hij
    obtain ⟨u, hu, hOnly⟩ := hUnique (e.symm i) (e.symm j) hij'
    refine ⟨u, ?_, ?_⟩
    · exact ⟨Finset.mem_map.mpr ⟨e.symm i, hu.1, e.apply_symm_apply i⟩,
        Finset.mem_map.mpr ⟨e.symm j, hu.2, e.apply_symm_apply j⟩⟩
    · intro v hv
      apply hOnly v
      rcases Finset.mem_map.mp hv.1 with ⟨i', hi', hiEq⟩
      rcases Finset.mem_map.mp hv.2 with ⟨j', hj', hjEq⟩
      have hi : i' = e.symm i := by
        apply e.injective
        simpa only [RelIso.coe_toEmbedding, e.apply_symm_apply] using hiEq
      have hj : j' = e.symm j := by
        apply e.injective
        simpa only [RelIso.coe_toEmbedding, e.apply_symm_apply] using hjEq
      exact ⟨hi ▸ hi', hj ▸ hj'⟩

end SKConstants

namespace SKConstants.DyadicCore

@[expose, reducible] def leafCount : ℕ → ℕ
  | 0 => 1
  | r + 1 => leafCount r + leafCount r

theorem leafCount_eq_pow (r : ℕ) : leafCount r = 2 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [leafCount, ih, pow_succ, Nat.mul_two]

@[expose, reducible] def Node : ℕ → Type
  | 0 => Empty
  | r + 1 => Unit ⊕ (Node r ⊕ Node r)

instance nodeFintype : (r : ℕ) → Fintype (Node r)
  | 0 => inferInstanceAs (Fintype Empty)
  | r + 1 => by
    letI := nodeFintype r
    exact inferInstanceAs (Fintype (Unit ⊕ (Node r ⊕ Node r)))

instance nodeDecidableEq : (r : ℕ) → DecidableEq (Node r)
  | 0 => inferInstanceAs (DecidableEq Empty)
  | r + 1 => by
    letI := nodeDecidableEq r
    exact inferInstanceAs (DecidableEq (Unit ⊕ (Node r ⊕ Node r)))

@[expose] def left : (r : ℕ) → Node r → Finset (Fin (leafCount r))
  | 0, node => nomatch node
  | r + 1, .inl _ => Finset.univ.map (Fin.castAddEmb (leafCount r))
  | r + 1, .inr (.inl node) => (left r node).map (Fin.castAddEmb (leafCount r))
  | r + 1, .inr (.inr node) => (left r node).map (Fin.natAddEmb (leafCount r))

@[expose] def right : (r : ℕ) → Node r → Finset (Fin (leafCount r))
  | 0, node => nomatch node
  | r + 1, .inl _ => Finset.univ.map (Fin.natAddEmb (leafCount r))
  | r + 1, .inr (.inl node) => (right r node).map (Fin.castAddEmb (leafCount r))
  | r + 1, .inr (.inr node) => (right r node).map (Fin.natAddEmb (leafCount r))

@[simp] theorem castAdd_mem_castAdd (m : ℕ) (s : Finset (Fin m)) (i : Fin m) :
    Fin.castAdd m i ∈ s.map (Fin.castAddEmb m) ↔ i ∈ s := by
  exact Finset.mem_map' (Fin.castAddEmb m)

@[simp] theorem natAdd_mem_natAdd (m : ℕ) (s : Finset (Fin m)) (i : Fin m) :
    Fin.natAdd m i ∈ s.map (Fin.natAddEmb m) ↔ i ∈ s := by
  exact Finset.mem_map' (Fin.natAddEmb m)

@[simp] theorem natAdd_not_mem_castAdd (m : ℕ) (s : Finset (Fin m)) (i : Fin m) :
    Fin.natAdd m i ∉ s.map (Fin.castAddEmb m) := by
  simp only [Finset.mem_map, Fin.castAddEmb_apply]
  rintro ⟨j, _, h⟩
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have hj := j.is_lt
  omega

@[simp] theorem castAdd_not_mem_natAdd (m : ℕ) (s : Finset (Fin m)) (i : Fin m) :
    Fin.castAdd m i ∉ s.map (Fin.natAddEmb m) := by
  simp only [Finset.mem_map, Fin.natAddEmb_apply]
  rintro ⟨j, _, h⟩
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have hi := i.is_lt
  omega

@[expose] def Contains (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) : Prop :=
  i ∈ left r node ∧ j ∈ right r node

@[simp] theorem contains_root_LL (r : ℕ) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inl ()) (Fin.castAdd _ i) (Fin.castAdd _ j) := by
  simp only [Contains, left, right, castAdd_not_mem_natAdd, and_false, not_false_eq_true]

@[simp] theorem contains_root_LR (r : ℕ) (i j : Fin (leafCount r)) :
    Contains (r + 1) (.inl ()) (Fin.castAdd _ i) (Fin.natAdd _ j) := by
  simp only [Contains, left, right, castAdd_mem_castAdd, natAdd_mem_natAdd, Finset.mem_univ, and_self]

@[simp] theorem contains_root_RL (r : ℕ) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inl ()) (Fin.natAdd _ i) (Fin.castAdd _ j) := by
  simp only [Contains, left, right, natAdd_not_mem_castAdd, false_and, not_false_eq_true]

@[simp] theorem contains_root_RR (r : ℕ) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inl ()) (Fin.natAdd _ i) (Fin.natAdd _ j) := by
  simp only [Contains, left, right, natAdd_not_mem_castAdd, false_and, not_false_eq_true]

@[simp] theorem contains_left_LL (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    Contains (r + 1) (.inr (.inl node)) (Fin.castAdd _ i) (Fin.castAdd _ j)
      ↔ Contains r node i j := by
  simp only [Contains, left, right, castAdd_mem_castAdd]

@[simp] theorem contains_left_LR (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inr (.inl node)) (Fin.castAdd _ i) (Fin.natAdd _ j) := by
  simp only [Contains, left, right, natAdd_not_mem_castAdd, and_false, not_false_eq_true]

@[simp] theorem contains_left_RL (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inr (.inl node)) (Fin.natAdd _ i) (Fin.castAdd _ j) := by
  simp only [Contains, left, right, natAdd_not_mem_castAdd, false_and, not_false_eq_true]

@[simp] theorem contains_left_RR (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inr (.inl node)) (Fin.natAdd _ i) (Fin.natAdd _ j) := by
  simp only [Contains, left, right, natAdd_not_mem_castAdd, false_and, not_false_eq_true]

@[simp] theorem contains_right_LL (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inr (.inr node)) (Fin.castAdd _ i) (Fin.castAdd _ j) := by
  simp only [Contains, left, right, castAdd_not_mem_natAdd, false_and, not_false_eq_true]

@[simp] theorem contains_right_LR (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inr (.inr node)) (Fin.castAdd _ i) (Fin.natAdd _ j) := by
  simp only [Contains, left, right, castAdd_not_mem_natAdd, false_and, not_false_eq_true]

@[simp] theorem contains_right_RL (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    ¬ Contains (r + 1) (.inr (.inr node)) (Fin.natAdd _ i) (Fin.castAdd _ j) := by
  simp only [Contains, left, right, castAdd_not_mem_natAdd, and_false, not_false_eq_true]

@[simp] theorem contains_right_RR (r : ℕ) (node : Node r) (i j : Fin (leafCount r)) :
    Contains (r + 1) (.inr (.inr node)) (Fin.natAdd _ i) (Fin.natAdd _ j)
      ↔ Contains r node i j := by
  simp only [Contains, left, right, natAdd_mem_natAdd]

theorem contains_strict (r : ℕ) (node : Node r) (i j : Fin (leafCount r))
    (h : Contains r node i j) : i < j := by
  induction r with
  | zero => exact Empty.elim node
  | succ r ih =>
      rcases node with u | node
      · cases u
        change i ∈ Finset.univ.map (Fin.castAddEmb (leafCount r)) ∧
          j ∈ Finset.univ.map (Fin.natAddEmb (leafCount r)) at h
        rcases Finset.mem_map.mp h.1 with ⟨i', _, rfl⟩
        rcases Finset.mem_map.mp h.2 with ⟨j', _, rfl⟩
        change i'.val < leafCount r + j'.val
        have hi := i'.is_lt
        omega
      · rcases node with node | node
        · change i ∈ (left r node).map (Fin.castAddEmb (leafCount r)) ∧
            j ∈ (right r node).map (Fin.castAddEmb (leafCount r)) at h
          rcases Finset.mem_map.mp h.1 with ⟨i', hi, rfl⟩
          rcases Finset.mem_map.mp h.2 with ⟨j', hj, rfl⟩
          exact ih node i' j' ⟨hi, hj⟩
        · change i ∈ (left r node).map (Fin.natAddEmb (leafCount r)) ∧
            j ∈ (right r node).map (Fin.natAddEmb (leafCount r)) at h
          rcases Finset.mem_map.mp h.1 with ⟨i', hi, rfl⟩
          rcases Finset.mem_map.mp h.2 with ⟨j', hj, rfl⟩
          exact (Fin.natAdd_lt_natAdd_iff (leafCount r)).mpr (ih node i' j' ⟨hi, hj⟩)

theorem unique_contains_of_lt (r : ℕ) (i j : Fin (leafCount r)) (hij : i < j) :
    ∃! node, Contains r node i j := by
  induction r with
  | zero =>
      have hi := i.is_lt
      have hj := j.is_lt
      change i.val < j.val at hij
      simp only [leafCount] at hi hj
      omega
  | succ r ih =>
      cases i using Fin.addCases with
      | left i =>
          cases j using Fin.addCases with
          | left j =>
              have hij' : i < j := hij
              obtain ⟨node, hn, hu⟩ := ih i j hij'
              refine ⟨Sum.inr (Sum.inl node), (contains_left_LL r node i j).mpr hn, ?_⟩
              intro node' hnode'
              rcases node' with u | node'
              · cases u
                exact False.elim (contains_root_LL r i j hnode')
              · rcases node' with node' | node'
                · have heq := hu node' ((contains_left_LL r node' i j).mp hnode')
                  exact congrArg (fun n => Sum.inr (Sum.inl n)) heq
                · exact False.elim (contains_right_LL r node' i j hnode')
          | right j =>
              refine ⟨Sum.inl (), contains_root_LR r i j, ?_⟩
              intro node' hnode'
              rcases node' with u | node'
              · cases u
                rfl
              · rcases node' with node' | node'
                · exact False.elim (contains_left_LR r node' i j hnode')
                · exact False.elim (contains_right_LR r node' i j hnode')
      | right i =>
          cases j using Fin.addCases with
          | left j =>
              change leafCount r + i.val < j.val at hij
              have hj := j.is_lt
              omega
          | right j =>
              have hij' : i < j := (Fin.natAdd_lt_natAdd_iff (leafCount r)).mp hij
              obtain ⟨node, hn, hu⟩ := ih i j hij'
              refine ⟨Sum.inr (Sum.inr node), (contains_right_RR r node i j).mpr hn, ?_⟩
              intro node' hnode'
              rcases node' with u | node'
              · cases u
                exact False.elim (contains_root_RR r i j hnode')
              · rcases node' with node' | node'
                · exact False.elim (contains_left_RR r node' i j hnode')
                · have heq := hu node' ((contains_right_RR r node' i j).mp hnode')
                  exact congrArg (fun n => Sum.inr (Sum.inr n)) heq

theorem node_card_add_one (r : ℕ) : Fintype.card (Node r) + 1 = leafCount r := by
  induction r with
  | zero => simp [Node, leafCount]
  | succ r ih =>
      change Fintype.card (Unit ⊕ (Node r ⊕ Node r)) + 1 = leafCount r + leafCount r
      rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit]
      omega

theorem node_card (r : ℕ) : Fintype.card (Node r) = 2 ^ r - 1 := by
  have h := node_card_add_one r
  rw [leafCount_eq_pow] at h
  omega

end SKConstants.DyadicCore

namespace SKConstants

@[expose] def dyadicLeft (r : ℕ) (node : DyadicCore.Node r) :
    Finset (Fin (2 ^ r)) :=
  (DyadicCore.left r node).map
    (Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)).toEmbedding

@[expose] def dyadicRight (r : ℕ) (node : DyadicCore.Node r) :
    Finset (Fin (2 ^ r)) :=
  (DyadicCore.right r node).map
    (Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)).toEmbedding

theorem dyadic_rectangle_strict (r : ℕ) (node : DyadicCore.Node r)
    (i j : Fin (2 ^ r)) (hi : i ∈ dyadicLeft r node)
    (hj : j ∈ dyadicRight r node) : i < j := by
  let e := Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)
  change i ∈ (DyadicCore.left r node).map e.toEmbedding at hi
  change j ∈ (DyadicCore.right r node).map e.toEmbedding at hj
  rcases Finset.mem_map.mp hi with ⟨i', hi', rfl⟩
  rcases Finset.mem_map.mp hj with ⟨j', hj', rfl⟩
  exact e.strictMono (DyadicCore.contains_strict r node i' j' ⟨hi', hj'⟩)

theorem dyadic_unique_rectangle (r : ℕ) (i j : Fin (2 ^ r)) (hij : i < j) :
    ∃! node : DyadicCore.Node r, i ∈ dyadicLeft r node ∧ j ∈ dyadicRight r node := by
  let e := Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)
  change ∃! node : DyadicCore.Node r,
    i ∈ (DyadicCore.left r node).map e.toEmbedding ∧
      j ∈ (DyadicCore.right r node).map e.toEmbedding
  obtain ⟨node, hn, hOnly⟩ := DyadicCore.unique_contains_of_lt r
    (e.symm i) (e.symm j) (e.symm.strictMono hij)
  refine ⟨node, ?_, ?_⟩
  · exact ⟨Finset.mem_map.mpr ⟨e.symm i, hn.1, e.apply_symm_apply i⟩,
      Finset.mem_map.mpr ⟨e.symm j, hn.2, e.apply_symm_apply j⟩⟩
  · intro node' hnode'
    apply hOnly node'
    rcases Finset.mem_map.mp hnode'.1 with ⟨i', hi', hiEq⟩
    rcases Finset.mem_map.mp hnode'.2 with ⟨j', hj', hjEq⟩
    have hi : i' = e.symm i := by
      apply e.injective
      simpa only [RelIso.coe_toEmbedding, e.apply_symm_apply] using hiEq
    have hj : j' = e.symm j := by
      apply e.injective
      simpa only [RelIso.coe_toEmbedding, e.apply_symm_apply] using hjEq
    exact ⟨hi ▸ hi', hj ▸ hj'⟩

theorem dyadic_rectangle_cover (r : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (DyadicCore.Node r)))
      (fun node => dyadicLeft r node ×ˢ dyadicRight r node) ∧
    (Finset.univ : Finset (DyadicCore.Node r)).biUnion
        (fun node => dyadicLeft r node ×ˢ dyadicRight r node) =
      Finset.univ.filter (fun p : Fin (2 ^ r) × Fin (2 ^ r) => p.1 < p.2) := by
  apply rectangle_cover_of_unique (dyadicLeft r) (dyadicRight r)
  · intro node i hi j hj
    exact dyadic_rectangle_strict r node i j hi hj
  · exact dyadic_unique_rectangle r

theorem dyadic_rectangle_bound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (r : ℕ) (X Y : Fin (2 ^ r) → H) (a b : Fin (2 ^ r) → ℝ) :
    |∑ p ∈ (Finset.univ.filter fun p : Fin (2 ^ r) × Fin (2 ^ r) => p.1 < p.2),
      inner (𝕜 := ℝ) (a p.1 • X p.1) (b p.2 • Y p.2)| ≤
      Real.sqrt (∑ node : DyadicCore.Node r,
        ‖∑ i ∈ dyadicLeft r node, a i • X i‖ ^ 2) *
      Real.sqrt (∑ node : DyadicCore.Node r,
        ‖∑ j ∈ dyadicRight r node, b j • Y j‖ ^ 2) := by
  exact rectangle_bound_explicit X Y a b Finset.univ (dyadicLeft r) (dyadicRight r)
    (dyadic_rectangle_cover r).1 (dyadic_rectangle_cover r).2

end SKConstants
