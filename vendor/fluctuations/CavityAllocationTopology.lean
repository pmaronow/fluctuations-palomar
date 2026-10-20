module

public import CavityAllocationCoefficients

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open scoped BigOperators
variable {C : Type*} [DecidableEq C]

def allocationWordCoefficient (cost : ℕ → ℝ) : Finset C → List C → ℝ
  | _, [] => 1
  | occupied, c::cs => if c ∈ occupied then allocationWordCoefficient cost occupied cs
      else cost occupied.card*allocationWordCoefficient cost (insert c occupied) cs

def occupancyProduct (cost : ℕ → ℝ) (k h : ℕ) : ℝ :=
  ∏ j ∈ Finset.range h, cost (k+j)

private theorem occupancyProduct_succ (cost : ℕ → ℝ) (k h : ℕ) :
    occupancyProduct cost k (h+1) = cost k*occupancyProduct cost (k+1) h := by
  rw [occupancyProduct, Finset.prod_range_succ', mul_comm]
  simp only [Nat.add_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  omega

theorem allocationWordCoefficient_eq_product (cost : ℕ → ℝ)
    (occupied : Finset C) (cs : List C) :
    allocationWordCoefficient cost occupied cs =
      occupancyProduct cost occupied.card (cs.toFinset \ occupied).card := by
  have hl : allocationWordCoefficient cost occupied cs =
      occupancyProduct cost occupied.card (newChildren occupied cs).length := by
    induction cs generalizing occupied with
    | nil => simp [allocationWordCoefficient, newChildren, occupancyProduct]
    | cons c cs ih =>
      by_cases hc : c ∈ occupied
      · simp only [allocationWordCoefficient, newChildren, if_pos hc, ih]
      · simp only [allocationWordCoefficient, newChildren, if_neg hc, List.length_cons,
          occupancyProduct_succ, Finset.card_insert_of_notMem hc, ih]
  rw [hl, newChildren_length]

theorem allocationWordCoefficient_perm (cost : ℕ → ℝ) (occupied : Finset C)
    {cs ds : List C} (h : cs.Perm ds) :
    allocationWordCoefficient cost occupied cs = allocationWordCoefficient cost occupied ds := by
  have he : cs.toFinset = ds.toFinset := by
    ext c
    simpa only [List.mem_toFinset] using h.mem_iff
  rw [allocationWordCoefficient_eq_product, allocationWordCoefficient_eq_product, he]

def actualNodeCost (a b : ℝ) (normalizedFirst : Bool) (k : ℕ) : ℝ :=
  if normalizedFirst = true ∧ k = 0 then 1 else a-(k:ℝ)*b

theorem actualNodeCost_unscaled (a b : ℝ) (occupied : Finset C) (cs : List C) :
    allocationWordCoefficient (actualNodeCost a b false) occupied cs =
      nodeAllocationCoeff a b occupied cs := by
  induction cs generalizing occupied with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c ∈ occupied
    · simp only [allocationWordCoefficient, nodeAllocationCoeff, if_pos hc, ih]
    · simp only [allocationWordCoefficient, nodeAllocationCoeff, if_neg hc, ih]
      simp only [actualNodeCost, Bool.false_eq_true, false_and, ite_false]

theorem actualNodeCost_normalized_first (a b : ℝ) : actualNodeCost a b true 0 = 1 := by
  simp [actualNodeCost]

theorem actualNodeCost_nonempty (a b : ℝ) (e : Bool) {k : ℕ} (hk : 0 < k) :
    actualNodeCost a b e k = a-(k:ℝ)*b := by
  simp [actualNodeCost, hk.ne']

section WholeTree
variable {N L : Type*} [Fintype N]

def visitCoefficient (cost : ℕ → ℝ) (occupied : Finset C) : Option C → ℝ
  | none => 1
  | some c => if c ∈ occupied then 1 else cost occupied.card

def visitOccupied (occupied : Finset C) : Option C → Finset C
  | none => occupied
  | some c => insert c occupied

def treeAllocationCoefficient (cost : N → ℕ → ℝ) (path : L → N → Option C) :
    (N → Finset C) → List L → ℝ
  | _, [] => 1
  | occupied, label::ls =>
      (∏ v, visitCoefficient (cost v) (occupied v) (path label v))*
      treeAllocationCoefficient cost path
        (fun v => visitOccupied (occupied v) (path label v)) ls

private theorem local_filterMap_cons (cost : ℕ → ℝ) (occupied : Finset C)
    (path : L → Option C) (label : L) (ls : List L) :
    allocationWordCoefficient cost occupied ((label::ls).filterMap path) =
      visitCoefficient cost occupied (path label)*
      allocationWordCoefficient cost (visitOccupied occupied (path label)) (ls.filterMap path) := by
  cases hp : path label with
  | none => simp [List.filterMap_cons, hp, visitCoefficient, visitOccupied]
  | some c =>
    by_cases hc : c ∈ occupied
    · simp [List.filterMap_cons, hp, visitCoefficient, visitOccupied, allocationWordCoefficient,
        hc, Finset.insert_eq_of_mem hc]
    · simp [List.filterMap_cons, hp, visitCoefficient, visitOccupied, allocationWordCoefficient, hc]

theorem treeAllocationCoefficient_eq_product (cost : N → ℕ → ℝ)
    (path : L → N → Option C) (occupied : N → Finset C) (ls : List L) :
    treeAllocationCoefficient cost path occupied ls =
      ∏ v, allocationWordCoefficient (cost v) (occupied v) (ls.filterMap (fun l => path l v)) := by
  induction ls generalizing occupied with
  | nil => simp [treeAllocationCoefficient, allocationWordCoefficient]
  | cons label ls ih =>
    rw [treeAllocationCoefficient, ih, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    exact (local_filterMap_cons (cost v) (occupied v) (fun l => path l v) label ls).symm

theorem treeAllocationCoefficient_perm (cost : N → ℕ → ℝ)
    (path : L → N → Option C) (occupied : N → Finset C) {ls rs : List L}
    (h : ls.Perm rs) :
    treeAllocationCoefficient cost path occupied ls =
      treeAllocationCoefficient cost path occupied rs := by
  rw [treeAllocationCoefficient_eq_product, treeAllocationCoefficient_eq_product]
  apply Finset.prod_congr rfl
  intro v hv
  exact allocationWordCoefficient_perm (cost v) (occupied v) (List.Perm.filterMap _ h)

theorem carried_topology_order {Ω : Type*} [Fintype Ω]
    (a b : Ω → N → ℝ) (normalizedFirst : Ω → N → Bool)
    (occupied : Ω → N → Finset C) (path : Ω → L → N → Option C)
    (F : Ω → ℝ) {ls rs : List L} (h : ls.Perm rs) :
    (∑ τ, treeAllocationCoefficient
      (fun v => actualNodeCost (a τ v) (b τ v) (normalizedFirst τ v))
      (path τ) (occupied τ) ls*F τ) =
    ∑ τ, treeAllocationCoefficient
      (fun v => actualNodeCost (a τ v) (b τ v) (normalizedFirst τ v))
      (path τ) (occupied τ) rs*F τ := by
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [treeAllocationCoefficient_perm _ _ _ h]

end WholeTree
end OAI.SKFluctuations.Cavity
