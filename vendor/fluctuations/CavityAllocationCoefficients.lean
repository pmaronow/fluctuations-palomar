module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open scoped BigOperators

theorem realPowerNode_new_child {a b I : ℝ} (hb : 0 < b) (hI : 0 < I) (k : ℕ) :
    HasDerivAt (fun t : ℝ => b*t^(a/b-(k:ℝ)))
      ((a-(k:ℝ)*b)*I^(a/b-(k:ℝ)-1)) I := by
  have hd := (Real.hasDerivAt_rpow_const (x := I) (p := a/b-(k:ℝ)) (Or.inl hI.ne')).const_mul b
  convert hd using 1
  field_simp [hb.ne']

def nodeCoefficient (a b : ℝ) (k h : ℕ) : ℝ :=
  ∏ j ∈ Finset.range h, (a-((k+j:ℕ):ℝ)*b)

theorem nodeCoefficient_zero (a b : ℝ) (k : ℕ) : nodeCoefficient a b k 0 = 1 := by
  simp [nodeCoefficient]

theorem nodeCoefficient_succ (a b : ℝ) (k h : ℕ) :
    nodeCoefficient a b k (h+1) = (a-(k:ℝ)*b)*nodeCoefficient a b (k+1) h := by
  rw [nodeCoefficient, Finset.prod_range_succ']
  rw [mul_comm]
  simp only [Nat.add_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [show k+(j+1) = (k+1)+j by omega]

variable {C : Type*} [DecidableEq C]

def nodeAllocationCoeff (a b : ℝ) : Finset C → List C → ℝ
  | _, [] => 1
  | occupied, c::cs => if c ∈ occupied then nodeAllocationCoeff a b occupied cs
      else (a-(occupied.card:ℝ)*b)*nodeAllocationCoeff a b (insert c occupied) cs

def newChildren : Finset C → List C → List C
  | _, [] => []
  | occupied, c::cs => if c ∈ occupied then newChildren occupied cs
      else c::newChildren (insert c occupied) cs

theorem nodeAllocationCoeff_eq_polynomial (a b : ℝ) (occupied : Finset C) (cs : List C) :
    nodeAllocationCoeff a b occupied cs =
      nodeCoefficient a b occupied.card (newChildren occupied cs).length := by
  induction cs generalizing occupied with
  | nil => simp [nodeAllocationCoeff, newChildren, nodeCoefficient]
  | cons c cs ih =>
    by_cases hc : c ∈ occupied
    · simp only [nodeAllocationCoeff, newChildren, if_pos hc, ih]
    · simp only [nodeAllocationCoeff, newChildren, if_neg hc, List.length_cons,
        nodeCoefficient_succ, Finset.card_insert_of_notMem hc, ih]

theorem newChildren_finset (occupied : Finset C) (cs : List C) :
    (newChildren occupied cs).toFinset = cs.toFinset \ occupied := by
  induction cs generalizing occupied with
  | nil => simp [newChildren]
  | cons c cs ih =>
    by_cases hc : c ∈ occupied
    · simp only [newChildren, if_pos hc, ih, List.toFinset_cons]
      ext d
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    · simp only [newChildren, if_neg hc, List.toFinset_cons, ih]
      ext d
      simp only [Finset.mem_insert, Finset.mem_sdiff]
      by_cases hdc : d = c
      · subst d; simp [hc]
      aesop

theorem newChildren_nodup (occupied : Finset C) (cs : List C) :
    (newChildren occupied cs).Nodup := by
  induction cs generalizing occupied with
  | nil => simp [newChildren]
  | cons c cs ih =>
    by_cases hc : c ∈ occupied
    · simp only [newChildren, if_pos hc]
      exact ih _
    · simp only [newChildren, if_neg hc, List.nodup_cons]
      refine ⟨?_, ih _⟩
      intro hm
      have hf : c ∈ (newChildren (insert c occupied) cs).toFinset := List.mem_toFinset.mpr hm
      rw [newChildren_finset] at hf
      exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_insert_self _ _)

theorem newChildren_length (occupied : Finset C) (cs : List C) :
    (newChildren occupied cs).length = (cs.toFinset \ occupied).card := by
  rw [← newChildren_finset, List.toFinset_card_of_nodup (newChildren_nodup occupied cs)]

theorem nodeAllocationCoeff_perm (a b : ℝ) (occupied : Finset C) {cs ds : List C}
    (h : cs.Perm ds) : nodeAllocationCoeff a b occupied cs = nodeAllocationCoeff a b occupied ds := by
  have he : cs.toFinset = ds.toFinset := by
    ext c
    simpa only [List.mem_toFinset] using h.mem_iff
  rw [nodeAllocationCoeff_eq_polynomial, nodeAllocationCoeff_eq_polynomial,
    newChildren_length, newChildren_length, he]

theorem nodeCoefficient_eq_scaled_falling {a b : ℝ} (hb : b ≠ 0) (k h : ℕ) :
    nodeCoefficient a b k h = b^h*∏ j ∈ Finset.range h, (a/b-(k:ℝ)-(j:ℝ)) := by
  rw [nodeCoefficient]
  have he (j : ℕ) : a-((k+j:ℕ):ℝ)*b = b*(a/b-(k:ℝ)-(j:ℝ)) := by
    push_cast
    field_simp [hb]
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

end OAI.SKFluctuations.Cavity
