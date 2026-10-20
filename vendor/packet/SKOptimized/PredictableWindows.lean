module

public import Mathlib

/-!
# Finite predictable threshold windows

The finite probability model, backward-coordinate induction, and grid
counting proof below are ported with attribution from openai/math,
`lean/OAI/Probability/SKBarriers/SpinGlass/{FiniteLaw,FiniteProduct}.lean`
and `Dynamics/GridThreshold.lean`. Only their elementary Mathlib-based
closure is copied. The predictable-center and deterministic-profile
window theorems are the interfaces for the optimized successor anchors.
-/

@[expose] public section

namespace SKOptimized

noncomputable section
open scoped BigOperators
open Classical Set

structure FiniteLaw (X : Type*) [Fintype X] where
  weight : X → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  sum_one : ∑ x, weight x=1

namespace FiniteLaw
variable {X Y : Type*} [Fintype X] [Fintype Y]

def expect (P : FiniteLaw X) (f : X → ℝ) : ℝ := ∑ x, P.weight x*f x

def prob (P : FiniteLaw X) (E : X → Prop) : ℝ := P.expect (fun x => if E x then 1 else 0)

theorem expect_nonneg (P : FiniteLaw X) {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hf x))

theorem expect_mono (P : FiniteLaw X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

@[simp] theorem expect_const (P : FiniteLaw X) (c : ℝ) : P.expect (fun _ => c)=c := by
  simp only [expect,← Finset.sum_mul,P.sum_one,one_mul]

@[simp] theorem expect_zero (P : FiniteLaw X) : P.expect (fun _ => 0)=0 := expect_const P 0

theorem expect_add (P : FiniteLaw X) (f g : X → ℝ) :
    P.expect (fun x => f x+g x)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

theorem expect_mul_const (P : FiniteLaw X) (f : X → ℝ) (c : ℝ) :
    P.expect (fun x => f x*c)=P.expect f*c := by
  simp only [expect,← mul_assoc,Finset.sum_mul]

theorem expect_const_mul (P : FiniteLaw X) (c : ℝ) (f : X → ℝ) :
    P.expect (fun x => c*f x)=c*P.expect f := by
  simp_rw [mul_comm c]
  exact expect_mul_const P f c

theorem expect_sum (P : FiniteLaw X) {I : Type*} [Fintype I] (f : I → X → ℝ) :
    P.expect (fun x => ∑ i, f i x)=∑ i, P.expect (f i) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm

theorem prob_nonneg (P : FiniteLaw X) (E : X → Prop) : 0 ≤ P.prob E :=
  P.expect_nonneg (fun x => by split_ifs <;> norm_num)

theorem prob_le_one (P : FiniteLaw X) (E : X → Prop) : P.prob E ≤ 1 := by
  rw [← P.expect_const 1]
  exact P.expect_mono (fun x => by split_ifs <;> norm_num)

theorem prob_mono (P : FiniteLaw X) {E F : X → Prop} (h : ∀ x, E x → F x) : P.prob E ≤ P.prob F := by
  apply P.expect_mono
  intro x
  by_cases he : E x
  · simp only [ite_eq_left he,ite_eq_left (h x he),le_refl]
  · simp only [ite_eq_right he]; split_ifs <;> norm_num

@[simp] theorem prob_true (P : FiniteLaw X) : P.prob (fun _ => True)=1 := by simp [prob]
@[simp] theorem prob_false (P : FiniteLaw X) : P.prob (fun _ => False)=0 := by simp [prob]

theorem prob_not (P : FiniteLaw X) (E : X → Prop) : P.prob (fun x => ¬E x)=1-P.prob E := by
  have he : P.prob E+P.prob (fun x => ¬E x)=1 := by
    rw [prob,prob,← expect_add]
    convert P.expect_const 1 using 2
    funext x
    by_cases h : E x <;> simp [h]
  linarith only [he]

theorem prob_or (P : FiniteLaw X) (E F : X → Prop) :
    P.prob (fun x => E x ∨ F x) ≤ P.prob E+P.prob F := by
  simp only [prob]
  rw [← expect_add]
  apply P.expect_mono
  intro x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf]

theorem prob_exists (P : FiniteLaw X) {I : Type*} [Fintype I] (E : I → X → Prop) :
    P.prob (fun x => ∃ i, E i x) ≤ ∑ i, P.prob (E i) := by
  simp only [prob]
  rw [← expect_sum]
  apply P.expect_mono
  intro x
  by_cases h : ∃ i, E i x
  · rw [ite_eq_left h]
    obtain ⟨i,hi⟩ := h
    exact (by simpa only [ite_eq_left hi] using
      (Finset.single_le_sum (fun j (_ : j∈Finset.univ) => show 0 ≤ (if E j x then (1:ℝ) else 0) by split_ifs <;> norm_num) (Finset.mem_univ i)))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

def prod (P : FiniteLaw X) (Q : FiniteLaw Y) : FiniteLaw (X × Y) where
  weight z := P.weight z.1*Q.weight z.2
  nonneg z := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_one := by simp only [Fintype.sum_prod_type,← Finset.mul_sum,Q.sum_one,mul_one,P.sum_one]

theorem prod_expect (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X × Y → ℝ) :
    (P.prod Q).expect f=P.expect (fun x => Q.expect (fun y => f (x,y))) := by
  simp only [expect,prod,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem prod_expect_fst (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X → ℝ) :
    (P.prod Q).expect (fun z => f z.1)=P.expect f := by
  simp only [prod_expect,expect_const]

theorem prod_expect_snd (P : FiniteLaw X) (Q : FiniteLaw Y) (f : Y → ℝ) :
    (P.prod Q).expect (fun z => f z.2)=Q.expect f := by
  simp only [prod_expect,expect_const]

def pi {I : Type*} [Fintype I] [DecidableEq I] (A : I → Type*) [∀ i, Fintype (A i)] (P : ∀ i, FiniteLaw (A i)) :
    FiniteLaw (∀ i, A i) where
  weight z := ∏ i, (P i).weight (z i)
  nonneg z := Finset.prod_nonneg (fun i _ => (P i).nonneg _)
  sum_one := by rw [← Fintype.prod_sum]; simp only [sum_one,Finset.prod_const_one]

theorem prob_eq_zero_of_support (P : FiniteLaw X) (E : X → Prop)
    (h : ∀ x, 0 < P.weight x → ¬E x) : P.prob E=0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : 0 < P.weight x
  · simp only [ite_eq_right (h x hx),mul_zero]
  · have he : P.weight x=0 := le_antisymm (le_of_not_gt hx) (P.nonneg x)
    simp only [he,zero_mul]

end FiniteLaw

namespace FiniteLaw
variable {X Y : Type*} [Fintype X] [Fintype Y]

def iid (P : FiniteLaw X) (I : Type*) [Fintype I] [DecidableEq I] : FiniteLaw (I → X) :=
  pi (fun _ : I => X) (fun _ => P)

theorem iid_expect_fin_succ (P : FiniteLaw X) (p : ℕ) (f : (Fin (p+1) → X) → ℝ) :
    (P.iid (Fin (p+1))).expect f=
      (P.iid (Fin p)).expect (fun z => P.expect (fun a => f (Fin.snoc z a))) := by
  classical
  unfold expect iid pi
  calc
    _ = ∑ z : (Fin p → X) × X, (∏ i, P.weight (z.1 i))*P.weight z.2*f (Fin.snoc z.1 z.2) := by
      apply Fintype.sum_equiv ((Fin.snocEquiv (fun _ : Fin (p+1) => X)).symm.trans (Equiv.prodComm _ _))
      intro z
      simp only [Equiv.trans_apply,Equiv.prodComm_apply,Fin.snocEquiv_symm_apply,Prod.swap,Fin.prod_univ_castSucc]
      simp only [Fin.snoc_init_self,Fin.init]
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem iid_expect_zero (P : FiniteLaw X) (f : (Fin 0 → X) → ℝ) :
    (P.iid (Fin 0)).expect f=f Fin.elim0 := by
  classical
  unfold expect iid pi
  rw [Fintype.sum_unique]
  simp only [Fin.prod_univ_zero,one_mul]
  congr 1

theorem iid_predictable_bound (P : FiniteLaw X) (E : (j : ℕ) → (Fin j → X) → X → Prop)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hE : ∀ j z, P.prob (E j z) ≤ a j) (p : ℕ) :
    (P.iid (Fin p)).prob (fun z => ∀ i : Fin p,
      E i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) (z i)) ≤ ∏ i : Fin p, a i := by
  classical
  induction p with
  | zero => simp [prob]
  | succ p ih =>
    simp only [prob] at ih ⊢
    rw [iid_expect_fin_succ]
    have H : (P.iid (Fin p)).expect (fun z => P.expect (fun b =>
        if ∀ i : Fin (p+1), E i.val (fun j => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.isLt⟩) (Fin.snoc (α := fun _ : Fin (p+1) => X) z b i)
        then 1 else 0)) ≤
        (P.iid (Fin p)).expect (fun z => (if ∀ i : Fin p,
          E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i) then 1 else 0)*a p) := by
      apply expect_mono
      intro z
      have hpref (b : X) (i : Fin p) :
          (fun j : Fin i.val => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.castSucc.isLt⟩) =
          (fun j : Fin i.val => z ⟨j.val,j.isLt.trans i.isLt⟩) := by
        funext j
        exact Fin.snoc_castSucc (α := fun _ : Fin (p+1) => X) b z ⟨j.val,j.isLt.trans i.isLt⟩
      have hlast (b : X) : (fun j : Fin p => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans (Nat.lt_succ_self p)⟩)=z := by
        funext j
        exact Fin.snoc_castSucc (α := fun _ : Fin (p+1) => X) b z j
      have heq (b : X) : (∀ i : Fin (p+1),
          E i.val (fun j => Fin.snoc (α := fun _ : Fin (p+1) => X) z b ⟨j.val,j.isLt.trans i.isLt⟩) (Fin.snoc (α := fun _ : Fin (p+1) => X) z b i)) ↔
          (∀ i : Fin p, E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i)) ∧ E p z b := by
        rw [Fin.forall_iff_castSucc, and_comm]
        constructor
        · intro h
          constructor
          · intro i
            simpa only [Fin.val_castSucc,Fin.snoc_castSucc,hpref] using h.1 i
          · simpa only [Fin.val_last,Fin.snoc_last,hlast] using h.2
        · rintro ⟨h,hp⟩
          constructor
          · intro i
            simpa only [Fin.val_castSucc,Fin.snoc_castSucc,hpref] using h i
          · simpa only [Fin.val_last,Fin.snoc_last,hlast] using hp
      simp_rw [heq]
      by_cases hz : ∀ i : Fin p, E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i)
      · simpa [hz,prob] using hE p z
      · simp only [hz,false_and,ite_false,zero_mul,expect_zero,le_refl]
    convert H.trans (show (P.iid (Fin p)).expect (fun z => (if ∀ i : Fin p,
          E i.val (fun j => z ⟨j.val,j.isLt.trans i.isLt⟩) (z i) then 1 else 0)*a p) ≤ ∏ i : Fin (p+1), a i from by
      rw [expect_mul_const,Fin.prod_univ_castSucc]
      apply mul_le_mul_of_nonneg_right _ (ha p)
      convert ih using 1 <;> first | rfl | (congr 1; funext z; split_ifs <;> rfl)) using 1
    all_goals first | rfl | (congr 1; funext z; congr 1; funext b; split_ifs <;> rfl)

end FiniteLaw

namespace FiniteLaw
def uniformFin (n : ℕ) (hn : 0 < n) : FiniteLaw (Fin n) where
  weight _ := 1/(n:ℝ)
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

theorem uniformFin_prob (n : ℕ) (hn : 0 < n) (E : Fin n → Prop) :
    (uniformFin n hn).prob E=(Finset.univ.filter E).card/(n:ℝ) := by
  simp only [prob,expect,uniformFin,← Finset.mul_sum]
  rw [Finset.sum_boole]
  ring

end FiniteLaw

def thresholdGrid (n : ℕ) (a ρ : ℝ) (i : Fin n) : ℝ := a+ρ*(i:ℕ)/(n:ℝ)

theorem thresholdGrid_mem {n : ℕ} (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ)
    (a : ℝ) (i : Fin n) : thresholdGrid n a ρ i ∈ Icc a (a+ρ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hi : (i:ℝ)<n := by exact_mod_cast i.isLt
  unfold thresholdGrid
  constructor
  · have : 0 ≤ ρ*(i:ℕ)/(n:ℝ) := by positivity
    linarith only [this]
  · have : ρ*(i:ℕ)/(n:ℝ) ≤ ρ := (div_le_iff₀ hnR).mpr (by gcongr)
    linarith only [this]

theorem thresholdGrid_count {n : ℕ} (hn : 0 < n) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w)
    (a x : ℝ) :
    ((Finset.univ.filter (fun i : Fin n => |thresholdGrid n a ρ i-x| ≤ w)).card:ℝ) ≤
      2*w*(n:ℝ)/ρ+1 := by
  let S := Finset.univ.filter (fun i : Fin n => |thresholdGrid n a ρ i-x| ≤ w)
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  by_cases hs : S.Nonempty
  · let i := S.min' hs
    let j := S.max' hs
    have hi : i∈S := Finset.min'_mem S hs
    have hj : j∈S := Finset.max'_mem S hs
    have hij : i≤j := Finset.min'_le S j hj
    have hcard : S.card ≤ (j:ℕ)+1-(i:ℕ) := by
      rw [← Fin.card_Icc]
      apply Finset.card_le_card
      intro z hz
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le S z hz,Finset.le_max' S z hz⟩
    have hcard' : (S.card:ℝ) ≤ (j:ℝ)-(i:ℝ)+1 := by
      have hnat : (i:ℕ)≤(j:ℕ)+1 := by omega
      have hc : (S.card:ℝ) ≤ (((j:ℕ)+1-(i:ℕ):ℕ):ℝ) := by exact_mod_cast hcard
      rw [Nat.cast_sub hnat,Nat.cast_add,Nat.cast_one] at hc
      linarith only [hc]
    have hdi := abs_le.mp ((Finset.mem_filter.mp hi).2)
    have hdj := abs_le.mp ((Finset.mem_filter.mp hj).2)
    have hgap : ρ*((j:ℝ)-(i:ℝ)) ≤ 2*w*(n:ℝ) := by
      have H : thresholdGrid n a ρ j-thresholdGrid n a ρ i ≤ 2*w := by linarith only [hdi.1,hdj.2]
      have HH : thresholdGrid n a ρ j-thresholdGrid n a ρ i=ρ*((j:ℝ)-(i:ℝ))/(n:ℝ) := by
        unfold thresholdGrid
        ring
      rw [HH,div_le_iff₀ hnR] at H
      exact H
    have hgap' : (j:ℝ)-(i:ℝ) ≤ 2*w*(n:ℝ)/ρ := (le_div_iff₀ hρ).mpr (by nlinarith only [hgap])
    exact hcard'.trans (by linarith only [hgap'])
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (S.card:ℝ)≤_
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem thresholdGrid_window {n : ℕ} (hn : 0 < n) {ρ w : ℝ} (hρ : 0 < ρ) (hw : 0 ≤ w)
    (a x : ℝ) :
    (FiniteLaw.uniformFin n hn).prob (fun i => |thresholdGrid n a ρ i-x| ≤ w) ≤ 2*w/ρ+1/(n:ℝ) := by
  rw [FiniteLaw.uniformFin_prob]
  have h := div_le_div_of_nonneg_right (thresholdGrid_count hn hρ hw a x) (by positivity : (0:ℝ)≤n)
  refine h.trans_eq ?_
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

/-- Finite predictable centers produce a product bound with the exact
finite-grid correction. The center at coordinate `j` can use all prior
coordinates but cannot use coordinate `j` itself. -/
theorem predictable_grid_windows_bound {N : ℕ} (hN : 0 < N)
    (center : (j : ℕ) → (Fin j → Fin N) → ℝ)
    (offset radius : ℕ → ℝ) (width : ℝ) (hwidth : 0 < width)
    (hradius : ∀ j, 0 ≤ radius j) (p : ℕ) :
    ((FiniteLaw.uniformFin N hN).iid (Fin p)).prob (fun z => ∀ i : Fin p,
      |center i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
        thresholdGrid N (offset i.val) width (z i)| ≤ radius i.val) ≤
      ∏ i : Fin p, (2 * radius i.val / width + 1 / (N : ℝ)) := by
  let P := FiniteLaw.uniformFin N hN
  let E (j : ℕ) (z : Fin j → Fin N) (u : Fin N) :=
    |center j z - thresholdGrid N (offset j) width u| ≤ radius j
  apply P.iid_predictable_bound E
    (fun j => 2 * radius j / width + 1 / (N : ℝ))
    (fun j => by have hrad := hradius j; positivity)
  intro j z
  simpa only [E, abs_sub_comm] using
    thresholdGrid_window hN hwidth (hradius j) (offset j) (center j z)

/-- A deterministic retained-pattern profile can require windows only at
selected indices. This is the genuine input for prefix-pattern unions;
no adaptive retained set is conditioned on. -/
theorem predictable_grid_profile_bound {N : ℕ} (hN : 0 < N)
    (center : (j : ℕ) → (Fin j → Fin N) → ℝ)
    (offset radius : ℕ → ℝ) (selected : ℕ → Prop)
    (width : ℝ) (hwidth : 0 < width)
    (hradius : ∀ j, 0 ≤ radius j) (p : ℕ) :
    ((FiniteLaw.uniformFin N hN).iid (Fin p)).prob (fun z => ∀ i : Fin p,
      selected i.val →
      |center i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
        thresholdGrid N (offset i.val) width (z i)| ≤ radius i.val) ≤
      ∏ i : Fin p, if selected i.val then
        (2 * radius i.val / width + 1 / (N : ℝ)) else 1 := by
  classical
  let P := FiniteLaw.uniformFin N hN
  let E (j : ℕ) (z : Fin j → Fin N) (u : Fin N) := selected j →
    |center j z - thresholdGrid N (offset j) width u| ≤ radius j
  apply P.iid_predictable_bound E
    (fun j => if selected j then 2 * radius j / width + 1 / (N : ℝ) else 1)
    (fun j => by have hrad := hradius j; split_ifs <;> positivity)
  intro j z
  by_cases hj : selected j
  · simp only [ite_eq_left hj]
    simpa only [E, hj, true_implies, abs_sub_comm] using
      thresholdGrid_window hN hwidth (hradius j) (offset j) (center j z)
  · simp only [ite_eq_right hj]
    exact P.prob_le_one _

/-- The probability union over a finite family of deterministic retained
profiles is bounded by the sum of the corresponding product bounds. -/
theorem predictable_grid_profile_union_bound {N : ℕ} (hN : 0 < N)
    {I : Type*} [Fintype I]
    (center : (j : ℕ) → (Fin j → Fin N) → ℝ)
    (offset : ℕ → ℝ) (radius : I → ℕ → ℝ) (selected : I → ℕ → Prop)
    (width : ℝ) (hwidth : 0 < width)
    (hradius : ∀ a j, 0 ≤ radius a j) (p : ℕ) :
    ((FiniteLaw.uniformFin N hN).iid (Fin p)).prob (fun z => ∃ a : I,
      ∀ i : Fin p, selected a i.val →
      |center i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
        thresholdGrid N (offset i.val) width (z i)| ≤ radius a i.val) ≤
      ∑ a : I, ∏ i : Fin p, if selected a i.val then
        (2 * radius a i.val / width + 1 / (N : ℝ)) else 1 := by
  classical
  apply (FiniteLaw.prob_exists _ _).trans
  apply Finset.sum_le_sum
  intro a _
  exact predictable_grid_profile_bound hN center offset (radius a)
    (selected a) width hwidth (hradius a) p

/-- If the exact finite profile union bound is less than one, there is
an auxiliary threshold tuple satisfying no profile. In the bank dynamics
argument this contradicts a threshold-independent sign passage whose
anchor invariant would produce a profile for every threshold tuple. -/
theorem exists_grid_without_profile {N : ℕ} (hN : 0 < N)
    {I : Type*} [Fintype I]
    (center : (j : ℕ) → (Fin j → Fin N) → ℝ)
    (offset : ℕ → ℝ) (radius : I → ℕ → ℝ) (selected : I → ℕ → Prop)
    (width : ℝ) (hwidth : 0 < width)
    (hradius : ∀ a j, 0 ≤ radius a j) (p : ℕ)
    (hcount : (∑ a : I, ∏ i : Fin p, if selected a i.val then
        (2 * radius a i.val / width + 1 / (N : ℝ)) else 1) < 1) :
    ∃ z : Fin p → Fin N, ¬∃ a : I,
      ∀ i : Fin p, selected a i.val →
      |center i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
        thresholdGrid N (offset i.val) width (z i)| ≤ radius a i.val := by
  classical
  by_contra h
  push Not at h
  let P := (FiniteLaw.uniformFin N hN).iid (Fin p)
  have hfull : 1 ≤ P.prob (fun z => ∃ a : I,
      ∀ i : Fin p, selected a i.val →
      |center i.val (fun j => z ⟨j.val, j.isLt.trans i.isLt⟩) -
        thresholdGrid N (offset i.val) width (z i)| ≤ radius a i.val) := by
    rw [← P.prob_true]
    exact P.prob_mono (fun z _ => h z)
  have hbound := predictable_grid_profile_union_bound hN center offset radius
    selected width hwidth hradius p
  exact (not_lt_of_ge (hfull.trans hbound)) hcount

end

end SKOptimized
