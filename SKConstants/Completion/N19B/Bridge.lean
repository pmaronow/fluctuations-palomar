module

public import SKConstants.Completion.Blueprint5.ContinuityStatements
public import SKConstants.Completion.N19.Rotation
import Mathlib.Tactic

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N19B
open GaussianProposal Blueprint Blueprint4 N19 N19n BrownianNormCaps
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem coarsePrefix_castAux_bridge_eq (δ : ℝ≥0) (q : ℕ) {N M : ℕ}
    (h : N = M) (a : N13a.PrefixAux δ N q) (j : ℕ) (i : Fin M) :
    (N13a.coarsePrefix_castAux δ q h a).1.2 j i = a.1.2 j (Fin.cast h.symm i) := by
  subst M
  rfl

theorem coarseReplayAux_bridge_eq (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f)
    (a : FineAux p n) (j : ℕ) (i : Fin (rankCount p.a p.b n + queryCount p.a p.b n)) :
    (coarseReplayAux p n hbf a).1.2 j i =
      a.1.2 j (Fin.cast (N13a.coarsePrefix_dimension p n).symm i) := by
  unfold coarseReplayAux N13a.coarsePrefix_fineAux N13a.coarsePrefix_replayAux
  dsimp only [Function.comp_apply]
  rw [coarsePrefix_castAux_bridge_eq]
  rfl

theorem path_norm_le_of_energy_le {H : ℝ≥0} {n : ℕ}
    (f : Fin n → ScalarContinuousPath H) (R : ℝ) (hR : 0 ≤ R)
    (hE : pathEnergy n f ≤ R ^ 2) (i : Fin n) : ‖f i‖ ≤ R := by
  have hi : ‖f i‖ ^ 2 ≤ pathEnergy n f :=
    Finset.single_le_sum (fun k _ => sq_nonneg ‖f k‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (f i)]

theorem coarse_bridge_sum_sub_norm_le (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f)
    (θ φ : ℝ) (ω : Internal p n) (j : ℕ) (R S : ℝ)
    (hR : ∀ i, ‖ω.2.1.1.1.2 j i‖ ≤ R)
    (hS : ∀ i, ‖ω.2.1.2.1.2 j i‖ ≤ S) :
    (∑ i, ‖(coarseReplayAux p n hbf (angleAux p n θ ω)).1.2 j i -
      (coarseReplayAux p n hbf (angleAux p n φ ω)).1.2 j i‖) ≤
      (n : ℝ) * (R + S) * |θ - φ| := by
  calc
    _ ≤ ∑ _i : Fin (rankCount p.a p.b n + queryCount p.a p.b n),
        |θ - φ| * (R + S) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [coarseReplayAux_bridge_eq, coarseReplayAux_bridge_eq]
      exact (angleAux_bridge_sub_norm_le p n j θ φ ω _).trans
        (mul_le_mul_of_nonneg_left (add_le_add (hR _) (hS _)) (abs_nonneg _))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      rankCount_add, nsmul_eq_mul]; ring

theorem used_queryDuration_le_one (a L : ℝ) (hL : 0 ≤ L) (ha : L / 4 ≤ a)
    (n : ℕ) (hn : 0 < n) (j : Fin (queryCount a L n)) :
    growingQueryDuration (meshSize a n) (j.val + 1) ≤ 1 := by
  apply paperGrowingQueryStop_small a L hL ha n hn
  have hq : queryCount a L n ≤ stopIndex a L n - 1 := min_le_left _ _
  rw [stopIndex_eq a L n hn] at hq
  omega

theorem replayAuxCap_bridge_norm_le (δ : ℝ≥0) (r q : ℕ) (CB CD R A : ℝ)
    (hCD : 0 ≤ CD) (hA : 0 ≤ A) (hsize : 4 * CD * (r + q : ℕ) ≤ A ^ 2)
    (a : ReplayAux δ r q) (ha : a ∈ replayAuxCap δ r q CB CD R)
    (j : ℕ) (hj : j ∈ Finset.range (q + 1))
    (hsmall : (growingQueryDuration δ j : ℝ) ≤ 1) (i : Fin (r + q)) :
    ‖a.1.2 j i‖ ≤ A := by
  apply path_norm_le_of_energy_le _ A hA
  calc
    pathEnergy (r + q) (a.1.2 j) ≤
        4 * (growingQueryDuration δ j : ℝ) * CD * (r + q : ℕ) :=
      (ha.2.1 j hj).le
    _ = (growingQueryDuration δ j : ℝ) * (4 * CD * (r + q : ℕ)) := by ring
    _ ≤ 1 * (4 * CD * (r + q : ℕ)) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ ≤ A ^ 2 := by simpa using hsize

theorem coarse_bridge_sum_sub_norm_le_on_cap (p : Parameters) (n : ℕ)
    (hbf : p.b ≤ p.f) (hn : 2 ≤ n) (CB CD R : ℝ) (hCD : 0 ≤ CD)
    (hnCD : 4 * CD ≤ n) (θ φ : ℝ) (z : Outer n × Internal p n)
    (hz : z ∈ experimentCap p n CB CD R) (j : Fin (queryCount p.a p.b n))
    (hsmall : growingQueryDuration (meshSize p.a n) (j.val + 1) ≤ 1) :
    (∑ i, ‖(coarseReplayAux p n hbf (angleAux p n θ z.2)).1.2 (j.val + 1) i -
      (coarseReplayAux p n hbf (angleAux p n φ z.2)).1.2 (j.val + 1) i‖) ≤
      (n : ℝ) ^ (3 : ℕ) * |θ - φ| := by
  have hsize : 4 * CD * (rankCount p.a p.f n + queryCount p.a p.f n : ℕ) ≤
      (n : ℝ) ^ 2 := by
    rw [rankCount_add]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hj : j.val + 1 ∈ Finset.range (queryCount p.a p.f n + 1) := by
    have hq := queryCount_mono p.a p.b p.f hbf n
    simp only [Finset.mem_range]
    omega
  have hcap₁ : z.2.2.1.1 ∈ replayAuxCap (meshSize p.a n)
      (rankCount p.a p.f n) (queryCount p.a p.f n) CB CD R := hz.2.2.2.2.1
  have hcap₂ : z.2.2.1.2 ∈ replayAuxCap (meshSize p.a n)
      (rankCount p.a p.f n) (queryCount p.a p.f n) CB CD R := hz.2.2.2.2.2
  have h₁ := replayAuxCap_bridge_norm_le _ _ _ CB CD R n hCD (Nat.cast_nonneg n)
    hsize _ hcap₁ (j.val + 1) hj (by exact_mod_cast hsmall)
  have h₂ := replayAuxCap_bridge_norm_le _ _ _ CB CD R n hCD (Nat.cast_nonneg n)
    hsize _ hcap₂ (j.val + 1) hj (by exact_mod_cast hsmall)
  calc
    _ ≤ (n : ℝ) * (n + n) * |θ - φ| :=
      coarse_bridge_sum_sub_norm_le p n hbf θ φ z.2 (j.val + 1) n n h₁ h₂
    _ ≤ (n : ℝ) ^ 3 * |θ - φ| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg (n : ℝ), mul_nonneg (sub_nonneg.mpr hnR) (sq_nonneg (n : ℝ))]

theorem coarse_bridge_bounds_eventually (p : Parameters) (hbf : p.b ≤ p.f)
    (hb : 0 ≤ p.b) (ha : p.b / 4 ≤ p.a) (CB CD : ℝ) (hCD : 0 ≤ CD) :
    ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ) (z : Outer n × Internal p n),
      z ∈ experimentCap p n CB CD n → ∀ j : Fin (queryCount p.a p.b n),
      (∑ i, ‖(coarseReplayAux p n hbf (angleAux p n θ z.2)).1.2 (j.val + 1) i -
        (coarseReplayAux p n hbf (angleAux p n φ z.2)).1.2 (j.val + 1) i‖) ≤
        (n : ℝ) ^ (3 : ℕ) * |θ - φ| := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * CD)
  filter_upwards [eventually_ge_atTop (max 2 N)] with n hn θ φ z hz j
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  have hnCD : 4 * CD ≤ n := hN.trans (by exact_mod_cast hNn)
  exact coarse_bridge_sum_sub_norm_le_on_cap p n hbf hn2 CB CD n hCD hnCD θ φ z hz j
    (used_queryDuration_le_one p.a p.b hb ha n (by omega) j)

end SKConstants.Completion.N19B
