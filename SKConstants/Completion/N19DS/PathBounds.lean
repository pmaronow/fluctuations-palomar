module

public import SKConstants.Completion.Blueprint5.ContinuityStatements
import Mathlib.Tactic

@[expose] public section
noncomputable section
open Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N19DS
open GaussianProposal Blueprint Blueprint4 N19 N19n BrownianNormCaps
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem restriction_sub_norm_le (H h : ℝ≥0) (hh : h ≤ H)
    (F G : ScalarContinuousPath H) :
    ‖scalarInitialAuxiliaryRestriction H h hh F -
      scalarInitialAuxiliaryRestriction H h hh G‖ ≤ ‖F - G‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  exact (F - G).norm_coe_le_norm ⟨t, t.property.1, t.property.2.trans hh⟩

theorem initialAuxiliaryB_sub_norm_le (H h : ℝ≥0)
    (F G : ScalarContinuousPath h) :
    ‖scalarInitialAuxiliaryB H h F - scalarInitialAuxiliaryB H h G‖ ≤ ‖F - G‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  exact (F - G).norm_coe_le_norm (projIcc 0 (h : ℝ) h.coe_nonneg (t : ℝ))

theorem norm_le_of_pathEnergy_le_sq {H : ℝ≥0} {n : ℕ}
    (F : Fin n → ScalarContinuousPath H) (R : ℝ) (hR : 0 ≤ R)
    (hF : pathEnergy n F ≤ R ^ 2) (i : Fin n) : ‖F i‖ ≤ R := by
  have hi : ‖F i‖ ^ 2 ≤ pathEnergy n F :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖F j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (F i)]

theorem initialDuration_le_horizon (δ : ℝ≥0) (q : ℕ) :
    growingQueryDuration δ 0 ≤ scalarGrowingSourceHorizon δ q := by
  have h := M1.growingQueryTime_monotone δ (show 1 ≤ q + 1 by omega)
  simpa only [scalarGrowingSourceHorizon, growingQueryTime_succ,
    growingQueryTime_zero, zero_add] using h

theorem replayAuxCap_path_norms_le (δ : ℝ≥0) (r q : ℕ) (CB CD R A : ℝ)
    (hCB : 0 ≤ CB) (hA : 0 ≤ A) (a : ReplayAux δ r q)
    (ha : a ∈ replayAuxCap δ r q CB CD R)
    (hsize : (scalarGrowingSourceHorizon δ q : ℝ) * CB * (r + q : ℕ) ≤ A ^ 2) :
    (∀ i, ‖a.1.1 i‖ ≤ A) ∧ (∀ i, ‖a.2.2 i‖ ≤ A) := by
  have htime : (growingQueryDuration δ 0 : ℝ) ≤ scalarGrowingSourceHorizon δ q :=
    NNReal.coe_le_coe.mpr (initialDuration_le_horizon δ q)
  refine ⟨norm_le_of_pathEnergy_le_sq _ A hA ?_,
    norm_le_of_pathEnergy_le_sq _ A hA (ha.2.2.2.le.trans hsize)⟩
  exact ha.1.le.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right htime hCB) (Nat.cast_nonneg _)).trans hsize)

theorem castAux_initial (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m)
    (a : N13a.PrefixAux δ n q) (i : Fin m) :
    (N13a.coarsePrefix_castAux δ q h a).1.1 i = a.1.1 (Fin.cast h.symm i) := by
  subst m
  rfl

theorem castAux_D (δ : ℝ≥0) (q : ℕ) {n m : ℕ} (h : n = m)
    (a : N13a.PrefixAux δ n q) (i : Fin m) :
    (N13a.coarsePrefix_castAux δ q h a).2.2 i = a.2.2 (Fin.cast h.symm i) := by
  subst m
  rfl

theorem coarsePrefix_initial (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf + qf = rb + qb) (hq : qb ≤ qf) (a : ReplayAux δ rf qf)
    (i : Fin (rb + qb)) :
    (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq a).1.1 i =
      a.1.1 (Fin.cast hdim.symm i) := by
  unfold N13a.coarsePrefix_replayAux
  rw [Function.comp_apply, castAux_initial]
  rfl

theorem coarsePrefix_D_sub_norm_le (δ : ℝ≥0) (rf qf rb qb : ℕ)
    (hdim : rf + qf = rb + qb) (hq : qb ≤ qf) (a b : ReplayAux δ rf qf)
    (i : Fin (rb + qb)) :
    ‖(N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq a).2.2 i -
      (N13a.coarsePrefix_replayAux δ rf qf rb qb hdim hq b).2.2 i‖ ≤
        ‖a.2.2 (Fin.cast hdim.symm i) - b.2.2 (Fin.cast hdim.symm i)‖ := by
  unfold N13a.coarsePrefix_replayAux
  simp only [Function.comp_apply, castAux_D]
  exact restriction_sub_norm_le _ _
    (M1.growingQueryTime_monotone δ (Nat.add_le_add_right hq 1)) _ _

theorem replayStart_path_sub_norm_le (δ : ℝ≥0) (r q : ℕ) (a b : ReplayAux δ r q)
    (i : Fin (r + q)) :
    ‖(replayStart δ r q a).2 i - (replayStart δ r q b).2 i‖ ≤
      ‖a.1.1 i - b.1.1 i‖ :=
  initialAuxiliaryB_sub_norm_le _ _ _ _

theorem fine_pathEnergy_scale_eventually (p : Parameters) (hf : FineExponents p)
    (CB : ℝ) (hCB : 0 < CB) :
    ∀ᶠ n : ℕ in atTop,
      (scalarGrowingSourceHorizon (meshSize p.a n) (queryCount p.a p.f n) : ℝ) *
        CB * n ≤ (n : ℝ) ^ 2 := by
  have hf0 : 0 < p.f := lt_trans hf.2.2.1 hf.2.2.2.2.1
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  filter_upwards [schedule_eventually p.a p.f hf0 hf.1.le ha1,
    amplification_log_le 0 1 (CB * p.f) (1 / 2) (by norm_num)
      (mul_pos hCB hf0).le (by norm_num),
    constant_rpow_le_small_rpow 0 1 CB (1 / 2) (by norm_num) hCB.le (by norm_num)]
    with n hs hlog hconst
  simp only [Real.rpow_zero, Real.rpow_one, mul_one] at hlog hconst
  have hH := (horizon_bounds p.a p.f hf0 hf.1.le n hs.1 hs.2.1).2
  have hbudget :
      (scalarGrowingSourceHorizon (meshSize p.a n) (queryCount p.a p.f n) : ℝ) * CB ≤ n := by
    have hm := mul_le_mul_of_nonneg_right hH hCB.le
    nlinarith
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg n)

theorem fineAux_cap_path_norms_eventually (p : Parameters) (hf : FineExponents p)
    (CB : ℝ) (hCB : 0 < CB) (CD : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (R : ℝ) (a : FineAux p n),
      a ∈ replayAuxCap (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) CB CD R →
      (∀ i, ‖a.1.1 i‖ ≤ n) ∧ (∀ i, ‖a.2.2 i‖ ≤ n) := by
  filter_upwards [fine_pathEnergy_scale_eventually p hf CB hCB] with n hn
  intro R a ha
  exact replayAuxCap_path_norms_le _ _ _ CB CD R n hCB.le (Nat.cast_nonneg n) a ha
    (by simpa only [rankCount_add] using hn)

theorem coarse_D_rotation_bound (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f)
    (R θ φ : ℝ) (ω : Internal p n)
    (h₁ : ∀ i, ‖ω.2.1.1.2.2 i‖ ≤ R) (h₂ : ∀ i, ‖ω.2.1.2.2.2 i‖ ≤ R)
    (i : Fin (rankCount p.a p.b n + queryCount p.a p.b n)) :
    ‖(coarseReplayAux p n hbf (angleAux p n θ ω)).2.2 i -
      (coarseReplayAux p n hbf (angleAux p n φ ω)).2.2 i‖ ≤ (2 * R) * |θ - φ| := by
  let k := Fin.cast (N13a.coarsePrefix_dimension p n).symm i
  calc
    _ ≤ ‖(angleAux p n θ ω).2.2 k - (angleAux p n φ ω).2.2 k‖ :=
      coarsePrefix_D_sub_norm_le _ _ _ _ _ _ _ _ _ _
    _ ≤ |θ - φ| * (‖ω.2.1.1.2.2 k‖ + ‖ω.2.1.2.2.2 k‖) :=
      angleAux_D_sub_norm_le p n θ φ ω k
    _ ≤ |θ - φ| * (R + R) :=
      mul_le_mul_of_nonneg_left (add_le_add (h₁ k) (h₂ k)) (abs_nonneg _)
    _ = _ := by ring

theorem coarse_start_rotation_bound (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f)
    (R θ φ : ℝ) (ω : Internal p n)
    (h₁ : ∀ i, ‖ω.2.1.1.1.1 i‖ ≤ R) (h₂ : ∀ i, ‖ω.2.1.2.1.1 i‖ ≤ R) :
    scalarMeshPathGap
      (replayStart (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
        (coarseReplayAux p n hbf (angleAux p n θ ω)))
      (replayStart (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
        (coarseReplayAux p n hbf (angleAux p n φ ω))) ≤
      (2 * R * n) * |θ - φ| := by
  unfold scalarMeshPathGap
  calc
    _ ≤ ∑ i : Fin (rankCount p.a p.b n + queryCount p.a p.b n), (2 * R) * |θ - φ| := by
      apply Finset.sum_le_sum
      intro i _
      let k := Fin.cast (N13a.coarsePrefix_dimension p n).symm i
      calc
        _ ≤ ‖(coarseReplayAux p n hbf (angleAux p n θ ω)).1.1 i -
              (coarseReplayAux p n hbf (angleAux p n φ ω)).1.1 i‖ :=
          replayStart_path_sub_norm_le _ _ _ _ _ _
        _ = ‖(angleAux p n θ ω).1.1 k - (angleAux p n φ ω).1.1 k‖ := by
          unfold coarseReplayAux N13a.coarsePrefix_fineAux
          rw [coarsePrefix_initial, coarsePrefix_initial]
        _ ≤ |θ - φ| * (‖ω.2.1.1.1.1 k‖ + ‖ω.2.1.2.1.1 k‖) :=
          angleAux_initial_sub_norm_le p n θ φ ω k
        _ ≤ |θ - φ| * (R + R) :=
          mul_le_mul_of_nonneg_left (add_le_add (h₁ k) (h₂ k)) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, rankCount_add,
        nsmul_eq_mul]
      ring

theorem experimentCap_coarse_path_bounds_eventually (p : Parameters) (hf : FineExponents p)
    (hbf : p.b ≤ p.f) (CB : ℝ) (hCB : 0 < CB) (CD : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (R θ φ : ℝ) (z : Outer n × Internal p n),
      z ∈ experimentCap p n CB CD R →
      (∀ i, ‖(coarseReplayAux p n hbf (angleAux p n θ z.2)).2.2 i -
        (coarseReplayAux p n hbf (angleAux p n φ z.2)).2.2 i‖ ≤
          (2 * n) * |θ - φ|) ∧
      scalarMeshPathGap
        (replayStart (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
          (coarseReplayAux p n hbf (angleAux p n θ z.2)))
        (replayStart (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
          (coarseReplayAux p n hbf (angleAux p n φ z.2))) ≤
            (2 * n * n) * |θ - φ| := by
  filter_upwards [fineAux_cap_path_norms_eventually p hf CB hCB CD] with n hn
  intro R θ φ z hz
  have h₁ := hn R z.2.2.1.1 hz.2.2.2.2.1
  have h₂ := hn R z.2.2.1.2 hz.2.2.2.2.2
  exact ⟨coarse_D_rotation_bound p n hbf n θ φ z.2 h₁.2 h₂.2,
    coarse_start_rotation_bound p n hbf n θ φ z.2 h₁.1 h₂.1⟩

end SKConstants.Completion.N19DS
