module

public import SKConstants.Completion.N19C.Completion

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology
namespace SKConstants.Completion.N19C
open GaussianProposal Blueprint Blueprint4 Blueprint5 N19 N19n
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem completionAt_rotation_norm_le (n q : ℕ) (R : ℝ)
    (a b : PaperCompletionNoise n q)
    (ha : paperCompletionNormCap n R q a) (hb : paperCompletionNormCap n R q b)
    (θ : ℝ) (j : Fin q) :
    ‖N13a.coarsePrefix_completionAt n q
        (completionComb (Real.cos θ) (Real.sin θ) q a b) j‖ ≤
      2 * Real.sqrt n * |R| := by
  rw [completionAt_comb]
  have h₁ := completionAt_norm_le n q R a ha j
  have h₂ := completionAt_norm_le n q R b hb j
  exact (rotation_norm_le _ _ θ).trans (by linarith)

theorem completionAt_rotation_sub_norm_le (n q : ℕ) (R : ℝ)
    (a b : PaperCompletionNoise n q)
    (ha : paperCompletionNormCap n R q a) (hb : paperCompletionNormCap n R q b)
    (θ φ : ℝ) (j : Fin q) :
    ‖N13a.coarsePrefix_completionAt n q
        (completionComb (Real.cos θ) (Real.sin θ) q a b) j -
      N13a.coarsePrefix_completionAt n q
        (completionComb (Real.cos φ) (Real.sin φ) q a b) j‖ ≤
      2 * Real.sqrt n * |R| * |θ - φ| := by
  rw [completionAt_comb, completionAt_comb]
  calc
    _ ≤ |θ - φ| *
        (‖N13a.coarsePrefix_completionAt n q a j‖ +
          ‖N13a.coarsePrefix_completionAt n q b j‖) := rotation_sub_norm_le _ _ _ _
    _ ≤ |θ - φ| * (Real.sqrt n * |R| + Real.sqrt n * |R|) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (completionAt_norm_le n q R a ha j)
          (completionAt_norm_le n q R b hb j)) (abs_nonneg _)
    _ = _ := by ring

theorem coarseCompletion_trace_bounds (p : Parameters) (n : ℕ) (hbf : p.b ≤ p.f)
    (CB CD R θ φ : ℝ) (z : Outer n × Internal p n)
    (hz : z ∈ experimentCap p n CB CD R) :
    (∀ j : Fin (queryCount p.a p.b n),
      ‖completionTrace (rankCount p.a p.b n + queryCount p.a p.b n)
        (queryCount p.a p.b n)
        (coarseReplayAux p n hbf (angleAux p n θ z.2)).2.1 j‖ ≤
          2 * Real.sqrt n * |R|) ∧
    (∀ j : Fin (queryCount p.a p.b n),
      ‖completionTrace (rankCount p.a p.b n + queryCount p.a p.b n)
          (queryCount p.a p.b n)
          (coarseReplayAux p n hbf (angleAux p n θ z.2)).2.1 j -
        completionTrace (rankCount p.a p.b n + queryCount p.a p.b n)
          (queryCount p.a p.b n)
          (coarseReplayAux p n hbf (angleAux p n φ z.2)).2.1 j‖ ≤
            2 * Real.sqrt n * |R| * |θ - φ|) := by
  have ha : paperCompletionNormCap
      (rankCount p.a p.f n + queryCount p.a p.f n) R (queryCount p.a p.f n)
      z.2.2.1.1.2.1 := hz.2.2.2.2.1.2.2.1
  have hb : paperCompletionNormCap
      (rankCount p.a p.f n + queryCount p.a p.f n) R (queryCount p.a p.f n)
      z.2.2.1.2.2.1 := hz.2.2.2.2.2.2.2.1
  constructor
  · intro j
    change ‖completionTrace _ _
      (N13a.coarsePrefix_replayAux _ _ _ _ _ _ _ (angleAux p n θ z.2)).2.1 j‖ ≤ _
    rw [completionTrace_coarseAux_norm]
    have h := completionAt_rotation_norm_le _ _ R _ _ ha hb θ
      (Fin.castLE (queryCount_mono p.a p.b p.f hbf n) j)
    simpa only [rankCount_add, angleAux, combineAux] using h
  · intro j
    change ‖completionTrace _ _
        (N13a.coarsePrefix_replayAux _ _ _ _ _ _ _ (angleAux p n θ z.2)).2.1 j -
      completionTrace _ _
        (N13a.coarsePrefix_replayAux _ _ _ _ _ _ _ (angleAux p n φ z.2)).2.1 j‖ ≤ _
    rw [completionTrace_coarseAux_sub_norm]
    have h := completionAt_rotation_sub_norm_le _ _ R _ _ ha hb θ φ
      (Fin.castLE (queryCount_mono p.a p.b p.f hbf n) j)
    simpa only [rankCount_add, angleAux, combineAux] using h

theorem coarseCompletionBoundsStatement_holds : CoarseCompletionBoundsStatement := by
  intro p _hf hb _hD CB CD _hCB _hCD
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  intro θ φ z hz
  have hnr : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 2 * Real.sqrt n ≤ (n : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 2),
      Real.sq_sqrt (Nat.cast_nonneg n)]
  have hpoly : 2 * Real.sqrt n * |(n : ℝ)| ≤ (n : ℝ) ^ (2 : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg n), Real.rpow_two]
    nlinarith [mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n)]
  obtain ⟨hsize, hdiff⟩ := coarseCompletion_trace_bounds p n hb.2.1.le CB CD n θ φ z hz
  constructor
  · intro j
    exact (hsize j).trans hpoly
  · intro j
    change ‖completionTrace _ _ _ j - completionTrace _ _ _ j‖ ≤ _
    exact (hdiff j).trans (mul_le_mul_of_nonneg_right hpoly (abs_nonneg _))

end SKConstants.Completion.N19C
