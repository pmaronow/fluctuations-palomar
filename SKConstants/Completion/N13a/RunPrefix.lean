module

public import SKConstants.Completion.N13a.PathRestriction

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.N13a
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def coarsePrefix_rows {a b n : ℕ} (h : a = b) (E : Matrix (Fin a) (Fin n) ℝ) :
    Matrix (Fin b) (Fin n) ℝ := fun i => E (Fin.cast h.symm i)

theorem coarsePrefix_frame {a b n : ℕ} (h : a = b)
    (E : Matrix (Fin (a+1)) (Fin n) ℝ) (v : Fin n → ℝ) :
    tailRows (paperFrame (coarsePrefix_rows (congrArg (fun k => k+1) h) E) v) =
      coarsePrefix_rows h (tailRows (paperFrame E v)) := by
  subst b
  rfl

theorem coarsePrefix_queriedNoise {a b n : ℕ} (h : a = b) (N : ℝ)
    (E : Matrix (Fin (a+1)) (Fin n) ℝ) (v : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (z : EuclideanSpace ℝ (Fin n ⊕ Unit)) :
    paperQueriedNoise N (paperFrame (coarsePrefix_rows (congrArg (fun k => k+1) h) E) v) M z =
      paperQueriedNoise N (paperFrame E v) M z := by
  subst b
  rfl

theorem coarsePrefix_run_after (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H h : ℝ≥0) (hh : h ≤ H) (δ τ : ℕ → ℝ≥0)
    (r n q K : ℕ) (N : ℝ) (s : ScalarMeshPaperPast H δ τ n)
    (E : Matrix (Fin (r+K)) (Fin n) ℝ) (z : StoppedNoise (Fin n) K)
    (M : Matrix (Fin n) (Fin n) ℝ) (hbefore : ∀ k < K, h ≤ τ (q-k)) :
    coarsePrefix_past H h hh δ τ n
      (paperMatrixQueryRun r n N (scalarMeshPaperTarget b f g hf hg m scale H δ τ n q)
        (scalarMeshPaperUpdate H δ τ n q) K (s,E) z M) =
      coarsePrefix_past H h hh δ τ n s := by
  have hs := scalarMeshMatrixQueryRun_static b f g hf hg m scale H δ τ r n q K N (s,E) z M
  apply Prod.ext
  · simp only [coarsePrefix_past, hs]
  · funext i
    apply ContinuousMap.ext
    intro u
    exact scalarMeshMatrixQueryRun_B_prefix_of_before b f g hf hg m scale H δ τ
      r n q K N (s,E) z M h hbefore i
      ⟨u,u.property.1,u.property.2.trans hh⟩ u.property.2

theorem coarsePrefix_run (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (m : ℝ → ℝ → ℝ) (scale : ℕ → ℝ)
    (H h : ℝ≥0) (hh : h ≤ H) (δ τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (r n qb d K : ℕ) (N : ℝ) (hqueries : τ qb ≤ h) (hstop : h ≤ τ (qb+1))
    (s : ScalarMeshPaperPast H δ τ n)
    (E : Matrix (Fin (r+(d+K))) (Fin n) ℝ)
    (z : PaperCompletionNoise n (d+K)) (M : Matrix (Fin n) (Fin n) ℝ) :
    coarsePrefix_past H h hh δ τ n
      (paperMatrixQueryRun r n N
        (scalarMeshPaperTarget b f g hf hg m scale H δ τ n (d+qb))
        (scalarMeshPaperUpdate H δ τ n (d+qb)) (d+K) (s,E)
        (paperCompletionReplayNoise n (d+K) z) M) =
      paperMatrixQueryRun (r+d) n N
        (scalarMeshPaperTarget b f g hf hg m scale h δ τ n qb)
        (scalarMeshPaperUpdate h δ τ n qb) K
        (coarsePrefix_past H h hh δ τ n s,
          coarsePrefix_rows (Nat.add_assoc r d K).symm E)
        (paperCompletionReplayNoise n K
          (coarsePrefix_completion n (d+K) K (by omega) z)) M := by
  induction K generalizing s with
  | zero =>
    apply coarsePrefix_run_after b f g hf hg m scale H h hh δ τ r n (d+qb) d N
    intro k hk
    exact hstop.trans (hτ (by omega))
  | succ K ih =>
    have hk : (d+qb) - (d+K) = qb-K := by omega
    have hk' : (d+qb) - (d+K+1) = qb-(K+1) := by omega
    have ht := coarsePrefix_target b f g hf hg m scale H h hh δ τ n
      (d+qb) (d+K) qb K hk hk'
      ((hτ (Nat.sub_le qb K)).trans hqueries)
      ((hτ (Nat.sub_le qb (K+1))).trans hqueries) s
    let w : EuclideanSpace ℝ (Fin n ⊕ Unit) :=
      WithLp.toLp 2 (Sum.elim z.1.ofLp (fun _ => 0))
    have hn : paperQueriedNoise N
        (paperFrame (coarsePrefix_rows (Nat.add_assoc r d (K+1)).symm E)
          (scalarMeshPaperTarget b f g hf hg m scale h δ τ n qb K
            (coarsePrefix_past H h hh δ τ n s))) M w =
        paperQueriedNoise N (paperFrame E
          (scalarMeshPaperTarget b f g hf hg m scale H δ τ n (d+qb) (d+K) s)) M w := by
      rw [← ht]
      exact coarsePrefix_queriedNoise (Nat.add_assoc r d K).symm N E _ M w
    have hE : tailRows
        (paperFrame (coarsePrefix_rows (Nat.add_assoc r d (K+1)).symm E)
          (scalarMeshPaperTarget b f g hf hg m scale h δ τ n qb K
            (coarsePrefix_past H h hh δ τ n s))) =
        coarsePrefix_rows (Nat.add_assoc r d K).symm
          (tailRows (paperFrame E
            (scalarMeshPaperTarget b f g hf hg m scale H δ τ n (d+qb) (d+K) s))) := by
      rw [← ht]
      exact coarsePrefix_frame (Nat.add_assoc r d K).symm E _
    change coarsePrefix_past H h hh δ τ n
      (paperMatrixQueryRun r n N _ _ (d+K)
        (scalarMeshPaperUpdate H δ τ n (d+qb) (d+K) s
          (paperQueriedNoise N (paperFrame E
            (scalarMeshPaperTarget b f g hf hg m scale H δ τ n (d+qb) (d+K) s)) M w),
          tailRows (paperFrame E
            (scalarMeshPaperTarget b f g hf hg m scale H δ τ n (d+qb) (d+K) s)))
        (paperCompletionReplayNoise n (d+K) z.2) M) =
      paperMatrixQueryRun (r+d) n N _ _ K
        (scalarMeshPaperUpdate h δ τ n qb K (coarsePrefix_past H h hh δ τ n s)
          (paperQueriedNoise N (paperFrame
            (coarsePrefix_rows (Nat.add_assoc r d (K+1)).symm E)
            (scalarMeshPaperTarget b f g hf hg m scale h δ τ n qb K
              (coarsePrefix_past H h hh δ τ n s))) M w), _)
        (paperCompletionReplayNoise n K
          (coarsePrefix_completion n (d+K) K (by omega) z.2)) M
    rw [ih, coarsePrefix_update H h hh δ τ n (d+qb) (d+K) qb K hk, hn, hE]

end SKConstants.N13a
