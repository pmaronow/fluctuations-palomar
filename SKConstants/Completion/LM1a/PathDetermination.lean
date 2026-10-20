module
public import SKConstants.Completion.LM1a.LiteralPathRecovery

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SKConstants.M1
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem GrowingCell_eval_at (δ : ℝ≥0) (q : ℕ) (j : Fin (q+1))
    (b : ScalarContinuousPath (Horizon δ q))
    (u : Icc (0 : ℝ) (growingQueryDuration δ j.val : ℝ))
    (t : Icc (0 : ℝ) (Horizon δ q : ℝ))
    (ht : (growingQueryTime δ j.val : ℝ) + u = t) :
    GrowingCell δ q j b u = b t - b
      ⟨growingQueryTime δ j.val,(growingQueryTime δ j.val).coe_nonneg,
        by exact_mod_cast growingQueryTime_monotone δ (Nat.le_of_lt j.isLt)⟩ := by
  change b _ - b _ = _
  congr 1
  exact congrArg b (Subtype.ext ht)

theorem growingPath_eq_of_restriction_cells (δ : ℝ≥0) (q : ℕ)
    (b c : ScalarContinuousPath (Horizon δ q))
    (hfirst : scalarInitialAuxiliaryRestriction (Horizon δ q) (growingQueryDuration δ 0)
        (growingFirstDuration_le_horizon δ q) b =
      scalarInitialAuxiliaryRestriction (Horizon δ q) (growingQueryDuration δ 0)
        (growingFirstDuration_le_horizon δ q) c)
    (hcells : ∀ e : Fin q, GrowingCell δ q e.succ b = GrowingCell δ q e.succ c) : b = c := by
  have hp (k : ℕ) (hk : k ≤ q) : ∀ t : Icc (0 : ℝ) (Horizon δ q : ℝ),
      (t : ℝ) ≤ growingQueryTime δ (k+1) → b t = c t := by
    induction k with
    | zero =>
      intro t ht
      have ht0 : (t : ℝ) ≤ growingQueryDuration δ 0 := by
        simpa only [growingQueryTime_succ, growingQueryTime_zero,
          NNReal.coe_add, NNReal.coe_zero, zero_add] using ht
      exact congrArg (fun p : ScalarContinuousPath (growingQueryDuration δ 0) =>
        p ⟨t,t.property.1,ht0⟩) hfirst
    | succ k ih =>
      intro t ht
      by_cases hta : (t : ℝ) ≤ growingQueryTime δ (k+1)
      · exact ih (by omega) t hta
      · let e : Fin q := ⟨k,by omega⟩
        have haH : growingQueryTime δ (k+1) ≤ Horizon δ q :=
          growingQueryTime_monotone δ (by omega)
        let a : Icc (0 : ℝ) (Horizon δ q : ℝ) :=
          ⟨growingQueryTime δ (k+1),(growingQueryTime δ (k+1)).coe_nonneg,haH⟩
        let u : Icc (0 : ℝ) (growingQueryDuration δ (k+1) : ℝ) :=
          ⟨(t : ℝ)-growingQueryTime δ (k+1),by
            constructor
            · exact sub_nonneg.mpr (le_of_not_ge hta)
            · have ht' := ht
              rw [growingQueryTime_succ, NNReal.coe_add] at ht'
              linarith⟩
        have he : (growingQueryTime δ e.succ.val : ℝ)+u = t := by dsimp [e,u]; ring
        have h := congrArg (fun p : ScalarContinuousPath (growingQueryDuration δ e.succ.val) => p u)
          (hcells e)
        rw [GrowingCell_eval_at δ q e.succ b u t he,
          GrowingCell_eval_at δ q e.succ c u t he] at h
        have ha := ih (by omega) a le_rfl
        change b t - b a = c t - c a at h
        linarith
  ext t
  exact hp q le_rfl t t.property.2

end SKConstants.M1
