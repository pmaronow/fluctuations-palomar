module
public import SKConstants.Completion.LM1a.GrowingCells
public import SKConstants.Completion.LM1a.ResidualNoise

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal
namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem scalarGrowingTerminalPast_static (H δ : ℝ≥0) (n q K : ℕ)
    (s : ScalarGrowingPaperPast H δ n) (z : StoppedNoise (Fin n) K) :
    (proposalTerminalPast (scalarGrowingPaperUpdate H δ n q) K s z).1 = s.1 := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih =>
    exact ih (scalarGrowingPaperUpdate H δ n q K s z.1) z.2

theorem scalarGrowingTerminalPast_prefix (H δ : ℝ≥0) (n q K : ℕ) (hK : K ≤ q)
    (s : ScalarGrowingPaperPast H δ n) (z : StoppedNoise (Fin n) K)
    (i : Fin n) (t : Icc (0 : ℝ) (H : ℝ))
    (ht : (t : ℝ) ≤ growingQueryTime δ (q-K+1)) :
    (proposalTerminalPast (scalarGrowingPaperUpdate H δ n q) K s z).2 i t = s.2 i t := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih =>
    have hj : q-(K+1)+1 = q-K := by omega
    have ht' : (t : ℝ) ≤ growingQueryTime δ (q-K) := by simpa only [hj] using ht
    have ht'' : (t : ℝ) ≤ growingQueryTime δ (q-K+1) :=
      ht'.trans (by exact_mod_cast growingQueryTime_monotone δ (Nat.le_succ _))
    change (proposalTerminalPast _ K (scalarGrowingPaperUpdate H δ n q K s z.1) z.2).2 i t = _
    rw [ih (by omega) _ z.2 ht'']
    exact scalarAppendQueryInterval_prefix H (growingQueryDuration δ (q-K))
      (growingQueryTime δ (q-K)) _ t ht'

theorem scalarGrowingTerminalPast_cell (δ : ℝ≥0) (n q K : ℕ) (hK : K ≤ q)
    (s : ScalarGrowingPaperPast (Horizon δ q) δ n) (z : PaperAugmentedNoise n K)
    (j : Fin (q+1)) (e : Fin K) (hj : j.val = q-K+e.val+1) (i : Fin n) :
    GrowingCell δ q j
        ((proposalTerminalPast (scalarGrowingPaperUpdate (Horizon δ q) δ n q) K s
          (paperAugmentedOriginal n K z)).2 i) =
      scalarQueryBridgeComplete (growingQueryDuration δ j.val)
        (NoiseEndpoints n K z e i,s.1.2.2 j.val i) := by
  induction K generalizing s j with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    revert hj
    refine Fin.cases ?_ (fun a => ?_) e
    · intro hj
      rcases j with ⟨j,hjlt⟩
      have hj' : j = q-K := by simp only [Fin.val_zero, Nat.add_zero] at hj; omega
      subst j
      let s' := scalarGrowingPaperUpdate (Horizon δ q) δ n q K s z.1.1
      have hp (t : Icc (0 : ℝ) (Horizon δ q : ℝ))
          (ht : (t : ℝ) ≤ growingQueryTime δ (q-K+1)) :
          (proposalTerminalPast (scalarGrowingPaperUpdate (Horizon δ q) δ n q) K s'
            (paperAugmentedOriginal n K z.2)).2 i t = s'.2 i t :=
        scalarGrowingTerminalPast_prefix _ _ _ _ _ (by omega) s' _ i t ht
      have haH : (growingQueryTime δ (q-K) : ℝ) + growingQueryDuration δ (q-K) ≤
          (Horizon δ q : ℝ) := by
        have h := growingQueryTime_monotone δ (show q-K+1 ≤ q+1 by omega)
        rw [growingQueryTime_succ] at h
        exact_mod_cast h
      ext u
      change (proposalTerminalPast _ K s' (paperAugmentedOriginal n K z.2)).2 i _ -
        (proposalTerminalPast _ K s' (paperAugmentedOriginal n K z.2)).2 i _ = _
      rw [hp _ (by
        have hu := u.property.2
        change (u : ℝ) ≤ growingQueryDuration δ (q-K) at hu
        change (growingQueryTime δ (q-K) : ℝ) + u ≤ growingQueryTime δ (q-K+1)
        rw [growingQueryTime_succ, NNReal.coe_add]
        linarith), hp _ (by
        change (growingQueryTime δ (q-K) : ℝ) ≤ growingQueryTime δ (q-K+1)
        exact_mod_cast growingQueryTime_monotone δ (Nat.le_succ (q-K)))]
      change scalarAppendQueryInterval (Horizon δ q) (growingQueryDuration δ (q-K))
          (growingQueryTime δ (q-K)) (s.2 i,(z.1.1 (.inl i),s.1.2.2 (q-K) i)) _ -
        scalarAppendQueryInterval (Horizon δ q) (growingQueryDuration δ (q-K))
          (growingQueryTime δ (q-K)) (s.2 i,(z.1.1 (.inl i),s.1.2.2 (q-K) i)) _ = _
      rw [scalarAppendQueryInterval_on_interval _ _ _ (growingQueryTime δ (q-K)).coe_nonneg
        haH _ u]
      have hp0 := scalarAppendQueryInterval_prefix (Horizon δ q)
        (growingQueryDuration δ (q-K)) (growingQueryTime δ (q-K))
        (s.2 i,(z.1.1 (.inl i),s.1.2.2 (q-K) i))
        ⟨growingQueryTime δ (q-K),(growingQueryTime δ (q-K)).coe_nonneg,
          by linarith [(growingQueryDuration δ (q-K)).coe_nonneg]⟩ le_rfl
      rw [hp0]
      simp only [NoiseEndpoints, Fin.cons_zero, WithLp.ofLp_toLp, add_sub_cancel_left]
    · intro hj
      simp only [proposalTerminalPast, paperAugmentedOriginal, NoiseEndpoints, Fin.cons_succ]
      exact ih (by omega)
        (scalarGrowingPaperUpdate (Horizon δ q) δ n q K s z.1.1) z.2 j a (by
          simp only [Fin.val_succ] at hj
          omega)

theorem growingFirstDuration_le_horizon (δ : ℝ≥0) (q : ℕ) :
    growingQueryDuration δ 0 ≤ Horizon δ q := by
  change growingQueryDuration δ 0 ≤ growingQueryTime δ (q+1)
  have h := growingQueryTime_monotone δ (show 1 ≤ q+1 by omega)
  simpa only [growingQueryTime_succ, growingQueryTime_zero, zero_add] using h

theorem sourcePast_cell (δ : ℝ≥0) (r₀ q : ℕ) (s : SourceInput δ r₀ q)
    (e : Fin q) (i : Fin (Size r₀ q)) :
    GrowingCell δ q e.succ ((SourcePast δ r₀ q s).2 i) =
      scalarQueryBridgeComplete (growingQueryDuration δ (e.val+1))
        (NoiseEndpoints (Size r₀ q) q s.2 e i,s.1.2.2 (e.val+1) i) := by
  exact scalarGrowingTerminalPast_cell δ (Size r₀ q) q q le_rfl
    (Initial δ r₀ q s) s.2 e.succ e (by simp) i

theorem sourcePast_initial_restriction (δ : ℝ≥0) (r₀ q : ℕ)
    (s : SourceInput δ r₀ q) (i : Fin (Size r₀ q)) :
    scalarInitialAuxiliaryRestriction (Horizon δ q) (growingQueryDuration δ 0)
      (growingFirstDuration_le_horizon δ q) ((SourcePast δ r₀ q s).2 i) = s.1.2.1 i := by
  ext t
  have hp := scalarGrowingTerminalPast_prefix (Horizon δ q) δ (Size r₀ q) q q le_rfl
    (Initial δ r₀ q s) (Original δ r₀ q s) i
    ⟨t,t.property.1,t.property.2.trans (growingFirstDuration_le_horizon δ q)⟩ (by
      simpa only [Nat.sub_self, zero_add, growingQueryTime_succ,
        growingQueryTime_zero, NNReal.coe_add, NNReal.coe_zero, zero_add] using t.property.2)
  exact hp.trans (scalarInitialAuxiliaryB_on_interval _ _
    (growingFirstDuration_le_horizon δ q) _ t)

end SKConstants.M1
