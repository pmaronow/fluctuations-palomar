module

public import SKConstants.Completion.N13a.Restriction

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace SKConstants.N13a
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def coarsePrefix_completionAt (n : ℕ) : (q : ℕ) →
    PaperCompletionNoise n q → Fin q → EuclideanSpace ℝ (Fin n)
  | 0, _, j => Fin.elim0 j
  | q+1, z, j => Fin.cases z.1 (fun i => coarsePrefix_completionAt n q z.2 i) j

theorem coarsePrefix_completion_position (n qf qb : ℕ) (hq : qb ≤ qf)
    (z : PaperCompletionNoise n qf) (j : Fin qb) :
    coarsePrefix_completionAt n qb (coarsePrefix_completion n qf qb hq z) j =
      coarsePrefix_completionAt n qf z (Fin.castLE hq j) := by
  induction qb generalizing qf with
  | zero => exact Fin.elim0 j
  | succ qb ih =>
    cases qf with
    | zero => omega
    | succ qf =>
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · exact ih qf (by omega) z.2 k

theorem coarsePrefix_retained_static (δ : ℝ≥0) (n qb qf : ℕ) (hq : qb ≤ qf)
    (v : PrefixInput δ n qf) :
    (coarsePrefix_input δ n qb qf hq v).1.1 = v.1.1 ∧
      (coarsePrefix_input δ n qb qf hq v).1.2.1 = v.1.2.1 := ⟨rfl,rfl⟩

theorem coarsePrefix_D_position (δ : ℝ≥0) (n qb qf : ℕ) (hq : qb ≤ qf)
    (v : PrefixInput δ n qf) (i : Fin n)
    (t : Icc (0 : ℝ) (scalarGrowingSourceHorizon δ qb : ℝ)) :
    (coarsePrefix_input δ n qb qf hq v).2 i t =
      v.2 i ⟨t,t.property.1,t.property.2.trans
        (M1.growingQueryTime_monotone δ (Nat.add_le_add_right hq 1))⟩ := rfl

end SKConstants.N13a
