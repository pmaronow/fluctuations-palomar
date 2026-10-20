module

public import SKConstants.Completion.LM5.ProjectionBudget
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5
variable {Past : Type*} [MeasurableSpace Past]

theorem measurable_paperQueryDirectionTrace (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) (K : ℕ) :
    Measurable (Function.uncurry (paperQueryDirectionTrace r n N target update K)) := by
  induction K with
  | zero => exact measurable_pi_iff.mpr fun j => Fin.elim0 j
  | succ K ih =>
    let F (s : PaperState r n (K+1) Past) := paperFrame s.2 (target K s.1)
    have hF (i : Fin (r+K+1)) (j : Fin n) : Measurable (fun s => F s i j) :=
      paperFrame_measurable (m := r+K) (n := n) (A := PaperState r n (K+1) Past)
        (fun s => s.2) (fun s => target K s.1)
        (fun _ _ => by fun_prop) (fun j => (htarget K j).comp measurable_fst) i j
    have hs : Measurable (fun p : PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1) =>
        (update K p.1.1 p.2.1, tailRows (F p.1))) := by
      apply Measurable.prodMk
      · exact (hupdate K).comp (measurable_fst.fst.prodMk measurable_snd.fst)
      · apply measurable_pi_iff.mpr
        intro i
        apply measurable_pi_iff.mpr
        intro j
        exact (hF i.succ j).comp measurable_fst
    have hi := ih.comp (hs.prodMk measurable_snd.snd)
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · apply measurable_pi_iff.mpr
      intro l
      exact ((hF 0 l).comp measurable_fst).const_mul (Real.sqrt N)
    · exact (measurable_pi_apply j).comp hi

theorem measurable_actualPaper_directions (r K : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    Measurable (fun p : Past × StoppedNoise (Fin (r+K)) K =>
      paperQueryDirectionTrace r (r+K) N target update K (p.1,1) p.2) :=
  (measurable_paperQueryDirectionTrace r (r+K) N target update htarget hupdate K).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

theorem measurable_paperSpinCoefficients (r K : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    Measurable (fun p : (Past × StoppedNoise (Fin (r+K)) K) × (Fin (r+K) → ℝ) =>
      paperSpinCoefficients r K N target update p.1.1 p.1.2 p.2) := by
  have hdir := measurable_actualPaper_directions r K N target update htarget hupdate
  apply measurable_pi_iff.mpr
  intro j
  exact (Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp measurable_snd).mul
      ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp
        (hdir.comp measurable_fst)))).const_mul N⁻¹

theorem measurable_paperResidualSpin (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    Measurable (fun p : (Past × StoppedNoise (Fin (r+K)) K) × (Fin (r+K) → ℝ) =>
      paperResidualSpin r K target update p.1.1 p.1.2 p.2) := by
  have hdir := measurable_actualPaper_directions r K 1 target update htarget hupdate
  have hP : Measurable (fun p : Past × StoppedNoise (Fin (r+K)) K =>
      paperResidualProjection r (r+K) target update K (p.1,1) p.2) := by
    have he (p : Past × StoppedNoise (Fin (r+K)) K) :
        paperResidualProjection r (r+K) target update K (p.1,1) p.2 =
        1 - ∑ j : Fin K, Matrix.vecMulVec
          (paperQueryDirectionTrace r (r+K) 1 target update K (p.1,1) p.2 j)
          (paperQueryDirectionTrace r (r+K) 1 target update K (p.1,1) p.2 j) := by
      unfold paperResidualProjection
      rw [actualPaper_remainingProjection_eq_past_queries r K 1 (by norm_num)]
      simp only [Fin.val_last, Fin.is_lt, ite_true, inv_one, one_smul]
    simp_rw [he]
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro l
    simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
    exact measurable_const.sub (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hdir)).mul
        ((measurable_pi_apply l).comp ((measurable_pi_apply j).comp hdir)))
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun p : (Past × StoppedNoise (Fin (r+K)) K) × (Fin (r+K) → ℝ) =>
    ∑ l, paperResidualProjection r (r+K) target update K (p.1.1,1) p.1.2 i l * p.2 l)
  exact Finset.measurable_sum _ fun l _ =>
    ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp
      (hP.comp measurable_fst))).mul ((measurable_pi_apply l).comp measurable_snd)

theorem measurable_signSpin (n : ℕ) : Measurable (@signSpin n) := by
  exact measurable_of_finite _

end SKConstants.Completion.LM5
