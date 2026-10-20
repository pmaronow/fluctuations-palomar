module

public import SKConstants.Completion.LGram.ActualSource
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem measurable_paperTargetTrace {Past : Type*} [MeasurableSpace Past] (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) (K : ℕ) (j : Fin K) (i : Fin n) :
    Measurable (fun v : PaperState r n K Past × StoppedNoise (Fin n) K =>
      paperTargetTrace r n target update K v.1 v.2 j i) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (htarget K i).comp measurable_fst.fst
    · let F (s : PaperState r n (K+1) Past) := paperFrame s.2 (target K s.1)
      have hF (a : Fin (r+K+1)) (b : Fin n) : Measurable (fun s => F s a b) :=
        paperFrame_measurable (m:=r+K) (n:=n) (A:=PaperState r n (K+1) Past)
          (fun s => s.2) (fun s => target K s.1)
          (fun _ _ => by fun_prop) (fun b => (htarget K b).comp measurable_fst) a b
      have hs : Measurable (fun v : PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1) =>
          (update K v.1.1 v.2.1, tailRows (F v.1))) := by
        apply Measurable.prodMk
        · exact (hupdate K).comp (measurable_fst.fst.prodMk measurable_snd.fst)
        · exact Measurable.of_eval (fun a => Measurable.of_eval
            (fun b => (hF a.succ b).comp measurable_fst))
      exact (ih j).comp (hs.prodMk measurable_snd.snd)

theorem measurable_paperEndpointTrace (n K : ℕ) (j : Fin K) (i : Fin n ⊕ Unit) :
    Measurable (fun z : StoppedNoise (Fin n) K => paperEndpointTrace n K z j i) := by
  induction K with
  | zero => exact Fin.elim0 j
  | succ K ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp measurable_fst
    · exact (ih j).comp measurable_snd

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_literalSourceRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (literalSourceRows W β hβ δ r K) := by
  let U := (Fin (r+K) → Bool) × M1.SourceInput δ r K
  have hi : Measurable (fun u : U => M1.Initial δ r K u.2) :=
    (measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_snd.fst
  have hz : Measurable (fun u : U => M1.Original δ r K u.2) :=
    (paperAugmentedOriginal_measurable _ _).comp measurable_snd.snd
  have hin : Measurable (fun u : U =>
      (((M1.Initial δ r K u.2,1) : PaperState r (r+K) K
        (ScalarGrowingPaperPast (M1.Horizon δ K) δ (r+K))), M1.Original δ r K u.2)) :=
    (hi.prodMk measurable_const).prodMk hz
  have ht (j : Fin K) (l : Fin (r+K)) : Measurable (fun u : U =>
      paperTargetTrace r (r+K) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
        (M1.Initial δ r K u.2,1) (M1.Original δ r K u.2) j l) :=
    (measurable_paperTargetTrace r (r+K) _ _
      (fun k i => measurable_scalarMeshPaperTarget _ _ _ _ _ _
        (continuous_actualParisiFullMagnetization β).measurable _ _ _ _ _ _ k i)
      (fun k => measurable_scalarMeshPaperUpdate _ _ _ _ _ k) K j l).comp hin
  apply Measurable.of_eval
  intro l
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro a
  refine Fin.addCases (fun j => ?_) (fun a => ?_) a
  · simpa only [Fin.append_left] using ht j l
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) a
    · simpa only [Fin.append_right, Fin.append_left, Function.comp_def] using
        (measurable_paperEndpointTrace (r+K) K j (.inl l)).comp hz
    · have hs : Measurable (fun u : U => scalarHiddenSign (u.1 l)) :=
        (measurable_of_finite scalarHiddenSign).comp ((measurable_pi_apply l).comp measurable_fst)
      simpa only [Fin.append_right] using hs

theorem measurableSet_sourceWholeGramEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (η : ℝ) : MeasurableSet (sourceWholeGramEvent W β hβ δ r K η) :=
  (measurableSet_rowGramEvent _ _ _).preimage (measurable_literalSourceRows W β hβ δ r K)

end SKConstants.Completion.LGram
