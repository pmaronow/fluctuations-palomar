module
public import SKConstants.Completion.LM1b.ReplayTrace
public import SKConstants.Completion.LC0.RawReplay

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped NNReal BigOperators
namespace SKConstants.GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Past : Type*} [MeasurableSpace Past]

theorem measurable_paperNoiseTrace (n K : ℕ) (e : Fin K) :
    Measurable (fun z => paperNoiseTrace n K z e) := by
  induction K with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · exact measurable_fst
    · exact (ih e).comp measurable_snd

theorem measurable_paperTargetTrace (r n : ℕ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (ht : ∀ k i, Measurable (fun a => target k a i))
    (hu : ∀ k, Measurable (Function.uncurry (update k)))
    (K : ℕ) (e : Fin K) (i : Fin n) :
    Measurable (fun x : PaperState r n K Past × StoppedNoise (Fin n) K =>
      paperTargetTrace r n target update K x.1 x.2 e i) := by
  induction K with
  | zero => exact Fin.elim0 e
  | succ K ih =>
    refine Fin.cases ?_ (fun e => ?_) e
    · exact (ht K i).comp measurable_fst.fst
    · have hF : Measurable (fun s : PaperState r n (K+1) Past => paperFrame s.2 (target K s.1)) := by
        exact Measurable.of_eval fun j => Measurable.of_eval fun k =>
          paperFrame_measurable (m := r+K) (n := n) (A := PaperState r n (K+1) Past)
            (fun s => s.2) (fun s => target K s.1)
            (fun j k => by fun_prop) (fun k => (ht K k).comp measurable_fst) j k
      have hNext : Measurable (fun x : PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1) =>
          ((update K x.1.1 x.2.1, tailRows (paperFrame x.1.2 (target K x.1.1))), x.2.2)) := by
        apply Measurable.prodMk
        · exact ((hu K).comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
            (Measurable.of_eval fun j => (measurable_pi_apply j.succ).comp (hF.comp measurable_fst))
        · exact measurable_snd.snd
      exact (ih e).comp hNext

theorem measurable_paperMatrixQueryNoiseRun (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (ht : ∀ k i, Measurable (fun a => target k a i))
    (hu : ∀ k, Measurable (Function.uncurry (update k))) (K : ℕ) :
    Measurable (fun x : (PaperState r n K Past × StoppedNoise (Fin n) K) ×
        Matrix (Fin n) (Fin n) ℝ => paperMatrixQueryNoiseRun r n N target update K x.1.1 x.1.2 x.2) := by
  induction K with
  | zero => exact measurable_fst.snd
  | succ K ih =>
    let F (s : PaperState r n (K+1) Past) : Matrix (Fin (r+K+1)) (Fin n) ℝ :=
      paperFrame s.2 (target K s.1)
    have hF : Measurable F := by
      exact Measurable.of_eval fun j => Measurable.of_eval fun k =>
        paperFrame_measurable (m := r+K) (n := n) (A := PaperState r n (K+1) Past)
          (fun s => s.2) (fun s => target K s.1)
          (fun j k => by fun_prop) (fun k => (ht K k).comp measurable_fst) j k
    let E (x : (PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1)) × Matrix (Fin n) (Fin n) ℝ) :
        EuclideanSpace ℝ (Fin n ⊕ Unit) :=
      paperQueriedNoise (m := r+K) N (F x.1.1) x.2 x.1.2.1
    have hArg : Measurable (fun x : (PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1)) ×
        Matrix (Fin n) (Fin n) ℝ => ((F x.1.1, x.2), x.1.2.1)) :=
      (((hF.comp measurable_fst.fst).prodMk measurable_snd).prodMk measurable_fst.snd.fst)
    have hE0 := (measurable_paperQueriedNoise (r+K) n N).comp hArg
    have hE : Measurable E := hE0
    have hU : Measurable (fun x : (PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1)) ×
        Matrix (Fin n) (Fin n) ℝ => update K x.1.1.1 (E x)) :=
      (hu K).comp (measurable_fst.fst.fst.prodMk hE)
    have hRows : Measurable (fun x : (PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1)) ×
        Matrix (Fin n) (Fin n) ℝ => tailRows (F x.1.1)) :=
      Measurable.of_eval fun j => (measurable_pi_apply j.succ).comp (hF.comp measurable_fst.fst)
    have hNext : Measurable (fun x : (PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1)) ×
        Matrix (Fin n) (Fin n) ℝ =>
        (((update K x.1.1.1 (E x), tailRows (F x.1.1)), x.1.2.2), x.2)) := by
      exact ((hU.prodMk hRows).prodMk measurable_fst.snd.snd).prodMk measurable_snd
    exact hE.prodMk (ih.comp hNext)

theorem measurable_paperMatrixQueryTargetTrace (r n : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (ht : ∀ k i, Measurable (fun a => target k a i))
    (hu : ∀ k, Measurable (Function.uncurry (update k))) (K : ℕ) (e : Fin K) (i : Fin n) :
    Measurable (fun x : (PaperState r n K Past × StoppedNoise (Fin n) K) ×
        Matrix (Fin n) (Fin n) ℝ => paperMatrixQueryTargetTrace r n N target update K x.1.1 x.1.2 x.2 e i) := by
  simp_rw [paperMatrixQueryTargetTrace_eq]
  exact (measurable_paperTargetTrace r n target update ht hu K e i).comp
    (measurable_fst.fst.prodMk (measurable_paperMatrixQueryNoiseRun r n N target update ht hu K))

end SKConstants.GaussianProposal

namespace SKConstants.M1
open GaussianProposal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_SourceTargets (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (SourceTargets W β hβ δ r₀ q) := by
  apply Measurable.of_eval
  intro e
  apply Measurable.of_eval
  intro i
  exact (measurable_paperTargetTrace r₀ (Size r₀ q) (Target W β hβ δ r₀ q) (Update δ r₀ q)
    (fun k i => measurable_scalarMeshPaperTarget _ _ _ _ _ _ (continuous_actualParisiFullMagnetization β).measurable _ _ _ _ _ _ k i)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ _ _ k) q e i).comp
    ((((measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_fst).prodMk measurable_const).prodMk
      ((paperAugmentedOriginal_measurable _ _).comp measurable_snd))

theorem measurable_SourceEndpoints (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (SourceEndpoints δ r₀ q) := by
  apply Measurable.of_eval
  intro e
  apply Measurable.of_eval
  intro i
  exact (EuclideanSpace.proj (.inl i)).continuous.measurable.comp
    ((measurable_paperNoiseTrace (Size r₀ q) q e).comp
      ((paperAugmentedOriginal_measurable _ _).comp measurable_snd))

theorem measurable_ReplayQueriedNoise (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (ReplayQueriedNoise W β hβ δ r₀ q) := by
  have hI : Measurable (ReplayInitial δ r₀ q) := (measurable_scalarGrowingPaperInitialState (Horizon δ q) δ (Size r₀ q)).comp
    (measurable_snd.prodMk measurable_fst.fst)
  have hZ : Measurable (ReplayNoise δ r₀ q) := (paperCompletionReplayNoise_measurable (Size r₀ q) q).comp measurable_fst.snd.snd
  exact (measurable_paperMatrixQueryNoiseRun r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ))
    (Target W β hβ δ r₀ q) (Update δ r₀ q)
    (fun k i => measurable_scalarMeshPaperTarget _ _ _ _ _ _ (continuous_actualParisiFullMagnetization β).measurable _ _ _ _ _ _ k i)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ _ _ k) q).comp
    (((hI.prodMk measurable_const).prodMk hZ).prodMk measurable_fst.snd.fst)

theorem measurable_ReplayTargets (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (ReplayTargets W β hβ δ r₀ q) := by
  apply Measurable.of_eval
  intro e
  apply Measurable.of_eval
  intro i
  have hI : Measurable (ReplayInitial δ r₀ q) := (measurable_scalarGrowingPaperInitialState (Horizon δ q) δ (Size r₀ q)).comp
    (measurable_snd.prodMk measurable_fst.fst)
  have hZ : Measurable (ReplayNoise δ r₀ q) := (paperCompletionReplayNoise_measurable (Size r₀ q) q).comp measurable_fst.snd.snd
  exact (measurable_paperMatrixQueryTargetTrace r₀ (Size r₀ q) ((r₀ : ℝ)+(q : ℝ))
    (Target W β hβ δ r₀ q) (Update δ r₀ q)
    (fun k i => measurable_scalarMeshPaperTarget _ _ _ _ _ _ (continuous_actualParisiFullMagnetization β).measurable _ _ _ _ _ _ k i)
    (fun k => measurable_scalarMeshPaperUpdate _ _ _ _ _ k) q e i).comp
    (((hI.prodMk measurable_const).prodMk hZ).prodMk measurable_fst.snd.fst)

theorem measurable_ReplayEndpoints (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (ReplayEndpoints W β hβ δ r₀ q) := by
  apply Measurable.of_eval
  intro e
  apply Measurable.of_eval
  intro i
  exact (EuclideanSpace.proj (.inl i)).continuous.measurable.comp
    ((measurable_paperNoiseTrace (Size r₀ q) q e).comp (measurable_ReplayQueriedNoise W β hβ δ r₀ q))

theorem growingSource_linked_trace_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    (SourceLinkedLaw W β hβ δ r₀ q).map
      (fun u => (u.1, SourceTargets W β hβ δ r₀ q u.2, SourceEndpoints δ r₀ q u.2)) =
    (ReplayLinkedLaw W β hβ δ r₀ q).map
      (fun u => (u.1, ReplayTargets W β hβ δ r₀ q u.2, ReplayEndpoints W β hβ δ r₀ q u.2)) := by
  have hObs : Measurable (fun u : (Fin (Size r₀ q) → Bool) × ReplayInput δ r₀ q =>
      (u.1, ReplayTargets W β hβ δ r₀ q u.2, ReplayEndpoints W β hβ δ r₀ q u.2)) :=
    measurable_fst.prodMk
      (((measurable_ReplayTargets W β hβ δ r₀ q).comp measurable_snd).prodMk
        ((measurable_ReplayEndpoints W β hβ δ r₀ q).comp measurable_snd))
  have hRun : Measurable (fun u : (Fin (Size r₀ q) → Bool) × SourceInput δ r₀ q =>
      (u.1, ToReplay W β hβ δ r₀ q u.2)) :=
    measurable_fst.prodMk ((measurable_ToReplay W β hβ δ r₀ q).comp measurable_snd)
  rw [← growingSource_toReplay_linked_law W β hβ δ r₀ q hN, Measure.map_map hObs hRun]
  congr 1
  funext u
  have h := completeReplayTraceCoupling_holds W β hβ δ r₀ q hN u.2
  exact Prod.ext rfl (Prod.ext h.1.symm h.2.1.symm)

theorem rawLinked_trace_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    (RawLinkedLaw W β hβ δ r₀ q).map (fun u =>
      ((RawToReplay W δ r₀ q u).1,
        ReplayTargets W β hβ δ r₀ q (RawToReplay W δ r₀ q u).2,
        ReplayEndpoints W β hβ δ r₀ q (RawToReplay W δ r₀ q u).2)) =
    (ReplayLinkedLaw W β hβ δ r₀ q).map
      (fun u => (u.1, ReplayTargets W β hβ δ r₀ q u.2, ReplayEndpoints W β hβ δ r₀ q u.2)) := by
  have hObs : Measurable (fun u : (Fin (Size r₀ q) → Bool) × ReplayInput δ r₀ q =>
      (u.1, ReplayTargets W β hβ δ r₀ q u.2, ReplayEndpoints W β hβ δ r₀ q u.2)) :=
    measurable_fst.prodMk
      (((measurable_ReplayTargets W β hβ δ r₀ q).comp measurable_snd).prodMk
        ((measurable_ReplayEndpoints W β hβ δ r₀ q).comp measurable_snd))
  have he := congrArg (fun ν => ν.map (fun u =>
    (u.1, ReplayTargets W β hβ δ r₀ q u.2, ReplayEndpoints W β hβ δ r₀ q u.2)))
    (rawLinked_toReplay_law W β hβ δ r₀ q)
  rw [Measure.map_map hObs (measurable_RawToReplay W δ r₀ q)] at he
  exact he

theorem growingSource_rawLinked_trace_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) (hN : 0 < Size r₀ q) :
    (SourceLinkedLaw W β hβ δ r₀ q).map
      (fun u => (u.1, SourceTargets W β hβ δ r₀ q u.2, SourceEndpoints δ r₀ q u.2)) =
    (RawLinkedLaw W β hβ δ r₀ q).map (fun u =>
      ((RawToReplay W δ r₀ q u).1,
        ReplayTargets W β hβ δ r₀ q (RawToReplay W δ r₀ q u).2,
        ReplayEndpoints W β hβ δ r₀ q (RawToReplay W δ r₀ q u).2)) :=
  (growingSource_linked_trace_law W β hβ δ r₀ q hN).trans
    (rawLinked_trace_law W β hβ δ r₀ q).symm

end SKConstants.M1
