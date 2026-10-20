module

public import SKConstants.Completion.N13A.Regularity
public import SKConstants.Completion.LM5.GrowingLinkedEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.N13A
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5

theorem measurable_frameProjection (m n : ℕ) :
    Measurable (frameProjection (m := m) (n := n)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  change Measurable (fun F : Matrix (Fin m) (Fin n) ℝ => ∑ a, F a i * F a j)
  refine Finset.measurable_sum _ (fun a _ => ?_)
  apply Measurable.mul
  · exact (measurable_pi_apply i).comp (measurable_pi_apply a)
  · exact (measurable_pi_apply j).comp (measurable_pi_apply a)

theorem measurable_paperRemainingProjectionTrace {Past : Type*} [MeasurableSpace Past]
    (r n : ℕ) (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (ht : ∀ k i, Measurable (fun a => target k a i))
    (hu : ∀ k, Measurable (Function.uncurry (update k))) (K : ℕ) :
    Measurable (Function.uncurry (paperRemainingProjectionTrace r n target update K)) := by
  induction K with
  | zero =>
    exact Measurable.of_eval (fun _ => (measurable_frameProjection _ n).comp measurable_fst.snd)
  | succ K ih =>
    let F (s : PaperState r n (K+1) Past) := paperFrame s.2 (target K s.1)
    have hF (i : Fin (r+K+1)) (j : Fin n) : Measurable (fun s => F s i j) :=
      paperFrame_measurable (m := r+K) (n := n) (A := PaperState r n (K+1) Past)
        (fun s => s.2) (fun s => target K s.1)
        (fun _ _ => by fun_prop) (fun j => (ht K j).comp measurable_fst) i j
    have hs : Measurable (fun p : PaperState r n (K+1) Past × StoppedNoise (Fin n) (K+1) =>
        (update K p.1.1 p.2.1, tailRows (F p.1))) :=
      ((hu K).comp (measurable_fst.fst.prodMk measurable_snd.fst)).prodMk
        (Measurable.of_eval (fun i => Measurable.of_eval
          (fun j => (hF i.succ j).comp measurable_fst)))
    have hi := ih.comp (hs.prodMk measurable_snd.snd)
    apply Measurable.of_eval
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (measurable_frameProjection _ n).comp measurable_fst.snd
    · exact (measurable_pi_apply j).comp hi

variable {Ω : Type} [MeasurableSpace Ω]

attribute [local irreducible] M1.Target M1.Update actualParisiFullScalarDrift
  actualParisiFullMagnetization actualParisiFullSusceptibilitySquareExpected
  actualParisiNegativeRhoStieltjes actualParisiSigmaStieltjes
  paperQueryDirectionTrace paperRemainingProjectionTrace paperEndpointTrace

theorem measurable_paperQueryEnergy {Past : Type*} [MeasurableSpace Past]
    (r n : ℕ) (N : ℝ) (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (ht : ∀ k i, Measurable (fun a => target k a i))
    (hu : ∀ k, Measurable (Function.uncurry (update k))) (K : ℕ) :
    Measurable (fun z : (PaperState r n K Past × StoppedNoise (Fin n) K) × (Fin n → ℝ) =>
      paperQueryEnergy r n N target update K z.1.1 z.1.2 z.2) := by
  have hdir := LM5.measurable_paperQueryDirectionTrace r n N target update ht hu K
  have hproj := measurable_paperRemainingProjectionTrace r n target update ht hu K
  have hd (j : Fin K) (i : Fin n) :
      Measurable (fun z : (PaperState r n K Past × StoppedNoise (Fin n) K) × (Fin n → ℝ) =>
        paperQueryDirectionTrace r n N target update K z.1.1 z.1.2 j i) :=
    ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hdir)).comp measurable_fst
  have hp (j : Fin (K+1)) (i l : Fin n) :
      Measurable (fun z : (PaperState r n K Past × StoppedNoise (Fin n) K) × (Fin n → ℝ) =>
        paperRemainingProjectionTrace r n target update K z.1.1 z.1.2 j i l) :=
    ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply j).comp hproj))).comp measurable_fst
  have hend (j : Fin K) (i : Fin n) :
      Measurable (fun z : (PaperState r n K Past × StoppedNoise (Fin n) K) × (Fin n → ℝ) =>
        paperEndpointTrace n K z.1.2 j (.inl i)) :=
    (LGram.measurable_paperEndpointTrace n K j (.inl i)).comp measurable_fst.snd
  change Measurable (fun z : (PaperState r n K Past × StoppedNoise (Fin n) K) × (Fin n → ℝ) =>
    ∑ j : Fin K,
      (N⁻¹ * (∑ i, z.2 i * paperQueryDirectionTrace r n N target update K z.1.1 z.1.2 j i)) *
      (N⁻¹ * (∑ i, z.2 i * (∑ l, paperRemainingProjectionTrace r n target update K
        z.1.1 z.1.2 j.succ i l * paperEndpointTrace n K z.1.2 j (.inl l)))))
  refine Finset.measurable_sum _ (fun j _ => ?_)
  apply Measurable.mul
  · apply measurable_const.mul
    exact Finset.measurable_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).mul (hd j i))
  · apply measurable_const.mul
    refine Finset.measurable_sum _ (fun i _ => ?_)
    apply ((measurable_pi_apply i).comp measurable_snd).mul
    exact Finset.measurable_sum _ (fun l _ => (hp j.succ i l).mul (hend j l))

set_option backward.isDefEq.respectTransparency true in
theorem measurable_sharpQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (sharpQueryEnergy W β hβ p n) := by
  let r := coarseRank p n
  let K := coarseCount p n
  let δ := coarseMesh p n
  let P := ScalarGrowingPaperPast (M1.Horizon δ K) δ (r+K)
  let target := M1.Target W β hβ δ r K
  let update := M1.Update δ r K
  have hinitial : Measurable (M1.ReplayInitial δ r K) :=
    (measurable_scalarGrowingPaperInitialState _ _ _).comp
      (measurable_snd.prodMk measurable_fst.fst)
  let arg (y : SharpInput p n) : PaperState r (r+K) K P × StoppedNoise (Fin (r+K)) K :=
    ((M1.ReplayInitial δ r K (sharpReplayInput p n y),1),
      M1.ReplayQueriedNoise W β hβ δ r K (sharpReplayInput p n y))
  have harg : Measurable arg :=
    ((hinitial.comp (measurable_sharpReplayInput p n)).prodMk measurable_const).prodMk
      ((M1.measurable_ReplayQueriedNoise W β hβ δ r K).comp (measurable_sharpReplayInput p n))
  have hx : Measurable (fun y : SharpInput p n => fun i : Fin (r+K) =>
      scalarHiddenSign (y.1 (Fin.cast (rankCount_add p.a p.b n) i))) :=
    Measurable.of_eval (fun i => (measurable_of_finite scalarHiddenSign).comp
      ((measurable_pi_apply (Fin.cast (rankCount_add p.a p.b n) i)).comp
        (show Measurable (Prod.fst : SharpInput p n → Spin n) from measurable_fst)))
  change Measurable (fun y : SharpInput p n => paperQueryEnergy r (r+K) n target update K
    (arg y).1 (arg y).2 (fun i => scalarHiddenSign (y.1 (Fin.cast (rankCount_add p.a p.b n) i))))
  have hQ : Measurable (fun z : (PaperState r (r+K) K P × StoppedNoise (Fin (r+K)) K) ×
      (Fin (r+K) → ℝ) => paperQueryEnergy r (r+K) n target update K z.1.1 z.1.2 z.2) :=
    measurable_paperQueryEnergy r (r+K) n target update
      (LM5.measurable_growingTarget W β hβ δ r K) (LM5.measurable_growingUpdate δ r K) K
  simpa only [Function.comp_def] using hQ.comp (harg.prodMk hx)

theorem measurable_sharpDiscarded (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) : Measurable (sharpDiscarded W β hβ p n) := by
  have hH : Measurable (fun z : Spin n × Prim n =>
      goeSpinHamiltonian (1 / Real.sqrt (2*(n:ℝ))) z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro x
    apply Continuous.measurable
    unfold goeSpinHamiltonian quadraticHamiltonian
    have hM := continuous_goeMatrix (V := Fin n) (1 / Real.sqrt (2*(n:ℝ)))
    fun_prop
  exact ((hH.comp (measurable_fst.prodMk measurable_snd.fst)).div_const n).sub
    (measurable_sharpQueryEnergy W β hβ p n)

end SKConstants.Completion.N13A
