module

public import SKConstants.Completion.NL1.Coordinates
public import SKConstants.Completion.T0.SharpIntegral
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator NNReal

namespace SKConstants.Completion.NL1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC5 LGram N13A LM5

variable {Ω : Type} [MeasurableSpace Ω]

theorem paperQueryEnergy_congr_endpoints {Past : Type*}
    (r n : ℕ) (N : ℝ) (target : ℕ → Past → Fin n → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin n ⊕ Unit) → Past)
    (hblind : ∀ j a z w, (∀ i, z (.inl i) = w (.inl i)) → update j a z = update j a w)
    (K : ℕ) (s : PaperState r n K Past) (z w : StoppedNoise (Fin n) K)
    (hz : ∀ j i, paperNoiseTrace n K z j (.inl i) = paperNoiseTrace n K w j (.inl i))
    (x : Fin n → ℝ) :
    paperQueryEnergy r n N target update K s z x =
      paperQueryEnergy r n N target update K s w x := by
  have ht := paperTraces_congr_endpoints r n N target update hblind K s z w hz
  have hf : paperOffColumnTrace r n target update K s z =
      paperOffColumnTrace r n target update K s w := by
    funext j
    unfold paperOffColumnTrace
    rw [ht.2.2.2.2]
    congr 1
    funext i
    simpa only [N13d.paperEndpointTrace_eq_noiseTrace] using hz j i
  unfold paperQueryEnergy
  rw [ht.2.2.2.1, hf]

def replayRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K) :=
  fun i : Fin (r+K) => WithLp.toLp 2 (Fin.append
    (fun j => M1.ReplayTargets W β hβ δ r K u.2 j i)
    (Fin.append (fun j => M1.ReplayEndpoints W β hβ δ r K u.2 j i)
      (fun _ : Fin 1 => scalarHiddenSign (u.1 i))))

def replayQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K) : ℝ :=
  paperQueryEnergy r (r+K) (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
    (M1.ReplayInitial δ r K u.2, 1) (M1.ReplayQueriedNoise W β hβ δ r K u.2) (signSpin u.1)

def replayDiscardedEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K) : ℝ :=
  quadraticEnergy (r+K : ℕ) (signSpin u.1) u.2.1.2.1 - replayQueryEnergy W β hβ δ r K u

def sourceQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) : ℝ :=
  paperQueryEnergy r (r+K) (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
    (M1.Initial δ r K u.2, 1) (M1.Original δ r K u.2) (signSpin u.1)

theorem replayRows_toReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    replayRows W β hβ δ r K (u.1, M1.ToReplay W β hβ δ r K u.2) =
      literalSourceRows W β hβ δ r K u := by
  have ht := M1.completeReplayTraceCoupling_holds W β hβ δ r K hN u.2
  unfold replayRows
  rw [ht.1, ht.2.1]
  funext i
  simp only [literalSourceRows, paperRows, M1.SourceTargets, M1.SourceEndpoints,
    N13d.paperEndpointTrace_eq_noiseTrace]

theorem replayQueryEnergy_toReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    replayQueryEnergy W β hβ δ r K (u.1, M1.ToReplay W β hβ δ r K u.2) =
      sourceQueryEnergy W β hβ δ r K u := by
  have ht := M1.completeReplayTraceCoupling_holds W β hβ δ r K hN u.2
  apply paperQueryEnergy_congr_endpoints r (r+K) (r+K : ℕ) _ _ (growingUpdate_blind δ r K) K
  intro j i
  exact congrFun (congrFun ht.2.1 j) i

theorem replayDiscardedEnergy_toReplay (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (u : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    replayDiscardedEnergy W β hβ δ r K (u.1, M1.ToReplay W β hβ δ r K u.2) =
      growingSourceDiscardedEnergy W β hβ δ r K u := by
  rw [replayDiscardedEnergy, replayQueryEnergy_toReplay W β hβ δ r K hN,
    growingSourceDiscardedEnergy_eq_actual]
  rfl

theorem measurable_replayRows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (replayRows W β hβ δ r K) := by
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [replayRows, Fin.append_left, Function.comp_def] using
      (measurable_pi_apply i).comp ((measurable_pi_apply j).comp
        ((M1.measurable_ReplayTargets W β hβ δ r K).comp measurable_snd))
  · refine Fin.addCases (fun j => ?_) (fun _ => ?_) j
    · simpa only [replayRows, Fin.append_right, Fin.append_left, Function.comp_def] using
        (measurable_pi_apply i).comp ((measurable_pi_apply j).comp
          ((M1.measurable_ReplayEndpoints W β hβ δ r K).comp measurable_snd))
    · simpa only [replayRows, Fin.append_right, Function.comp_def] using
        (measurable_of_finite scalarHiddenSign).comp ((measurable_pi_apply i).comp measurable_fst)

section
attribute [local irreducible] M1.Target M1.Update actualParisiFullScalarDrift
  actualParisiFullMagnetization actualParisiFullSusceptibilitySquareExpected
  actualParisiNegativeRhoStieltjes actualParisiSigmaStieltjes
  paperQueryDirectionTrace paperRemainingProjectionTrace paperEndpointTrace

set_option backward.isDefEq.respectTransparency true in
theorem measurable_replayQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (replayQueryEnergy W β hβ δ r K) := by
  let P := ScalarGrowingPaperPast (M1.Horizon δ K) δ (r+K)
  let target := M1.Target W β hβ δ r K
  let update := M1.Update δ r K
  let arg (u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K) :
      PaperState r (r+K) K P × StoppedNoise (Fin (r+K)) K :=
    ((M1.ReplayInitial δ r K u.2, 1), M1.ReplayQueriedNoise W β hβ δ r K u.2)
  have hi : Measurable (M1.ReplayInitial δ r K) :=
    (measurable_scalarGrowingPaperInitialState _ _ _).comp
      (measurable_snd.prodMk measurable_fst.fst)
  have ha : Measurable arg :=
    ((hi.comp measurable_snd).prodMk measurable_const).prodMk
    ((M1.measurable_ReplayQueriedNoise W β hβ δ r K).comp measurable_snd)
  have hx : Measurable (fun u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K => signSpin u.1) :=
    Measurable.of_eval fun i =>
      (measurable_of_finite scalarHiddenSign).comp ((measurable_pi_apply i).comp measurable_fst)
  change Measurable (fun u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K =>
    paperQueryEnergy r (r+K) (r+K : ℕ) target update K (arg u).1 (arg u).2 (signSpin u.1))
  have hQ : Measurable (fun z : (PaperState r (r+K) K P × StoppedNoise (Fin (r+K)) K) ×
      (Fin (r+K) → ℝ) => paperQueryEnergy r (r+K) (r+K : ℕ) target update K z.1.1 z.1.2 z.2) :=
    measurable_paperQueryEnergy r (r+K) (r+K : ℕ) target update
      (measurable_growingTarget W β hβ δ r K) (measurable_growingUpdate δ r K) K
  simpa only [Function.comp_def] using hQ.comp (ha.prodMk hx)
end

theorem measurable_quadraticEnergy_spin (N : ℝ) (n : ℕ) :
    Measurable (fun u : Spin n × Matrix (Fin n) (Fin n) ℝ => quadraticEnergy N (signSpin u.1) u.2) := by
  apply measurable_from_prod_countable_right
  intro x
  apply Continuous.measurable
  unfold quadraticEnergy Matrix.mulVec dotProduct
  fun_prop

theorem measurable_replayDiscardedEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (replayDiscardedEnergy W β hβ δ r K) := by
  have hq : Measurable (fun u : (Fin (r+K) → Bool) × M1.ReplayInput δ r K =>
      quadraticEnergy (r+K : ℕ) (signSpin u.1) u.2.1.2.1) :=
    (measurable_quadraticEnergy_spin (r+K : ℕ) (r+K)).comp
      (measurable_fst.prodMk measurable_snd.fst.snd.fst)
  exact hq.sub (measurable_replayQueryEnergy W β hβ δ r K)

theorem source_replay_joint_energy_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) :
    (M1.SourceLinkedLaw W β hβ δ r K).map (fun u =>
      (literalSourceRows W β hβ δ r K u, sourceQueryEnergy W β hβ δ r K u,
        growingSourceDiscardedEnergy W β hβ δ r K u)) =
    (M1.ReplayLinkedLaw W β hβ δ r K).map (fun u =>
      (replayRows W β hβ δ r K u, replayQueryEnergy W β hβ δ r K u,
        replayDiscardedEnergy W β hβ δ r K u)) := by
  let F := fun u => (replayRows W β hβ δ r K u,
    replayQueryEnergy W β hβ δ r K u, replayDiscardedEnergy W β hβ δ r K u)
  have hF : Measurable F := (measurable_replayRows W β hβ δ r K).prodMk
    ((measurable_replayQueryEnergy W β hβ δ r K).prodMk
      (measurable_replayDiscardedEnergy W β hβ δ r K))
  have he : (fun u => (literalSourceRows W β hβ δ r K u,
      sourceQueryEnergy W β hβ δ r K u, growingSourceDiscardedEnergy W β hβ δ r K u)) =
      F ∘ (fun u => (u.1, M1.ToReplay W β hβ δ r K u.2)) := by
    funext u
    simp only [F, Function.comp_apply, replayRows_toReplay W β hβ δ r K hN,
      replayQueryEnergy_toReplay W β hβ δ r K hN, replayDiscardedEnergy_toReplay W β hβ δ r K hN]
  have hmap : Measurable (fun u : (Fin (r+K) → Bool) × M1.SourceInput δ r K =>
      (u.1, M1.ToReplay W β hβ δ r K u.2)) :=
    measurable_fst.prodMk ((M1.measurable_ToReplay W β hβ δ r K).comp measurable_snd)
  rw [he, ← Measure.map_map hF hmap,
    M1.growingSource_toReplay_linked_law W β hβ δ r K hN]

end SKConstants.Completion.NL1
