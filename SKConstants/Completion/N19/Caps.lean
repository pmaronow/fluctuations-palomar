module

public import SKConstants.Completion.Blueprint.Experiment
public import SKConstants.ReplayBrownianNormCaps
public import SKConstants.GaussianInputNormCaps
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N19
open Blueprint GaussianProposal BrownianNormCaps SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem measureReal_preimage_of_preserving {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {μ : Measure A} {ν : Measure B}
    {f : A → B} (hf : MeasurePreserving f μ ν) {E : Set B} (hE : MeasurableSet E) :
    μ.real (f ⁻¹' E) = ν.real E := by
  rw [← map_measureReal_apply hf.measurable hE, hf.map_eq]

def replayAuxCap (δ : ℝ≥0) (r q : ℕ) (CB CD R : ℝ) : Set (ReplayAux δ r q) :=
  {a | pathEnergy (r + q) a.1.1 < (growingQueryDuration δ 0 : ℝ) * CB * (r + q : ℕ) ∧
    (∀ j ∈ Finset.range (q + 1), pathEnergy (r + q) (a.1.2 j) <
      4 * (growingQueryDuration δ j : ℝ) * CD * (r + q : ℕ)) ∧
    paperCompletionNormCap (r + q) R q a.2.1 ∧
    pathEnergy (r + q) a.2.2 < (scalarGrowingSourceHorizon δ q : ℝ) * CB * (r + q : ℕ)}

theorem measurableSet_replayAuxCap (δ : ℝ≥0) (r q : ℕ) (CB CD R : ℝ) :
    MeasurableSet (replayAuxCap δ r q CB CD R) := by
  have h0 : MeasurableSet {a : ReplayAux δ r q |
      pathEnergy (r + q) a.1.1 < (growingQueryDuration δ 0 : ℝ) * CB * (r + q : ℕ)} := by
    apply measurableSet_lt _ measurable_const
    unfold pathEnergy
    fun_prop
  have hb : MeasurableSet {a : ReplayAux δ r q |
      ∀ j ∈ Finset.range (q + 1), pathEnergy (r + q) (a.1.2 j) <
        4 * (growingQueryDuration δ j : ℝ) * CD * (r + q : ℕ)} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    apply measurableSet_lt _ measurable_const
    unfold pathEnergy
    fun_prop
  have hc : MeasurableSet {a : ReplayAux δ r q |
      paperCompletionNormCap (r + q) R q a.2.1} :=
    (measurable_snd.fst) (measurableSet_paperCompletionNormCap (r + q) R q)
  have hD : MeasurableSet {a : ReplayAux δ r q |
      pathEnergy (r + q) a.2.2 < (scalarGrowingSourceHorizon δ q : ℝ) * CB * (r + q : ℕ)} := by
    apply measurableSet_lt _ measurable_const
    unfold pathEnergy
    fun_prop
  exact h0.inter (hb.inter (hc.inter hD))

theorem replayAuxCap_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) :
    ∃ CB CD : ℝ, 0 < CB ∧ 0 < CD ∧ ∀ (δ : ℝ≥0), 0 < δ → ∀ (r q : ℕ)
      (R : ℝ), 0 < R →
      (replayAuxLaw W δ r q).real (replayAuxCap δ r q CB CD R)ᶜ ≤
        ((q : ℝ) + 3) * Real.exp (-(r + q : ℕ)) +
          2 * (r + q : ℕ) * q * Real.exp (-R ^ 2 / 2) := by
  obtain ⟨CB, hCB, hB⟩ := primitivePathLaw_uniform_energy_tail W
  obtain ⟨CD, hCD, hBr⟩ := primitiveBridgeStream_energy_tail W
  refine ⟨CB, CD, hCB, hCD, fun δ hδ r q R hR => ?_⟩
  let N := r + q
  let μ0 := Measure.pi (fun _ : Fin N => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))
  let μb := Measure.infinitePi (fun j : ℕ => Measure.pi
    (fun _ : Fin N => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ j)))
  let μc := paperCompletionNoiseLaw N q
  let μd := Measure.pi (fun _ : Fin N => scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q))
  let μ := replayAuxLaw W δ r q
  let A0 : Set (ReplayAux δ r q) :=
    {a | (growingQueryDuration δ 0 : ℝ) * CB * N ≤ pathEnergy N a.1.1}
  let Ab : Set (ReplayAux δ r q) :=
    {a | ∃ j ∈ Finset.range (q + 1),
      4 * (growingQueryDuration δ j : ℝ) * CD * N ≤ pathEnergy N (a.1.2 j)}
  let Ac : Set (ReplayAux δ r q) := {a | ¬paperCompletionNormCap N R q a.2.1}
  let Ad : Set (ReplayAux δ r q) :=
    {a | (scalarGrowingSourceHorizon δ q : ℝ) * CB * N ≤ pathEnergy N a.2.2}
  have hp0 : MeasurePreserving (fun a : ReplayAux δ r q => a.1.1) μ μ0 :=
    measurePreserving_fst.comp measurePreserving_fst
  have hpb : MeasurePreserving (fun a : ReplayAux δ r q => a.1.2) μ μb :=
    measurePreserving_snd.comp measurePreserving_fst
  have hpc : MeasurePreserving (fun a : ReplayAux δ r q => a.2.1) μ μc :=
    measurePreserving_fst.comp measurePreserving_snd
  have hpd : MeasurePreserving (fun a : ReplayAux δ r q => a.2.2) μ μd :=
    measurePreserving_snd.comp measurePreserving_snd
  have h0 : μ.real A0 ≤ Real.exp (-(N : ℝ)) := by
    have hs : MeasurableSet {a : Fin N → ScalarContinuousPath (growingQueryDuration δ 0) |
        (growingQueryDuration δ 0 : ℝ) * CB * N ≤ pathEnergy N a} := by
      apply measurableSet_le measurable_const
      unfold pathEnergy
      fun_prop
    change μ.real ((fun a : ReplayAux δ r q => a.1.1) ⁻¹'
      {a | (growingQueryDuration δ 0 : ℝ) * CB * N ≤ pathEnergy N a}) ≤ _
    rw [measureReal_preimage_of_preserving hp0 hs]
    simpa [μ0] using hB _ (growingQueryDuration_pos δ hδ 0) N 0 (by norm_num)
  have hb : μ.real Ab ≤ (q + 1 : ℕ) * Real.exp (-(N : ℝ)) := by
    have hs : MeasurableSet {f : (j : ℕ) → Fin N → ScalarContinuousPath (growingQueryDuration δ j) |
        ∃ j ∈ Finset.range (q + 1),
          4 * (growingQueryDuration δ j : ℝ) * CD * N ≤ pathEnergy N (f j)} := by
      simp only [ofPred_exists]
      apply MeasurableSet.iUnion
      intro j
      by_cases hj : j ∈ Finset.range (q + 1)
      · simp only [hj, true_and]
        apply measurableSet_le measurable_const
        unfold pathEnergy
        fun_prop
      · simp [hj]
    change μ.real ((fun a : ReplayAux δ r q => a.1.2) ⁻¹'
      {f | ∃ j ∈ Finset.range (q + 1),
        4 * (growingQueryDuration δ j : ℝ) * CD * N ≤ pathEnergy N (f j)}) ≤ _
    rw [measureReal_preimage_of_preserving hpb hs]
    simpa [μb] using hBr (growingQueryDuration δ) N (Finset.range (q + 1))
      (fun j _ => growingQueryDuration_pos δ hδ j) 0 (by norm_num)
  have hc : μ.real Ac ≤ 2 * (N : ℝ) * q * Real.exp (-R ^ 2 / 2) := by
    calc
      μ.real Ac = μc.real {a | ¬paperCompletionNormCap N R q a} :=
        measureReal_preimage_of_preserving hpc (measurableSet_paperCompletionNormCap N R q).compl
      _ ≤ _ := paperCompletionNoiseLaw_norm_tail N q R hR
  have hH : 0 < scalarGrowingSourceHorizon δ q := by
    simpa [scalarGrowingSourceHorizon, growingQueryTime_zero] using
      growingQueryTime_strictMono δ hδ (Nat.zero_lt_succ q)
  have hd : μ.real Ad ≤ Real.exp (-(N : ℝ)) := by
    have hs : MeasurableSet {a : Fin N → ScalarContinuousPath (scalarGrowingSourceHorizon δ q) |
        (scalarGrowingSourceHorizon δ q : ℝ) * CB * N ≤ pathEnergy N a} := by
      apply measurableSet_le measurable_const
      unfold pathEnergy
      fun_prop
    change μ.real ((fun a : ReplayAux δ r q => a.2.2) ⁻¹'
      {a | (scalarGrowingSourceHorizon δ q : ℝ) * CB * N ≤ pathEnergy N a}) ≤ _
    rw [measureReal_preimage_of_preserving hpd hs]
    simpa [μd] using hB _ hH N 0 (by norm_num)
  have he : (replayAuxCap δ r q CB CD R)ᶜ = A0 ∪ (Ab ∪ (Ac ∪ Ad)) := by
    ext a
    change ¬ (_ ∧ _ ∧ _ ∧ _) ↔ _ ∨ (_ ∨ (_ ∨ _))
    simp only [not_and_or, not_forall, not_lt, exists_prop]
    rfl
  rw [he]
  have h := (measureReal_union_le A0 (Ab ∪ (Ac ∪ Ad)) (μ := μ)).trans
    (add_le_add h0 ((measureReal_union_le Ab (Ac ∪ Ad)).trans
      (add_le_add hb ((measureReal_union_le Ac Ad).trans (add_le_add hc hd)))))
  dsimp only [N] at h
  convert h using 1
  push_cast
  ring

end SKConstants.Completion.N19
