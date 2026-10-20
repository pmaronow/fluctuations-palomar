module

public import SKConstants.Completion.N19.Caps
public import SKConstants.Completion.N19.Grid
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N19
open Blueprint GaussianProposal SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def primitiveCap (n : ℕ) (R : ℝ) : Set (Prim n) := {g | ∀ i, |g i| < R}

theorem measurableSet_primitiveCap (n : ℕ) (R : ℝ) : MeasurableSet (primitiveCap n R) := by
  simp only [primitiveCap, ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_lt (by fun_prop) measurable_const)

theorem primitiveCap_failure_le (n : ℕ) (R : ℝ) (hR : 0 < R) :
    (primLaw n).real (primitiveCap n R)ᶜ ≤ 2 * (n : ℝ) ^ 2 * Real.exp (-R ^ 2 / 2) := by
  have he : (primitiveCap n R)ᶜ = {g | ∃ i, R ≤ |g i|} := by
    ext g
    simp only [primitiveCap, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt]
  rw [he]
  simpa [Fintype.card_prod, pow_two] using
    primitiveGaussian_coordinate_max_tail (ι := Fin n × Fin n) R hR

def experimentCap (p : Parameters) (n : ℕ) (CB CD R : ℝ) : Set (Outer n × Internal p n) :=
  (fun z => z.1.1) ⁻¹' primitiveCap n R ∩
  ((fun z => z.1.2) ⁻¹' primitiveCap n R ∩
  ((fun z => z.2.1.1) ⁻¹' primitiveCap n R ∩
  ((fun z => z.2.1.2) ⁻¹' primitiveCap n R ∩
  ((fun z => z.2.2.1.1) ⁻¹'
    replayAuxCap (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) CB CD R ∩
  (fun z => z.2.2.1.2) ⁻¹'
    replayAuxCap (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) CB CD R))))

theorem measurableSet_experimentCap (p : Parameters) (n : ℕ) (CB CD R : ℝ) :
    MeasurableSet (experimentCap p n CB CD R) := by
  have hG := measurableSet_primitiveCap n R
  have hA := measurableSet_replayAuxCap (meshSize p.a n) (rankCount p.a p.f n)
    (queryCount p.a p.f n) CB CD R
  exact (measurable_fst.fst hG).inter ((measurable_fst.snd hG).inter
    ((measurable_snd.fst.fst hG).inter ((measurable_snd.fst.snd hG).inter
      ((measurable_snd.snd.fst.fst hA).inter (measurable_snd.snd.fst.snd hA)))))

theorem failure_inter_le {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] (E F : Set A) :
    μ.real (E ∩ F)ᶜ ≤ μ.real Eᶜ + μ.real Fᶜ := by
  rw [compl_inter]
  exact measureReal_union_le _ _

theorem experimentCap_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) :
    ∃ CB CD : ℝ, 0 < CB ∧ 0 < CD ∧ ∀ (p : Parameters) (n : ℕ), 0 < n →
      ∀ (R : ℝ), 0 < R →
      (experimentLaw W p n).real (experimentCap p n CB CD R)ᶜ ≤
        2 * ((queryCount p.a p.f n : ℝ) + 3) * Real.exp (-(n : ℝ)) +
          (8 * (n : ℝ) ^ 2 + 4 * n * queryCount p.a p.f n) * Real.exp (-R ^ 2 / 2) := by
  obtain ⟨CB, CD, hCB, hCD, hA⟩ := replayAuxCap_failure_le W
  refine ⟨CB, CD, hCB, hCD, fun p n hn R hR => ?_⟩
  let μ := experimentLaw W p n
  let G := primitiveCap n R
  let A := replayAuxCap (meshSize p.a n) (rankCount p.a p.f n) (queryCount p.a p.f n) CB CD R
  let bG := 2 * (n : ℝ) ^ 2 * Real.exp (-R ^ 2 / 2)
  let bA := ((queryCount p.a p.f n : ℝ) + 3) * Real.exp (-(n : ℝ)) +
    2 * n * queryCount p.a p.f n * Real.exp (-R ^ 2 / 2)
  have hG : (primLaw n).real Gᶜ ≤ bG := primitiveCap_failure_le n R hR
  have hAux : (fineAuxLaw W p n).real Aᶜ ≤ bA := by
    have hh := hA (meshSize p.a n) (paperGrowingQueryMeshSize_pos p.a n hn)
      (rankCount p.a p.f n) (queryCount p.a p.f n) R hR
    simpa only [rankCount_add] using hh
  have h0 : μ.real ((fun z : Outer n × Internal p n => z.1.1) ⁻¹' G)ᶜ ≤ bG := by
    have hp : MeasurePreserving (fun z : Outer n × Internal p n => z.1.1) μ (primLaw n) :=
      measurePreserving_fst.comp measurePreserving_fst
    exact (measureReal_preimage_of_preserving hp (measurableSet_primitiveCap n R).compl).trans_le hG
  have h1 : μ.real ((fun z : Outer n × Internal p n => z.1.2) ⁻¹' G)ᶜ ≤ bG := by
    have hp : MeasurePreserving (fun z : Outer n × Internal p n => z.1.2) μ (primLaw n) :=
      measurePreserving_snd.comp measurePreserving_fst
    exact (measureReal_preimage_of_preserving hp (measurableSet_primitiveCap n R).compl).trans_le hG
  have h2 : μ.real ((fun z : Outer n × Internal p n => z.2.1.1) ⁻¹' G)ᶜ ≤ bG := by
    have hp : MeasurePreserving (fun z : Outer n × Internal p n => z.2.1.1) μ (primLaw n) :=
      measurePreserving_fst.comp (measurePreserving_fst.comp measurePreserving_snd)
    exact (measureReal_preimage_of_preserving hp (measurableSet_primitiveCap n R).compl).trans_le hG
  have h3 : μ.real ((fun z : Outer n × Internal p n => z.2.1.2) ⁻¹' G)ᶜ ≤ bG := by
    have hp : MeasurePreserving (fun z : Outer n × Internal p n => z.2.1.2) μ (primLaw n) :=
      measurePreserving_snd.comp (measurePreserving_fst.comp measurePreserving_snd)
    exact (measureReal_preimage_of_preserving hp (measurableSet_primitiveCap n R).compl).trans_le hG
  have h4 : μ.real ((fun z : Outer n × Internal p n => z.2.2.1.1) ⁻¹' A)ᶜ ≤ bA := by
    have hp : MeasurePreserving (fun z : Outer n × Internal p n => z.2.2.1.1) μ (fineAuxLaw W p n) :=
      measurePreserving_fst.comp (measurePreserving_fst.comp (measurePreserving_snd.comp measurePreserving_snd))
    exact (measureReal_preimage_of_preserving hp (measurableSet_replayAuxCap _ _ _ _ _ _).compl).trans_le hAux
  have h5 : μ.real ((fun z : Outer n × Internal p n => z.2.2.1.2) ⁻¹' A)ᶜ ≤ bA := by
    have hp : MeasurePreserving (fun z : Outer n × Internal p n => z.2.2.1.2) μ (fineAuxLaw W p n) :=
      measurePreserving_snd.comp (measurePreserving_fst.comp (measurePreserving_snd.comp measurePreserving_snd))
    exact (measureReal_preimage_of_preserving hp (measurableSet_replayAuxCap _ _ _ _ _ _).compl).trans_le hAux
  have h := (failure_inter_le μ _ _).trans (add_le_add h0
    ((failure_inter_le μ _ _).trans (add_le_add h1
    ((failure_inter_le μ _ _).trans (add_le_add h2
    ((failure_inter_le μ _ _).trans (add_le_add h3
    ((failure_inter_le μ _ _).trans (add_le_add h4 h5)))))))))
  change μ.real (experimentCap p n CB CD R)ᶜ ≤ _ at h
  exact h.trans_eq (by dsimp [bG, bA]; ring)

theorem experimentCap_eventually_exp {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) :
    ∃ CB CD : ℝ, 0 < CB ∧ 0 < CD ∧ ∀ p : Parameters,
      ∀ᶠ n : ℕ in atTop,
        (experimentLaw W p n).real (experimentCap p n CB CD n)ᶜ ≤
          Real.exp (-(n : ℝ) / 2) := by
  obtain ⟨CB, CD, hCB, hCD, hcap⟩ := experimentCap_failure_le W
  refine ⟨CB, CD, hCB, hCD, fun p => ?_⟩
  filter_upwards [quadratic_prefactor_absorption 20 (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with n habs hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hq : (queryCount p.a p.f n : ℝ) ≤ n := by
    exact_mod_cast (show queryCount p.a p.f n ≤ n from Nat.min_le_right _ _)
  have he : Real.exp (-((n : ℝ) ^ 2) / 2) ≤ Real.exp (-(n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hb : 2 * ((queryCount p.a p.f n : ℝ) + 3) * Real.exp (-(n : ℝ)) +
      (8 * (n : ℝ) ^ 2 + 4 * n * queryCount p.a p.f n) * Real.exp (-((n : ℝ) ^ 2) / 2) ≤
        20 * (n : ℝ) ^ 2 * Real.exp (-(n : ℝ)) := by
    have hc : 0 ≤ 8 * (n : ℝ) ^ 2 + 4 * n * queryCount p.a p.f n := by positivity
    have hmul := mul_le_mul_of_nonneg_left he hc
    have hcoeff : 2 * ((queryCount p.a p.f n : ℝ) + 3) +
        (8 * (n : ℝ) ^ 2 + 4 * n * queryCount p.a p.f n) ≤ 20 * (n : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (n : ℝ))]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos (-(n : ℝ))).le]
  exact (hcap p n hn0 n (by positivity)).trans (hb.trans habs)

end SKConstants.Completion.N19
