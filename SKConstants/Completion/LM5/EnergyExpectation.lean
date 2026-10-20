module

public import SKConstants.Completion.LM5.GrowingCompletionLaw
public import SKConstants.Completion.LF0.EnergyMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SKConstantsOAI.ZeroTemperatureSK
open scoped BigOperators Matrix NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5
variable {Ω : Type*} [MeasurableSpace Ω]

def growingSourceMatrix (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (s : M1.SourceInput δ r K) :=
  (actualParisiGrowingSourceAugmentedOutput W β hβ δ r K s.1 s.2).1

theorem measurable_growingSourceMatrix (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (growingSourceMatrix W β hβ δ r K) :=
  ((measurable_scalarGrowingSourceAugmentedOutput _ _ _ _ _ _
    (continuous_actualParisiFullMagnetization β).measurable _ δ r K).fst)

theorem growingSourceMatrix_unlinked_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    (M1.SourceLaw W δ r K).map (growingSourceMatrix W β hβ δ r K) = skDisorderLaw (r+K) := by
  have h := scalarGrowingSourceAugmentedOutput_joint_law W
    (actualParisiFullScalarDrift β) (actualParisiNegativeRhoStieltjes W β hβ)
    (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (actualParisiFullMagnetization β)
    (continuous_actualParisiFullMagnetization β).measurable
    (actualParisiFullSusceptibilitySquareExpected W β) δ r K
  have hmap := congrArg (fun ν => ν.map (Prod.fst ∘ Prod.snd)) h
  have hOut : Measurable (fun s : M1.SourceInput δ r K =>
      actualParisiGrowingSourceAugmentedOutput W β hβ δ r K s.1 s.2) :=
    measurable_scalarGrowingSourceAugmentedOutput _ _ _ _ _ _
      (continuous_actualParisiFullMagnetization β).measurable _ δ r K
  change ((M1.SourceLaw W δ r K).map (fun s : M1.SourceInput δ r K =>
    (s.1, actualParisiGrowingSourceAugmentedOutput W β hβ δ r K s.1 s.2))).map
      (Prod.fst ∘ Prod.snd) =
    ((scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)).prod
      ((skDisorderLaw (r+K)).prod (paperCompletionNoiseLaw (r+K) K))).map
        (Prod.fst ∘ Prod.snd) at hmap
  rw [Measure.map_map (measurable_fst.comp measurable_snd)
    (measurable_fst.prodMk hOut),
    ← Measure.map_map measurable_fst measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul,
    Measure.map_fst_prod, measure_univ, one_smul] at hmap
  exact hmap

theorem growingSourceMatrix_linked_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    (M1.SourceLinkedLaw W β hβ δ r K).map
      (fun z => growingSourceMatrix W β hβ δ r K z.2) = skDisorderLaw (r+K) := by
  change (M1.SourceLinkedLaw W β hβ δ r K).map
    (growingSourceMatrix W β hβ δ r K ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_growingSourceMatrix W β hβ δ r K) measurable_snd,
    M1.sourceLinkedLaw_base_marginal, growingSourceMatrix_unlinked_law]

def growingSourceEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) : ℝ :=
  quadraticEnergy (r+K : ℕ) (signSpin z.1) (growingSourceMatrix W β hβ δ r K z.2)

def growingSourceQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) : ℝ :=
  paperQueryEnergy r (r+K) (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
    (growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) (signSpin z.1)

theorem growingSourceDiscardedEnergy_eq_sub (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    growingSourceDiscardedEnergy W β hβ δ r K =
      fun z => growingSourceEnergy W β hβ δ r K z - growingSourceQueryEnergy W β hβ δ r K z :=
  funext (growingSourceDiscardedEnergy_eq_actual W β hβ δ r K)

theorem quadraticEnergy_signSpin_eq {n : ℕ} (N : ℝ) (x : Fin n → Bool)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    quadraticEnergy N (signSpin x) W = N⁻¹ * quadraticHamiltonian W x := by
  unfold quadraticEnergy quadraticHamiltonian
  rw [Matrix.dot_mulVec_eq_sum_sum]
  rw [Finset.sum_comm]
  simp only [signSpin, scalarHiddenSign, signedSpin]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem growingSourceEnergy_memLp_two (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    MemLp (growingSourceEnergy W β hβ δ r K) 2 (M1.SourceLinkedLaw W β hβ δ r K) := by
  have h := LF0.gaussian_marginal_energy_memLp (M1.SourceLinkedLaw W β hβ δ r K)
    (fun z => growingSourceMatrix W β hβ δ r K z.2) (fun z => z.1)
    ((measurable_growingSourceMatrix W β hβ δ r K).comp measurable_snd) measurable_fst
    (growingSourceMatrix_linked_law W β hβ δ r K)
  have he : growingSourceEnergy W β hβ δ r K = fun z =>
      ((r+K : ℕ) : ℝ)⁻¹ * quadraticHamiltonian (growingSourceMatrix W β hβ δ r K z.2) z.1 :=
    funext fun z => quadraticEnergy_signSpin_eq _ _ _
  rw [he]
  exact h.const_mul _

theorem growingSourceQueryEnergy_memLp_two (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) :
    MemLp (growingSourceQueryEnergy W β hβ δ r K) 2 (M1.SourceLinkedLaw W β hβ δ r K) := by
  have h := (growingSourceEnergy_memLp_two W β hβ δ r K).sub
    (growingSourceDiscardedEnergy_memLp_two W β hβ δ r K hN)
  have he : growingSourceQueryEnergy W β hβ δ r K =
      (growingSourceEnergy W β hβ δ r K - growingSourceDiscardedEnergy W β hβ δ r K) := by
    funext z
    rw [growingSourceDiscardedEnergy_eq_sub]
    simp only [Pi.sub_apply]
    ring
  rw [he]
  exact h

theorem growingSource_energy_integral_eq_query (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) :
    (∫ z, growingSourceEnergy W β hβ δ r K z ∂M1.SourceLinkedLaw W β hβ δ r K) =
      ∫ z, growingSourceQueryEnergy W β hβ δ r K z ∂M1.SourceLinkedLaw W β hβ δ r K := by
  have h := growingSourceDiscardedEnergy_mean W β hβ δ r K hN
  rw [growingSourceDiscardedEnergy_eq_sub,
    integral_sub ((growingSourceEnergy_memLp_two W β hβ δ r K).integrable (by norm_num))
      ((growingSourceQueryEnergy_memLp_two W β hβ δ r K hN).integrable (by norm_num))] at h
  exact sub_eq_zero.mp h

end SKConstants.Completion.LM5
