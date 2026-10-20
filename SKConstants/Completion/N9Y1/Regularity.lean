module

public import SKConstants.Completion.Blueprint5.FineStatements
public import SKConstants.Completion.N13A.EnergyMeasurable
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.N9Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine N9 M1 LM5 Blueprint5
variable {Ω : Type*} [MeasurableSpace Ω]

theorem complement_projection_dot_self_le {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hsym : P.IsSymm) (hid : P*P=P)
    (x : Fin n → ℝ) :
    dot ((1-P)*ᵥx) ((1-P)*ᵥx) ≤ dot x x := by
  have hU : (1-P)*(1-P)=1-P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hid]
    abel
  have hc := symmetric_idempotent_apply_norm_le
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (1-P)) (by
      change (1-P).toEuclideanLin.IsSymmetric
      apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
      change (1-P)ᴴ=1-P
      rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_sub, Matrix.transpose_one, hsym]) (by
      intro y
      have hm := congrArg (fun A => Matrix.toEuclideanCLM (𝕜 := ℝ) A y) hU
      simpa only [map_mul, ContinuousLinearMap.mul_apply] using hm)
    (WithLp.toLp 2 x)
  have he : ‖WithLp.toLp 2 ((1-P)*ᵥx)‖ ≤ ‖WithLp.toLp 2 x‖ := by
    simpa only [Matrix.toEuclideanCLM_toLp] using hc
  nlinarith [euclidean_norm_sq_dot ((1-P)*ᵥx), euclidean_norm_sq_dot x,
    norm_nonneg (WithLp.toLp 2 ((1-P)*ᵥx)), norm_nonneg (WithLp.toLp 2 x)]

theorem measurable_fineCellRemainingProjection (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K) :
    Measurable (fineCellRemainingProjection W β hβ δ r K e) := by
  have hi : Measurable (fun z : (Fin (r+K) → Bool) × SourceInput δ r K =>
      ((M1.Initial δ r K z.2,(1 : Matrix (Fin (r+K)) (Fin (r+K)) ℝ)),M1.Original δ r K z.2)) :=
    (((measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_snd.fst).prodMk
      measurable_const).prodMk ((paperAugmentedOriginal_measurable _ _).comp measurable_snd.snd)
  have hm := (N13A.measurable_paperRemainingProjectionTrace r (r+K)
      (M1.Target W β hβ δ r K) (M1.Update δ r K)
      (measurable_growingTarget W β hβ δ r K) (measurable_growingUpdate δ r K) K).comp hi
  have he := (measurable_pi_apply e.castSucc).comp hm
  exact he

theorem fineCellRemainingProjection_symm (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    (fineCellRemainingProjection W β hβ δ r K e z).IsSymm :=
  paperRemainingProjectionTrace_symm r (r+K) _ _ K _ _ _

theorem fineCellRemainingProjection_idempotent (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    fineCellRemainingProjection W β hβ δ r K e z *
      fineCellRemainingProjection W β hβ δ r K e z =
        fineCellRemainingProjection W β hβ δ r K e z := by
  apply paperRemainingProjectionTrace_idempotent
  intro i j
  simp [dot, Matrix.one_apply]

theorem measurable_fineCellRemovedSquare (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K) :
    Measurable (fineCellRemovedSquare W β hβ δ r K e) := by
  have hp := measurable_fineCellRemainingProjection W β hβ δ r K e
  have ht : Measurable (fun z : (Fin (r+K) → Bool) × SourceInput δ r K =>
      SourceTargets W β hβ δ r K z.2 e) :=
    ((measurable_pi_apply e).comp (measurable_SourceTargets W β hβ δ r K)).comp measurable_snd
  unfold fineCellRemovedSquare dot Matrix.mulVec dotProduct
  fun_prop

theorem fineCellRemovedSquare_nonneg (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    0 ≤ fineCellRemovedSquare W β hβ δ r K e z :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (dot_self_nonneg _)

theorem fineCellRemovedSquare_le_total (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
    fineCellRemovedSquare W β hβ δ r K e z ≤
      queryTotalSquare (r+K : ℕ) (SourceTargets W β hβ δ r K z.2 e) :=
  mul_le_mul_of_nonneg_left
    (complement_projection_dot_self_le _
      (fineCellRemainingProjection_symm W β hβ δ r K e z)
      (fineCellRemainingProjection_idempotent W β hβ δ r K e z) _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem fineCellRemovedSquare_memLp_two (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (e : Fin K) :
    MemLp (fineCellRemovedSquare W β hβ δ r K e) 2 (SourceLinkedLaw W β hβ δ r K) := by
  let μ := SourceLinkedLaw W β hβ δ r K
  let T := fun z : (Fin (r+K) → Bool) × SourceInput δ r K => SourceTargets W β hβ δ r K z.2 e
  have hQ : MemLp (fun z => queryTotalSquare (r+K : ℕ) (T z)) 2 μ := by
    convert (memLp_finsetSum Finset.univ (fun i _ =>
      memLp_square_of_four μ (fun z => T z i)
        (N9b.sourceTarget_memLp W β hβ δ hδ r K hn e i 4))).const_mul
          (((r+K : ℕ) : ℝ)⁻¹) using 1
    ext z
    simp only [queryTotalSquare,dot,pow_two]
  apply hQ.mono (measurable_fineCellRemovedSquare W β hβ δ r K e).aestronglyMeasurable
  apply ae_of_all
  intro z
  have hy := fineCellRemovedSquare_nonneg W β hβ δ r K e z
  have hle := fineCellRemovedSquare_le_total W β hβ δ r K e z
  simpa only [T,Real.norm_eq_abs,abs_of_nonneg hy,abs_of_nonneg (hy.trans hle)] using hle

theorem fineCellRemovedSquare_integrable (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (e : Fin K) :
    Integrable (fineCellRemovedSquare W β hβ δ r K e) (SourceLinkedLaw W β hβ δ r K) :=
  (fineCellRemovedSquare_memLp_two W β hβ δ hδ r K hn e).integrable (by norm_num)

theorem fineCellRemovedSquare_sq_integrable (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (e : Fin K) :
    Integrable (fun z => fineCellRemovedSquare W β hβ δ r K e z^2)
      (SourceLinkedLaw W β hβ δ r K) :=
  (fineCellRemovedSquare_memLp_two W β hβ δ hδ r K hn e).integrable_sq

end SKConstants.Completion.N9Y1
