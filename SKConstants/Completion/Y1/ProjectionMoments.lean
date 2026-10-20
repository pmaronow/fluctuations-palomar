module

public import SKConstants.Completion.Y1.ConditionalMoments
public import SKConstants.Completion.Y1.RemovedFrame
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine LQ N9 M1 Blueprint5 N9T1 N9Y2
variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] earlierCellProjection earlierCellFrame N9Y2.earlierFreshTarget

def pastRemovedSquare (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K)) (T : Fin (r+K) → ℝ) : ℝ :=
  ((r+K : ℕ) : ℝ)⁻¹ * dot ((1-earlierCellProjection W β hβ δ r K e p)*ᵥT)
    ((1-earlierCellProjection W β hβ δ r K e p)*ᵥT)

theorem measurable_pastRemovedSquare (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (e : Fin K) : Measurable (Function.uncurry (pastRemovedSquare W β hβ δ r K e)) := by
  have hP : Measurable (fun v : OriginalPastRows (growingQueryTime δ e.val) (r+K) × (Fin (r+K) → ℝ) =>
      earlierCellProjection W β hβ δ r K e v.1) :=
    (measurable_earlierCellProjection W β hβ δ r K e).comp measurable_fst
  unfold Function.uncurry pastRemovedSquare dot Matrix.mulVec dotProduct
  fun_prop

def freshRemovedSquare (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K))
    (u : Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
      (Horizon δ K-growingQueryTime δ (e.val+1))) : ℝ :=
  pastRemovedSquare W β hβ δ r K e p
    (fun i => earlierFreshTarget W β hβ δ hδ K e (p i) (u i))

theorem measurable_freshRemovedSquare (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) :
    Measurable (Function.uncurry (freshRemovedSquare W β hβ δ hδ r K e)) := by
  let R : OriginalPastRows (growingQueryTime δ e.val) (r+K) ×
      (Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1))) →
      OriginalPastRows (growingQueryTime δ e.val) (r+K) × (Fin (r+K) → ℝ) :=
    fun u => (u.1,fun i => earlierFreshTarget W β hβ δ hδ K e (u.1 i) (u.2 i))
  have hR : Measurable R := measurable_fst.prodMk (Measurable.of_eval fun i : Fin (r+K) =>
    (measurable_earlierFreshTarget_joint W β hβ δ hδ K e).comp
      (f := fun u : OriginalPastRows (growingQueryTime δ e.val) (r+K) ×
        (Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1))) => (u.1 i,u.2 i))
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  change Measurable (Function.uncurry (pastRemovedSquare W β hβ δ r K e) ∘
    R)
  exact (measurable_pastRemovedSquare W β hβ δ r K e).comp hR

theorem freshRemovedSquare_eq_rows (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K)
    (p : OriginalPastRows (growingQueryTime δ e.val) (r+K))
    (u : Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
      (Horizon δ K-growingQueryTime δ (e.val+1))) :
    freshRemovedSquare W β hβ δ hδ r K e p u =
      ((r+K : ℕ) : ℝ)⁻¹ * ∑ j : Fin e.val,
        (∑ i, earlierRemovedFrame W β hβ δ r K e p j i*
          earlierFreshTarget W β hβ δ hδ K e (p i) (u i))^2 := by
  exact congrArg (((r+K : ℕ) : ℝ)⁻¹ * ·)
    (complement_projection_square_eq_rows (earlierCellProjection W β hβ δ r K e p)
      (earlierCellProjection_symm W β hβ δ r K e p)
      (earlierCellProjection_idempotent W β hβ δ r K e p)
      (earlierRemovedFrame W β hβ δ r K e p) (earlierRemovedFrame_projection W β hβ δ r K e p) _)

theorem freshTargetCoordinate_memLp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) (n : ℕ)
    (p : OriginalPastRows (growingQueryTime δ e.val) n) (i : Fin n) (q : ℝ≥0∞) :
    MemLp (fun u => earlierFreshTarget W β hβ δ hδ K e (p i) (u i)) q
      (freshRowsLaw W (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) n) :=
  (earlierFreshTarget_memLp W β hβ δ hδ K e (p i) q).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => earlierRowFreshLaw W δ K e) i)

theorem freshRemovedSquare_conditional_moments (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K) (e : Fin K) :
    ∀ᵐ p ∂Measure.pi (fun _ : Fin (r+K) => earlierRowPastLaw W δ e),
      (∫ u, freshRemovedSquare W β hβ δ hδ r K e p u
        ∂freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K)) ≤
        (e.val : ℝ)*meshDuration δ e.val/(((r+K : ℕ) : ℝ)*(actualFineScale W β δ e.val)^2) ∧
      (∫ u, (freshRemovedSquare W β hβ δ hδ r K e p u)^2
        ∂freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K)) ≤
        3*(e.val : ℝ)^2*(meshDuration δ e.val)^2/
          (((r+K : ℕ) : ℝ)^2*(actualFineScale W β δ e.val)^4) := by
  let Q := freshRowsLaw W (growingQueryDuration δ e.val)
    (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K)
  letI : IsProbabilityMeasure Q := freshRowsLaw_probability W _ _ _
  let v := meshDuration δ e.val/(actualFineScale W β δ e.val)^2
  have hv : 0 ≤ v := div_nonneg (growingQueryDuration δ e.val).coe_nonneg (sq_nonneg _)
  filter_upwards [earlierFreshTargets_conditional_moments W β hβ δ hδ K e (r+K)] with p hp
  let T := fun (i : Fin (r+K)) (u : Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
    (Horizon δ K-growingQueryTime δ (e.val+1))) => earlierFreshTarget W β hβ δ hδ K e (p i) (u i)
  let E := earlierRemovedFrame W β hβ δ r K e p
  have hm (i : Fin (r+K)) : Measurable (T i) :=
    (measurable_earlierFreshTarget W β hβ δ hδ K e (p i)).comp (measurable_pi_apply i)
  have hT (i : Fin (r+K)) (q : ℝ≥0∞) : MemLp (T i) q Q :=
    freshTargetCoordinate_memLp W β hβ δ hδ K e (r+K) p i q
  have hind : iIndepFun T Q := earlierFreshTargets_independent W β hβ δ hδ K e (r+K) p
  have hc (i : Fin (r+K)) : (∫ u, T i u ∂Q)=0 := (hp i).1
  have h2 (i : Fin (r+K)) : (∫ u, T i u^2 ∂Q) ≤ v := (hp i).2.1
  have h4 (i : Fin (r+K)) : (∫ u, T i u^4 ∂Q) ≤ 3*v^2 := by
    exact (hp i).2.2.trans_eq (by dsimp only [v]; simp only [div_pow,← pow_mul]; ring)
  have hrow (j : Fin e.val) : (∑ i, E j i^2)=1 := earlierRemovedFrame_unit W β hβ δ r K e p j
  have hs := projection_second_moment_le Q T (fun i => hT i 2) hind hc v h2 e.val E hrow
    ((r+K : ℕ) : ℝ) (Nat.cast_pos.mpr hn)
  have hf := projection_fourth_moment_of_coordinates Q T hm (fun i => hT i 4) hind hc v hv h2 h4
    e.val E hrow ((r+K : ℕ) : ℝ)
  have he : freshRemovedSquare W β hβ δ hδ r K e p =
      (fun u => ((r+K : ℕ) : ℝ)⁻¹*∑ j : Fin e.val, (∑ i, E j i*T i u)^2) :=
    funext (freshRemovedSquare_eq_rows W β hβ δ hδ r K e p)
  rw [he]
  exact ⟨hs.trans_eq (by dsimp only [v]; ring),
    hf.trans_eq (by dsimp only [v]; simp only [div_pow,← pow_mul]; ring)⟩

end SKConstants.Completion.Y1
