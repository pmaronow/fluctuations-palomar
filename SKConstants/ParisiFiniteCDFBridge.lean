module

public import SKConstants.Upstream.OAI.Probability.SKSupport.Foundations.Cascade
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.ScalarTimeChain

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat

theorem semigroup_eq_standardGaussian_scaled {f : ℝ → ℝ} (hf : Measurable f)
    (v x : ℝ) :
    semigroup (Real.toNNReal (v ^ 2)) f x =
      ∫ y, f (x + v * y) ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun y : ℝ => v * y) =
      gaussianReal 0 (Real.toNNReal (v ^ 2)) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [sq_nonneg]
  unfold semigroup
  rw [← hmap]
  exact integral_map (by fun_prop)
    ((hf.comp (measurable_const.add measurable_id)).aestronglyMeasurable)

theorem scalarStep_eq_logSemigroup {f : ℝ → ℝ} (hf : Measurable f)
    (m v : ℝ) :
    SKConstantsOAI.SK.Analytic.scalarStep m v f = logSemigroup m (Real.toNNReal (v ^ 2)) f := by
  funext x
  unfold SKConstantsOAI.SK.Analytic.scalarStep SKConstantsOAI.SK.Analytic.gaussianStep
    SKConstantsOAI.SK.Analytic.positiveGaussianLogStep logSemigroup
  by_cases hm : m = 0
  · simp only [hm, ite_eq_left]
    exact (semigroup_eq_standardGaussian_scaled hf v x).symm
  · simp only [ite_eq_right hm]
    rw [semigroup_eq_standardGaussian_scaled
      (f := fun z => Real.exp (m * f z)) ((measurable_const.mul hf).exp)]

theorem scalarTimeStep_eq_logSemigroup {f : ℝ → ℝ} (hf : Measurable f)
    (β m : ℝ) (h : ℝ≥0) :
    SKConstantsOAI.SK.Analytic.scalarTimeStep β m h f =
      logSemigroup m (Real.toNNReal (β ^ 2) * h) f := by
  rw [SKConstantsOAI.SK.Analytic.scalarTimeStep, scalarStep_eq_logSemigroup hf]
  congr 1
  ext
  simp [mul_pow, Real.sq_sqrt h.coe_nonneg,
    sq_nonneg, mul_nonneg (sq_nonneg β) h.coe_nonneg]

theorem scalarTimeChain_uniform_eq_cascade {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (β : ℝ) (c : ℕ → ℝ≥0) (h : ℝ≥0)
    (N k : ℕ) :
    SKConstantsOAI.SK.Analytic.scalarTimeChain β
      (List.ofFn (fun i : Fin N => ((c (k + i) : ℝ), h))) f =
      cascade c (Real.toNNReal (β ^ 2) * h) f N k := by
  induction N generalizing k with
  | zero => simp [SKConstantsOAI.SK.Analytic.scalarTimeChain, cascade]
  | succ N ih =>
    rw [List.ofFn_succ, SKConstantsOAI.SK.Analytic.scalarTimeChain]
    have hlist : (List.ofFn (fun i : Fin N => ((c (k + i.succ) : ℝ), h))) =
        List.ofFn (fun i : Fin N => ((c ((k + 1) + i) : ℝ), h)) := by
      congr 1
      funext i
      simp only [Fin.val_succ]
      apply congrArg (fun j => ((c j : ℝ), h))
      change k + (i.val + 1) = (k + 1) + i.val
      omega
    rw [hlist, ih (k + 1)]
    change SKConstantsOAI.SK.Analytic.scalarTimeStep β (c k) h
      (cascade c (Real.toNNReal (β ^ 2) * h) f N (k + 1)) =
      logSemigroup (c k) (Real.toNNReal (β ^ 2) * h)
        (cascade c (Real.toNNReal (β ^ 2) * h) f N (k + 1))
    simpa only [Fin.val_zero, Nat.add_zero] using
      scalarTimeStep_eq_logSemigroup
        (cascade_regular hf hLip c _ N (k + 1)).smooth.continuous.measurable
        β (c k) h

end SKConstants.ParisiFullSupport
