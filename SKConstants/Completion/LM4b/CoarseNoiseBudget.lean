module

public import SKConstants.Completion.LM4b.QueryPredictability
public import SKConstants.Completion.LM4b.ActualZetaMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
namespace SKConstants.Completion.LM4b
open SKConstantsOAI.ZeroTemperatureSK LM4
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualCoarseScale_sum_sq_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) :
    (∑ j ∈ Finset.range k, (actualCoarseScale W β t j)^2) ≤ 1 := by
  let := W.isProbability
  have he : (∑ j ∈ Finset.range k, (actualCoarseScale W β t j)^2) =
      actualParisiFullOverlap W β (t k)-actualParisiFullOverlap W β (t 0) := by
    have hj (j : ℕ) : (actualCoarseScale W β t j)^2 =
        actualParisiFullOverlap W β (t (j+1))-actualParisiFullOverlap W β (t j) :=
      actualParisiPosteriorIntervalScale_sq W β hβ _ _ (ht (Nat.lt_succ_self j))
    simp_rw [hj]
    exact Finset.sum_range_sub (fun j : ℕ => actualParisiFullOverlap W β (t j)) k
  have h0 : 0 ≤ actualParisiFullOverlap W β (t 0) := integral_nonneg (fun _ => sq_nonneg _)
  have h1 : actualParisiFullOverlap W β (t k) ≤ 1 := by
    have hi : Integrable (fun w => (actualParisiMagnetizationObservable W β (t k) w)^2) W.law := by
      simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β (t k) (t k)
    calc
      _ ≤ ∫ _w, (1:ℝ) ∂W.law := integral_mono hi (integrable_const _) (fun w => by
        have hp := pow_le_pow_left₀ (abs_nonneg _) (actualParisiMagnetizationObservable_abs_le W β (t k) w) 2
        simpa only [sq_abs, one_pow] using hp)
      _ = 1 := by simp
  rw [he]
  linarith

theorem actualCoarseNoiseWeight_budget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) :
    (∑ j ∈ Finset.range k, (actualCoarseNoiseWeight W β t j)^2 *
      (brownianMeshVariance (fun j => t (j+1)) j : ℝ)) ≤ 1 := by
  have he (j : ℕ) : (actualCoarseNoiseWeight W β t j)^2 *
      (brownianMeshVariance (fun j => t (j+1)) j : ℝ) = (actualCoarseScale W β t j)^2 := by
    have hpos : 0 < (t (j+2):ℝ)-(t (j+1):ℝ) := sub_pos.mpr (NNReal.coe_lt_coe.mpr (ht (by omega)))
    have hs := Real.sq_sqrt hpos.le
    have hne := (Real.sqrt_pos.mpr hpos).ne'
    unfold actualCoarseNoiseWeight brownianMeshVariance
    rw [NNReal.coe_sub (ht.monotone (by omega)), div_pow, hs]
    field_simp
  simp_rw [he]
  exact actualCoarseScale_sum_sq_le_one W β hβ t ht k

theorem actualCoarseNoise_hasSubgaussianMGF (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) :
    HasSubgaussianMGF (actualNoise W Z β hβ (fun j => t (j+1)) (actualCoarseNoiseWeight W β t) k)
      4 (actualRowBaseLaw W Z) :=
  actualNoise_hasSubgaussianMGF_of_predictable W Z β hβ _
    (fun a b hab => ht.monotone (by omega)) _ k
    (actualQueryPredictableState W Z β hβ _ (fun a b hab => ht.monotone (by omega)) _)
    (actualCoarseNoiseWeight_budget W β hβ t ht k)

end SKConstants.Completion.LM4b
