module
public import SKConstants.ParisiFullPosteriorProfile
public import SKConstants.ScalarProcessWeightedProducts

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]
local instance ParisiFullNormalizedRows_localInstance1 (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

def actualParisiPosteriorIntervalScale (W : BrownianSystem Ω) (β : ℝ) (S T : ℝ≥0) : ℝ≥0 :=
  NNReal.sqrt (Real.toNNReal (actualParisiFullOverlap W β T-actualParisiFullOverlap W β S))

lemma actualParisiPosteriorIntervalScale_pos (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hST : S < T) : 0 < actualParisiPosteriorIntervalScale W β S T := by
  exact NNReal.sqrt_pos.mpr (Real.toNNReal_pos.mpr (actualParisiFullOverlap_strict_drop W β hβ S T hST))

lemma actualParisiPosteriorIntervalScale_sq (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (S T : ℝ≥0) (hST : S < T) :
    (actualParisiPosteriorIntervalScale W β S T:ℝ)^2=
      actualParisiFullOverlap W β T-actualParisiFullOverlap W β S := by
  rw [← NNReal.coe_pow,actualParisiPosteriorIntervalScale,NNReal.sq_sqrt,
    Real.coe_toNNReal _ (actualParisiFullOverlap_strict_drop W β hβ S T hST).le]

def actualParisiNormalizedPosteriorRow (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (d : ℕ) (w : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => actualParisiMagnetizationIncrement W β (t i) (t (i+1)) w /
    (actualParisiPosteriorIntervalScale W β (t i) (t (i+1)):ℝ))

lemma measurable_actualParisiNormalizedPosteriorRow (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (d : ℕ) : Measurable (actualParisiNormalizedPosteriorRow W β t d) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  exact (measurable_actualParisiMagnetizationIncrement W β _ _).div_const _

theorem actualParisiNormalizedPosteriorRow_secondMoment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (d : ℕ) (a : EuclideanSpace ℝ (Fin d)) :
    (∫ w,⟪actualParisiNormalizedPosteriorRow W β t d w,a⟫_ℝ^2 ∂W.law)=‖a‖^2 := by
  let s : Fin d → ℝ≥0 := fun i => actualParisiPosteriorIntervalScale W β (t i) (t (i+1))
  let c : ℕ → ℝ := fun k => if hk : k<d then a ⟨k,hk⟩/(s ⟨k,hk⟩:ℝ) else 0
  have hs (i : Fin d) : 0 < s i := actualParisiPosteriorIntervalScale_pos W β hβ _ _
    (ht (Nat.lt_succ_self _))
  have he (w : Ω) : ⟪actualParisiNormalizedPosteriorRow W β t d w,a⟫_ℝ=
      ∑ i ∈ Finset.range d,c i*actualParisiMagnetizationIncrement W β (t i) (t (i+1)) w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,Pi.star_apply,star_trivial,actualParisiNormalizedPosteriorRow,WithLp.ofLp_toLp]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [c,Finset.mem_range.mp hk,dite_true]
    ring
  simp_rw [he]
  rw [actualParisiFullPosteriorForm_secondMoment W β hβ t ht.monotone c d]
  change (∑ i ∈ Finset.range d,c i^2*(actualParisiFullOverlap W β (t (i+1))-
      actualParisiFullOverlap W β (t i)))=‖a‖^2
  rw [EuclideanSpace.real_norm_sq_eq a,Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  let i : Fin d := ⟨k,hk'⟩
  have hsi : (s i:ℝ)≠0 := (NNReal.coe_pos.mpr (hs i)).ne'
  simp only [c,hk',dite_true]
  change (a i/(s i:ℝ))^2*(actualParisiFullOverlap W β (t (i+1))-
    actualParisiFullOverlap W β (t i))=(a i)^2
  rw [←actualParisiPosteriorIntervalScale_sq W β hβ (t i) (t (i+1)) (ht (Nat.lt_succ_self _))]
  change (a i/(s i:ℝ))^2*(s i:ℝ)^2=(a i)^2
  field_simp

end SKConstants
