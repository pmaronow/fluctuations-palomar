module

public import SKConstants.Completion.N13bc.PaddedMGF
public import SKConstants.Completion.N13bc.PaddedRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace
namespace SKConstants.Completion.N13bc
open SKConstantsOAI.ZeroTemperatureSK LW Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actual_padded_halfUpper_duration_localMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r)
    (hV : t k ≤ V) (a : EuclideanSpace ℝ (Fin (2^r))) (ha : ‖a‖ ≤ 1)
    (w : EuclideanSpace ℝ (Fin k)) (J : Finset (Fin (2^r)))
    {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hw : ∀ j, |w j / posteriorWeight W β t k j| ≤ B)
    (hd : 0 < ∑ j ∈ J, paddedDuration t h j) (transpose : Bool) :
    LocalQuadraticMGF
      (fun u => ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ)
        (if transpose then
          (halfUpperTruncation (liftMatrix h (posteriorGramError W β t k u))).transpose
        else halfUpperTruncation (liftMatrix h (posteriorGramError W β t k u)))
        (coordinateProjection J (liftVector h w))⟫_ℝ /
          Real.sqrt (∑ j ∈ J, paddedDuration t h j))
      (linkedScalarLaw W Z β V) (weightedProducerVariance B R r)
      (weightedProducerRadius B R r) := by
  let μ := linkedScalarLaw W Z β V
  let T := fun u : (Bool × Ω) × A => liftVector h (posteriorRow W β t k u)
  have hTm : Measurable T := measurable_liftVector h _ (measurable_posteriorRow W β t k)
  have hproj := paddedPosterior_unit_hasSubgaussianMGF W Z β hβ t ht V h hV hR hProxy
  have H := dyadic_half_product_localMGF_le r T hTm (paddedDuration t h)
    (paddedDuration_nonneg t ht.monotone h) a (liftVector h w) ha J hB hR hd hproj
    (paddedPosterior_secondMoment W Z β hβ t ht V h)
    (paddedPosterior_weighted_hasSubgaussianMGF W Z β hβ t ht V h w hw) transpose
  have hLp (b : EuclideanSpace ℝ (Fin (2^r))) :
      MemLp (fun u => ⟪T u,b⟫_ℝ) 2 μ :=
    (projection_hasSubgaussian_of_unit T (by linarith : 0 ≤ R) hproj b).memLp 2
  have hInt i j : Integrable (fun u => T u i*T u j) μ := by
    convert (hLp (EuclideanSpace.single i 1)).integrable_mul
      (hLp (EuclideanSpace.single j 1)) using 1
    ext u
    simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply,
      star_trivial, Pi.mul_apply]
  apply H.congr_ae
  apply ae_of_all
  intro u
  dsimp only
  rw [posteriorGramError_eq_centeredCrossMatrix W Z β hβ t ht k V hV,
    liftMatrix_centeredCross, centered_halfUpper_form_eq_productSum r T hInt]

end SKConstants.Completion.N13bc
