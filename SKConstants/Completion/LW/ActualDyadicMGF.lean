module

public import SKConstants.Completion.LW.CenteredForms

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem posteriorRow_projection_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0) (hV : t k ≤ V)
    {R : ℝ} (hR : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (a : EuclideanSpace ℝ (Fin k)) :
    HasSubgaussianMGF (fun u => ⟪posteriorRow W β t k u,a⟫_ℝ)
      (Real.toNNReal (R*‖a‖^2)) (linkedScalarLaw W Z β V) := by
  have hR0 : 0 ≤ R := (NNReal.coe_nonneg _).trans hR
  apply projection_hasSubgaussian_of_unit _ hR0 _ a
  intro b hb
  apply hasSubgaussianMGF_of_proxy_le
    (posteriorRow_unit_hasSubgaussianMGF W Z β hβ t ht k V hV b hb)
  apply NNReal.coe_le_coe.mp
  simpa only [Real.coe_toNNReal _ hR0] using hR

theorem posteriorRow_coordinate_crossMoment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0) (hV : t k ≤ V)
    (i j : Fin k) :
    (∫ u, posteriorRow W β t k u i*posteriorRow W β t k u j
      ∂linkedScalarLaw W Z β V) = if i=j then 1 else 0 := by
  have hLp (a : EuclideanSpace ℝ (Fin k)) :
      MemLp (fun u => ⟪posteriorRow W β t k u,a⟫_ℝ) 2 (linkedScalarLaw W Z β V) :=
    (posteriorRow_projection_hasSubgaussianMGF W Z β hβ t ht k V hV (le_refl _) a).memLp 2
  have H := projection_crossMoment_of_isometry (posteriorRow (A := A) W β t k) hLp
    (posteriorRow_secondMoment W Z β hβ t ht k V)
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa only [EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left,
    map_one, one_mul, mul_one, PiLp.single_apply, Pi.single_apply, eq_comm,
    starRingEnd_apply, star_trivial] using H

theorem posteriorGramError_eq_centeredCrossMatrix
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0) (hV : t k ≤ V)
    (u : (Bool × Ω) × A) :
    posteriorGramError W β t k u =
      centeredCrossMatrix (posteriorRow W β t k) (posteriorRow W β t k)
        (linkedScalarLaw W Z β V) u := by
  ext i j
  simp only [posteriorGramError, centeredCrossMatrix,
    posteriorRow_coordinate_crossMoment W Z β hβ t ht k V hV]

theorem posteriorRow_pair_integrable
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0) (hV : t k ≤ V)
    (i j : Fin k) :
    Integrable (fun u => posteriorRow W β t k u i*posteriorRow W β t k u j)
      (linkedScalarLaw W Z β V) := by
  have hLp (a : EuclideanSpace ℝ (Fin k)) :
      MemLp (fun u => ⟪posteriorRow W β t k u,a⟫_ℝ) 2 (linkedScalarLaw W Z β V) :=
    (posteriorRow_projection_hasSubgaussianMGF W Z β hβ t ht k V hV (le_refl _) a).memLp 2
  convert (hLp (EuclideanSpace.single i 1)).integrable_mul (hLp (EuclideanSpace.single j 1)) using 1
  ext u
  simp only [EuclideanSpace.inner_single_right, mul_one, one_mul, starRingEnd_apply,
    star_trivial, Pi.mul_apply]

def weightedProducerVariance (B R : ℝ) (r : ℕ) : ℝ :=
  (B*(r+1 : ℝ))^2*productMGFVariance R

def weightedProducerRadius (B R : ℝ) (r : ℕ) : ℝ :=
  productMGFRadius R/(B*(r+1 : ℝ))

theorem weightedProducerParameters_pos {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R) (r : ℕ) :
    0 < weightedProducerVariance B R r ∧ 0 < weightedProducerRadius B R r := by
  have hp := productMGFParameters_pos hR
  have hF := hp.1
  have hG := hp.2
  constructor
  · unfold weightedProducerVariance; positivity
  · unfold weightedProducerRadius; positivity

theorem actual_halfUpper_duration_localMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ) (hV : t (2^r) ≤ V)
    (a w : EuclideanSpace ℝ (Fin (2^r))) (ha : ‖a‖ ≤ 1)
    (J : Finset (Fin (2^r))) {B R : ℝ} (hB : 0 < B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hw : ∀ j, |w j / posteriorWeight W β t (2^r) j| ≤ B)
    (hd : 0 < ∑ j ∈ J, previousDuration t j) (transpose : Bool) :
    LocalQuadraticMGF
      (fun u => ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ)
        (if transpose then (halfUpperTruncation (posteriorGramError W β t (2^r) u)).transpose
          else halfUpperTruncation (posteriorGramError W β t (2^r) u))
        (coordinateProjection J w)⟫_ℝ / Real.sqrt (∑ j ∈ J, previousDuration t j))
      (linkedScalarLaw W Z β V) (weightedProducerVariance B R r) (weightedProducerRadius B R r) := by
  have hproj (b : EuclideanSpace ℝ (Fin (2^r))) (hb : ‖b‖ ≤ 1) :
      HasSubgaussianMGF (fun u => ⟪posteriorRow W β t (2^r) u,b⟫_ℝ)
        (Real.toNNReal R) (linkedScalarLaw W Z β V) := by
    apply hasSubgaussianMGF_of_proxy_le
      (posteriorRow_unit_hasSubgaussianMGF W Z β hβ t ht (2^r) V hV b hb)
    exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal _ (by linarith : 0 ≤ R)] using hProxy)
  have H := dyadic_half_product_localMGF r (posteriorRow W β t (2^r))
    (measurable_posteriorRow W β t (2^r)) (fun j => previousDuration t j)
    (fun j => sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht.monotone (Nat.le_succ _))))
    a w ha J hB hR hd hproj (posteriorRow_secondMoment W Z β hβ t ht (2^r) V)
    (posteriorRow_weighted_block_hasSubgaussianMGF W Z β hβ t ht (2^r) V w hw) transpose
  apply H.congr_ae
  apply ae_of_all
  intro u
  dsimp only
  rw [posteriorGramError_eq_centeredCrossMatrix W Z β hβ t ht (2^r) V hV]
  rw [centered_halfUpper_form_eq_productSum r _
    (posteriorRow_pair_integrable W Z β hβ t ht (2^r) V hV)]

end SKConstants.Completion.LW
