module

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

theorem actual_padded_cross_duration_localMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (k r : ℕ) (h : k ≤ 2^r) (hV : t k ≤ V)
    (a : EuclideanSpace ℝ (Fin (2^r))) (ha : ‖a‖ ≤ 1)
    (I : DyadicCore.Interval r)
    (hdur : 0 < nodeDuration r (paddedDuration t h) I) {R : ℝ} (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R) (transpose : Bool) :
    LocalQuadraticMGF
      (fun u => ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ)
        (if transpose then (liftMatrix h (crossError W Z β hβ t V k u)).transpose
          else liftMatrix h (crossError W Z β hβ t V k u))
        (coordinateProjection (dyadicIntervalSets r I) (liftVector h (posteriorWeight W β t k)))⟫_ℝ /
          Real.sqrt (nodeDuration r (paddedDuration t h) I))
      (linkedScalarLaw W Z β V) (productMGFVariance R) (productMGFRadius R) := by
  let μ := linkedScalarLaw W Z β V
  let T := fun u : (Bool × Ω) × A => liftVector h (posteriorRow W β t k u)
  let g := fun u => liftVector h (queryRow W Z β hβ t k u)
  let s := liftVector h (posteriorWeight W β t k)
  let w := coordinateProjection (dyadicIntervalSets r I) s
  let d := nodeDuration r (paddedDuration t h) I
  have hTm : Measurable T := measurable_liftVector h _ (measurable_posteriorRow W β t k)
  have hgm : Measurable g := measurable_liftVector h _ (measurable_queryRow W Z β hβ t k)
  have hd : 0 < d := hdur
  have hR0 : 0 ≤ R := by linarith
  have hTunit := paddedPosterior_unit_hasSubgaussianMGF W Z β hβ t ht V h hV hR hProxy
  have hgunit := paddedQuery_unit_hasSubgaussianMGF W Z β hβ t ht V h
  have hT b := projection_hasSubgaussian_of_unit T hR0 hTunit b
  have hg b := projection_hasSubgaussian_of_unit g zero_le_one
    (by simpa only [Real.toNNReal_one] using hgunit) b
  have hTa : HasSubgaussianMGF (fun u => ⟪T u,a⟫_ℝ) (Real.toNNReal R) μ := by
    apply hasSubgaussianMGF_of_proxy_le (hT a)
    exact Real.toNNReal_mono (mul_le_of_le_one_right hR0 (by nlinarith [norm_nonneg a]))
  have hga : HasSubgaussianMGF (fun u => ⟪g u,a⟫_ℝ) (Real.toNNReal R) μ := by
    apply hasSubgaussianMGF_of_proxy_le (hg a)
    apply Real.toNNReal_mono
    simpa only [one_mul] using ((by nlinarith [norm_nonneg a] : ‖a‖^2 ≤ 1).trans hR)
  have hgw : HasSubgaussianMGF (fun u => ⟪g u,w⟫_ℝ) (Real.toNNReal d) μ := by
    apply hasSubgaussianMGF_of_proxy_le (hg w)
    apply Real.toNNReal_mono
    simpa only [one_mul, w, s, d, nodeDuration] using
      paddedWeight_norm_sq_le W β hβ t ht h (dyadicIntervalSets r I)
  have hTw : HasSubgaussianMGF (fun u => ⟪T u,w⟫_ℝ) (Real.toNNReal d) μ := by
    have H := paddedPosterior_weighted_hasSubgaussianMGF W Z β hβ t ht V h
      (posteriorWeight W β t k) (B := 1) (fun j => by
        have hj : posteriorWeight W β t k j ≠ 0 :=
          (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ
            (t j) (t (j+1)) (ht (Nat.lt_succ_self _)))).ne'
        simp only [div_self hj, abs_one]; exact le_refl 1) (dyadicIntervalSets r I)
    simpa only [T, w, s, d, nodeDuration, μ, one_pow, one_mul] using H
  have hTLp b : MemLp (fun u => ⟪T u,b⟫_ℝ) 2 μ := (hT b).memLp 2
  have hgLp b : MemLp (fun u => ⟪g u,b⟫_ℝ) 2 μ := (hg b).memLp 2
  have hInt i j : Integrable (fun u => T u i*g u j) μ := by
    convert (hTLp (EuclideanSpace.single i 1)).integrable_mul
      (hgLp (EuclideanSpace.single j 1)) using 1
    ext u
    simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial, Pi.mul_apply]
  have hCross u : liftMatrix h (crossError W Z β hβ t V k u) = centeredCrossMatrix T g μ u :=
    liftMatrix_centeredCross h _ _ μ u
  have hD : 0 < Real.toNNReal d := Real.toNNReal_pos.mpr hd
  have hRq : (1 : ℝ≥0) ≤ Real.toNNReal R := NNReal.coe_le_coe.mp
    (by simpa only [NNReal.coe_one, Real.coe_toNNReal _ hR0] using hR)
  cases transpose
  · have H := correlated_product_duration_localMGF μ (fun u => ⟪T u,a⟫_ℝ)
      (fun u => ⟪g u,w⟫_ℝ) (by fun_prop) (by fun_prop)
      (Real.toNNReal R) (Real.toNNReal d) hRq hD hTa hgw
      ((paddedPosterior_secondMoment W Z β hβ t ht V h a).trans (by nlinarith [norm_nonneg a]))
    rw [Real.coe_toNNReal _ hR0, Real.coe_toNNReal _ hd.le] at H
    apply H.congr_ae
    apply ae_of_all
    intro u
    dsimp only
    simp only [Bool.false_eq_true, ite_false]
    rw [hCross, centeredCrossMatrix_bilinear T g hInt]
  · have H := correlated_product_duration_localMGF μ (fun u => ⟪g u,a⟫_ℝ)
      (fun u => ⟪T u,w⟫_ℝ) (by fun_prop) (by fun_prop)
      (Real.toNNReal R) (Real.toNNReal d) hRq hD hga hTw
      ((paddedQuery_secondMoment W Z β hβ t ht V h a).trans (by nlinarith [norm_nonneg a]))
    rw [Real.coe_toNNReal _ hR0, Real.coe_toNNReal _ hd.le] at H
    apply H.congr_ae
    apply ae_of_all
    intro u
    dsimp only
    simp only [ite_true]
    rw [real_inner_comm, matrix_transpose_inner, hCross, centeredCrossMatrix_bilinear T g hInt]
    unfold centeredObservable
    simp only [mul_comm]
    rfl

end SKConstants.Completion.N13bc
