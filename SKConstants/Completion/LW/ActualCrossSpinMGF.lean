module

public import SKConstants.Completion.LW.ActualDyadicMGF

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem linkedSpin_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    HasSubgaussianMGF (fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1) 1
      (linkedScalarLaw W Z β V) := by
  apply HasSubgaussianMGF.of_map (X := fun u : Bool × Ω => scalarHiddenSign u.1)
    (actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).aemeasurable
  rw [(actualParisiFullQuerySpinLaw_terminal_hasLaw W Z β V).map_eq]
  exact actualParisiFullTerminalSpinLaw_spin_hasSubgaussianMGF W β hβ V

theorem queryRow_projection_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0)
    (a : EuclideanSpace ℝ (Fin k)) :
    HasSubgaussianMGF (fun u => ⟪queryRow W Z β hβ t k u,a⟫_ℝ)
      (Real.toNNReal (‖a‖^2)) (linkedScalarLaw W Z β V) := by
  simpa only [one_mul, Real.toNNReal_one] using
    projection_hasSubgaussian_of_unit (queryRow W Z β hβ t k) zero_le_one
      (fun b hb => by simpa only [Real.toNNReal_one] using
        queryRow_unit_hasSubgaussianMGF W Z β hβ t ht k V b hb) a

theorem projection_spin_centering {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {k : ℕ} (T : E → EuclideanSpace ℝ (Fin k)) (spin : E → ℝ)
    (m a : EuclideanSpace ℝ (Fin k))
    (hInt : ∀ j, Integrable (fun z => T z j*spin z) μ)
    (hMean : ∀ j, (∫ z, T z j*spin z ∂μ) = m j) (ω : E) :
    ⟪spin ω • T ω-m,a⟫_ℝ =
      centeredObservable μ (fun z => ⟪T z,a⟫_ℝ * spin z) ω := by
  have he z : ⟪T z,a⟫_ℝ * spin z = ∑ j : Fin k, a j*(T z j*spin z) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, star_trivial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi : (∫ z, ⟪T z,a⟫_ℝ * spin z ∂μ) = ⟪m,a⟫_ℝ := by
    simp_rw [he]
    rw [integral_finsetSum Finset.univ (fun j _ => (hInt j).const_mul _)]
    simp only [integral_const_mul, hMean, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Pi.star_apply, star_trivial]
  rw [inner_sub_left, real_inner_smul_left]
  unfold centeredObservable
  rw [hi]
  ring

theorem actual_spin_row_localMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0) (hV : t (k+1) ≤ V)
    (a : EuclideanSpace ℝ (Fin k)) (ha : ‖a‖ ≤ 1)
    {R : ℝ} (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R) (query : Bool) :
    LocalQuadraticMGF
      (fun u => ⟪scalarHiddenSign u.1.1 •
        (if query then queryRow W Z β hβ t k u else posteriorRow W β t k u) -
        (if query then queryWeight W β t k else posteriorWeight W β t k),a⟫_ℝ)
      (linkedScalarLaw W Z β V) (productMGFVariance R) (productMGFRadius R) := by
  let μ := linkedScalarLaw W Z β V
  let spin (u : (Bool × Ω) × A) := scalarHiddenSign u.1.1
  have hspin : HasSubgaussianMGF spin 1 μ := linkedSpin_hasSubgaussianMGF W Z β hβ V
  have hspinMeas : Measurable spin := (measurable_of_finite scalarHiddenSign).comp
    (measurable_fst.comp measurable_fst)
  have hV0 : t k ≤ V := (ht.monotone (Nat.le_succ _)).trans hV
  have hbase (T : ((Bool × Ω) × A) → EuclideanSpace ℝ (Fin k))
      (hT : Measurable T) (m : EuclideanSpace ℝ (Fin k))
      (hProj : ∀ b, ‖b‖ ≤ 1 → HasSubgaussianMGF (fun u => ⟪T u,b⟫_ℝ) (Real.toNNReal R) μ)
      (hIso : ∀ b, (∫ u, ⟪T u,b⟫_ℝ^2 ∂μ) = ‖b‖^2)
      (hMean : ∀ j, (∫ u, T u j*spin u ∂μ) = m j) :
      LocalQuadraticMGF (fun u => ⟪spin u • T u-m,a⟫_ℝ) μ
        (productMGFVariance R) (productMGFRadius R) := by
    have hprojAll b := projection_hasSubgaussian_of_unit T (by linarith : 0 ≤ R) hProj b
    have hLp b : MemLp (fun u => ⟪T u,b⟫_ℝ) 2 μ := (hprojAll b).memLp 2
    have hspinLp : MemLp spin 2 μ := hspin.memLp 2
    have hInt j : Integrable (fun u => T u j*spin u) μ := by
      convert (hLp (EuclideanSpace.single j 1)).integrable_mul hspinLp using 1
      ext u
      simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial, Pi.mul_apply]
    have H := subGaussian_correlated_product_balanced_localMGF μ
      (fun u => ⟪T u,a⟫_ℝ) spin (by fun_prop) hspinMeas (Real.toNNReal R)
      (by apply NNReal.coe_le_coe.mp; simpa only [NNReal.coe_one,
        Real.coe_toNNReal _ (by linarith : 0 ≤ R)] using hR)
      (hProj a ha) hspin ((hIso a).le.trans (by nlinarith [norm_nonneg a]))
    rw [Real.coe_toNNReal _ (by linarith : 0 ≤ R)] at H
    apply H.congr_ae
    exact ae_of_all _ (fun u => projection_spin_centering T spin m a hInt hMean u)
  cases query
  · refine hbase (posteriorRow W β t k) (measurable_posteriorRow W β t k)
      (posteriorWeight W β t k) ?_ ?_ ?_
    · intro b hb
      apply hasSubgaussianMGF_of_proxy_le
        (posteriorRow_unit_hasSubgaussianMGF W Z β hβ t ht k V hV0 b hb)
      exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal _ (by linarith : 0 ≤ R)] using hProxy)
    · exact posteriorRow_secondMoment W Z β hβ t ht k V
    · intro j
      exact posteriorRow_spin_moment W Z β hβ t ht k j V
        ((ht.monotone (by omega)).trans hV)
  · refine hbase (queryRow W Z β hβ t k) (measurable_queryRow W Z β hβ t k)
      (queryWeight W β t k) ?_ ?_ ?_
    · intro b hb
      apply hasSubgaussianMGF_of_proxy_le (queryRow_unit_hasSubgaussianMGF W Z β hβ t ht k V b hb)
      exact NNReal.coe_le_coe.mp (by simpa only [NNReal.coe_one, Real.coe_toNNReal _ (by linarith : 0 ≤ R)] using hR)
    · exact queryRow_secondMoment W Z β hβ t ht k V
    · intro j
      exact queryRow_spin_moment W Z β hβ t ht.monotone k j V
        ((ht.monotone (by omega)).trans hV)

theorem actual_cross_row_duration_localMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ) (hV : t (2^r) ≤ V)
    (a : EuclideanSpace ℝ (Fin (2^r))) (ha : ‖a‖ ≤ 1)
    (I : DyadicCore.Interval r) {R : ℝ} (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R) (transpose : Bool) :
    LocalQuadraticMGF
      (fun u => ⟪a,Matrix.toEuclideanCLM (𝕜 := ℝ)
        (if transpose then (crossError W Z β hβ t V (2^r) u).transpose
          else crossError W Z β hβ t V (2^r) u)
        (coordinateProjection (dyadicIntervalSets r I) (posteriorWeight W β t (2^r)))⟫_ℝ /
          Real.sqrt (nodeDuration r (fun j => previousDuration t j) I))
      (linkedScalarLaw W Z β V) (productMGFVariance R) (productMGFRadius R) := by
  let μ := linkedScalarLaw W Z β V
  let T := posteriorRow (A := A) W β t (2^r)
  let g := queryRow W Z β hβ t (2^r)
  let s := posteriorWeight W β t (2^r)
  let w := coordinateProjection (dyadicIntervalSets r I) s
  let d := nodeDuration r (fun j => previousDuration t j) I
  have hTm : Measurable T := measurable_posteriorRow W β t (2^r)
  have hgm : Measurable g := measurable_queryRow W Z β hβ t (2^r)
  have hd : 0 < d := Finset.sum_pos
    (fun j _ => sub_pos.mpr (NNReal.coe_lt_coe.mpr (ht (Nat.lt_succ_self _))))
    (dyadicIntervalSets_nonempty r I)
  have hR0 : 0 ≤ R := by linarith
  have hT b := posteriorRow_projection_hasSubgaussianMGF W Z β hβ t ht (2^r) V hV hProxy b
  have hg b := queryRow_projection_hasSubgaussianMGF W Z β hβ t ht (2^r) V b
  have hTa : HasSubgaussianMGF (fun u => ⟪T u,a⟫_ℝ) (Real.toNNReal R) μ := by
    apply hasSubgaussianMGF_of_proxy_le (hT a)
    exact Real.toNNReal_mono (mul_le_of_le_one_right hR0 (by nlinarith [norm_nonneg a]))
  have hga : HasSubgaussianMGF (fun u => ⟪g u,a⟫_ℝ) (Real.toNNReal R) μ := by
    apply hasSubgaussianMGF_of_proxy_le (hg a)
    exact Real.toNNReal_mono ((by nlinarith [norm_nonneg a] : ‖a‖^2 ≤ 1).trans hR)
  have hgw : HasSubgaussianMGF (fun u => ⟪g u,w⟫_ℝ) (Real.toNNReal d) μ := by
    apply hasSubgaussianMGF_of_proxy_le (hg w)
    exact Real.toNNReal_mono (posteriorWeight_node_norm_sq_le W β hβ t ht r I)
  have hTw : HasSubgaussianMGF (fun u => ⟪T u,w⟫_ℝ) (Real.toNNReal d) μ := by
    have H := posteriorRow_weighted_block_hasSubgaussianMGF W Z β hβ t ht (2^r) V s
      (B := 1) (fun j => by
        have hj : s j ≠ 0 := (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos
          W β hβ (t j) (t (j+1)) (ht (Nat.lt_succ_self _)))).ne'
        change |s j/s j| ≤ 1
        simp only [div_self hj, abs_one]; exact le_refl 1) (dyadicIntervalSets r I)
    simpa only [T, w, d, nodeDuration, μ, one_pow, one_mul] using H
  have hTLp b : MemLp (fun u => ⟪T u,b⟫_ℝ) 2 μ := (hT b).memLp 2
  have hgLp b : MemLp (fun u => ⟪g u,b⟫_ℝ) 2 μ := (hg b).memLp 2
  have hInt i j : Integrable (fun u => T u i*g u j) μ := by
    convert (hTLp (EuclideanSpace.single i 1)).integrable_mul
      (hgLp (EuclideanSpace.single j 1)) using 1
    ext u
    simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial, Pi.mul_apply]
  have hCross u : crossError W Z β hβ t V (2^r) u = centeredCrossMatrix T g μ u := rfl
  have hD : 0 < Real.toNNReal d := Real.toNNReal_pos.mpr hd
  have hRq : (1 : ℝ≥0) ≤ Real.toNNReal R := NNReal.coe_le_coe.mp
    (by simpa only [NNReal.coe_one, Real.coe_toNNReal _ hR0] using hR)
  cases transpose
  · have H := correlated_product_duration_localMGF μ (fun u => ⟪T u,a⟫_ℝ)
      (fun u => ⟪g u,w⟫_ℝ) (by fun_prop) (by fun_prop)
      (Real.toNNReal R) (Real.toNNReal d) hRq hD hTa hgw
      ((posteriorRow_secondMoment W Z β hβ t ht (2^r) V a).le.trans (by nlinarith [norm_nonneg a]))
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
      ((queryRow_secondMoment W Z β hβ t ht (2^r) V a).le.trans (by nlinarith [norm_nonneg a]))
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

end SKConstants.Completion.LW
