module

public import SKConstants.SKModel
public import SKConstants.GaussianMaximum
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Metric Set
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants

set_option backward.isDefEq.respectTransparency false

lemma euclidean_real_ball_scale (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0 < r) :
    volume.real (ball x r) = r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, measureReal_def]

lemma euclidean_separated_card_le (n : ℕ)
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hN : ∀ x ∈ N, ‖x‖ ≤ 1)
    (hsep : (↑N : Set (EuclideanSpace ℝ (Fin n))).Pairwise
      (fun x y => (1 / 4 : ℝ) < dist x y)) :
    (N.card : ℝ) ≤ (9 : ℝ) ^ n := by
  have hd : PairwiseDisjoint (↑N : Set (EuclideanSpace ℝ (Fin n)))
      (fun x => ball x (1 / 8 : ℝ)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hdist := dist_triangle x z y
    have hxz : dist x z < (1 / 8 : ℝ) := by simpa [dist_comm] using hzx
    have hzy' : dist z y < (1 / 8 : ℝ) := hzy
    have hxy' := hsep hx hy hxy
    linarith
  have hsub : (⋃ x ∈ N, ball x (1 / 8 : ℝ)) ⊆
      ball (0 : EuclideanSpace ℝ (Fin n)) (9 / 8 : ℝ) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    have hdist := dist_triangle z x 0
    have hxn : dist x 0 ≤ 1 := by simpa using hN x hx
    change dist z 0 < (9 / 8 : ℝ)
    have hzxn : dist z x < (1 / 8 : ℝ) := hzx
    linarith
  have hvol := measureReal_mono hsub (measure_ball_lt_top (μ := volume)).ne
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hvol
  simp_rw [euclidean_real_ball_scale n _ (1 / 8 : ℝ) (by norm_num)] at hvol
  rw [Finset.sum_const, nsmul_eq_mul,
    euclidean_real_ball_scale n _ (9 / 8 : ℝ) (by norm_num)] at hvol
  have hv : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume _ (by norm_num)))
      (measure_ball_lt_top (μ := volume)).ne
  have hp : 0 < (1 / 8 : ℝ) ^ n := pow_pos (by norm_num) _
  have he : (9 / 8 : ℝ) ^ n = (9 : ℝ) ^ n * (1 / 8 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  rw [he] at hvol
  nlinarith [mul_pos hp hv]

theorem exists_euclidean_quarter_net (n : ℕ) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ N, ‖x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → ∃ y ∈ N, dist x y ≤ (1 / 4 : ℝ)) ∧
      (N.card : ℝ) ≤ (9 : ℝ) ^ n := by
  let A := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨D, hDA, hDf, hDc⟩ :=
    exists_finite_isCover_of_isCompact (ε := (1 / 8 : ℝ≥0)) (by norm_num)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hcover : coveringNumber (1 / 8 : ℝ≥0) A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hDf)
    exact hDc.coveringNumber_le_encard hDA
  have hpack : packingNumber (1 / 4 : ℝ≥0) A ≠ ⊤ := by
    apply ne_top_of_le_ne_top hcover
    calc
      _ = packingNumber (2 * (1 / 8 : ℝ≥0)) A := by norm_num
      _ ≤ externalCoveringNumber (1 / 8 : ℝ≥0) A :=
        packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ coveringNumber (1 / 8 : ℝ≥0) A := externalCoveringNumber_le_coveringNumber _ _
  let S := maximalSeparatedSet (1 / 4 : ℝ≥0) A
  have hSf : S.Finite := Set.encard_ne_top_iff.mp (by
    rw [show S.encard = packingNumber (1 / 4 : ℝ≥0) A from encard_maximalSeparatedSet hpack]
    exact hpack)
  have hSA : S ⊆ A := maximalSeparatedSet_subset
  have hSc : IsCover (1 / 4 : ℝ≥0) A S := isCover_maximalSeparatedSet hpack
  have hSs : IsSeparated (1 / 4 : ℝ≥0) S := isSeparated_maximalSeparatedSet
  refine ⟨hSf.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    simpa only [A, mem_closedBall, dist_zero_right] using hSA (hSf.mem_toFinset.mp hx)
  · intro x hx
    have hxA : x ∈ A := by simpa only [A, mem_closedBall, dist_zero_right] using hx
    obtain ⟨y, hy, hxy⟩ := hSc hxA
    refine ⟨y, hSf.mem_toFinset.mpr hy, ?_⟩
    change edist x y ≤ ((1 / 4 : ℝ≥0) : ℝ≥0∞) at hxy
    rw [edist_dist] at hxy
    have hh : ENNReal.ofReal (1 / 4 : ℝ) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [← hh] at hxy
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hxy
  · apply euclidean_separated_card_le n hSf.toFinset
    · intro x hx
      simpa only [A, mem_closedBall, dist_zero_right] using hSA (hSf.mem_toFinset.mp hx)
    · intro x hx y hy hxy
      have h := hSs (hSf.mem_toFinset.mp hx) (hSf.mem_toFinset.mp hy) hxy
      change ((1 / 4 : ℝ≥0) : ℝ≥0∞) < edist x y at h
      rw [edist_dist] at h
      have hh : ENNReal.ofReal (1 / 4 : ℝ) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      rw [← hh] at h
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp h

theorem opNorm_le_of_quarter_net {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hN : ∀ x ∈ N, ‖x‖ ≤ 1)
    (hcover : ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ N, dist x y ≤ (1 / 4 : ℝ))
    (b : ℝ) (hb : 0 ≤ b)
    (hbil : ∀ x ∈ N, ∀ y ∈ N, |⟪A x, y⟫_ℝ| ≤ b) :
    ‖A‖ ≤ 2 * b := by
  have hnorm : ‖A‖ ≤ b + ‖A‖ / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨x₀, hx₀, hxx₀⟩ := hcover x hx.le
    obtain ⟨y₀, hy₀, hyy₀⟩ := hcover y hy.le
    have h1 : |⟪A (x - x₀), y⟫_ℝ| ≤ ‖A‖ / 4 := by
      calc
        _ ≤ ‖A (x - x₀)‖ * ‖y‖ := abs_real_inner_le_norm _ _
        _ = ‖A (x - x₀)‖ := by rw [hy, mul_one]
        _ ≤ ‖A‖ * ‖x - x₀‖ := A.le_opNorm _
        _ ≤ ‖A‖ * (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left
          (by simpa only [dist_eq_norm] using hxx₀) (norm_nonneg _)
        _ = _ := by ring
    have h2 : |⟪A x₀, y - y₀⟫_ℝ| ≤ ‖A‖ / 4 := by
      calc
        _ ≤ ‖A x₀‖ * ‖y - y₀‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖x₀‖) * (1 / 4 : ℝ) := by
          gcongr
          · exact A.le_opNorm _
          · simpa only [dist_eq_norm] using hyy₀
        _ ≤ (‖A‖ * 1) * (1 / 4 : ℝ) := by gcongr; exact hN x₀ hx₀
        _ = _ := by ring
    have he : ⟪A x, y⟫_ℝ = ⟪A (x - x₀), y⟫_ℝ +
        ⟪A x₀, y - y₀⟫_ℝ + ⟪A x₀, y₀⟫_ℝ := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h3 := hbil x₀ hx₀ y₀ hy₀
    simp only [RCLike.re_to_real]
    rw [he]
    linarith [le_abs_self ⟪A (x - x₀), y⟫_ℝ,
      le_abs_self ⟪A x₀, y - y₀⟫_ℝ, le_abs_self ⟪A x₀, y₀⟫_ℝ]
  linarith

lemma goeBilinear_variance_unit_ball_le {n : ℕ} (sigma : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    Var[GaussianProposal.goeBilinear sigma x y;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] ≤ 4 * sigma ^ 2 := by
  have hd (u v : EuclideanSpace ℝ (Fin n)) :
      GaussianProposal.dot u v = ⟪u, v⟫_ℝ := by
    simp [GaussianProposal.dot, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [← covariance_self (GaussianProposal.goeBilinear_gaussian sigma x y).aemeasurable,
    GaussianProposal.goeBilinear_covariance]
  simp_rw [hd]
  simp only [real_inner_comm x y]
  have hxx : ⟪x, x⟫_ℝ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg x]
  have hyy : ⟪y, y⟫_ℝ ≤ 1 := by
    rw [real_inner_self_eq_norm_sq]
    nlinarith [norm_nonneg y]
  have hxy : |⟪x, y⟫_ℝ| ≤ 1 := by
    apply (abs_real_inner_le_norm x y).trans
    nlinarith [mul_le_mul_of_nonneg_right hx (norm_nonneg y)]
  have hprod : ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ ≤ 1 :=
    by nlinarith [mul_le_mul_of_nonneg_right hxx (real_inner_self_nonneg (x := y))]
  have hs : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ 1 := by
    nlinarith [sq_abs ⟪x, y⟫_ℝ, abs_nonneg ⟪x, y⟫_ℝ]
  have hb : ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ + ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ 2 := by linarith
  calc
    _ ≤ 2 * sigma ^ 2 * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

theorem gaussian_centered_two_sided_tail_of_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : HasGaussianLaw X μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (V u : ℝ) (hV : 0 < V) (hu : 0 < u) (hvariance : Var[X; μ] ≤ V) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * V)) := by
  have hlocal : Concentration.LocalQuadraticMGF X μ (V / 2) (u / V) := by
    constructor
    · intro t _
      exact (centered_gaussian_exponential_integral μ X hX hmean t).1
    · intro t _
      change (∫ ω, Real.exp (t * X ω) ∂μ) ≤ _
      rw [(centered_gaussian_exponential_integral μ X hX hmean t).2]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hvariance (sq_nonneg t)]
  have h := Concentration.localQuadraticMGF_two_sided hlocal
    (by positivity) (by positivity) hu
  have heq : min (u ^ 2 / (4 * (V / 2))) ((u / V) * u / 2) =
      u ^ 2 / (2 * V) := by
    have ha : u ^ 2 / (4 * (V / 2)) = u ^ 2 / (2 * V) := by ring
    have hb : (u / V) * u / 2 = u ^ 2 / (2 * V) := by ring
    rw [ha, hb, min_self]
  rw [heq] at h
  simpa only [neg_div] using h

theorem sk_goeBilinear_unit_ball_tail {n : ℕ} (hn : 0 < n)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (u : ℝ) (hu : 0 < u) :
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
      {z | u ≤ |GaussianProposal.goeBilinear (1 / Real.sqrt (2 * (n : ℝ))) x y z|} ≤
      2 * Real.exp (-(n : ℝ) * u ^ 2 / 4) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hv : Var[GaussianProposal.goeBilinear (1 / Real.sqrt (2 * (n : ℝ))) x y;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] ≤ 2 / (n : ℝ) := by
    have h := goeBilinear_variance_unit_ball_le (1 / Real.sqrt (2 * (n : ℝ))) x y hx hy
    have he : 4 * (1 / Real.sqrt (2 * (n : ℝ))) ^ 2 = 2 / (n : ℝ) := by
      rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
      field_simp
      ring
    rwa [he] at h
  have h := gaussian_centered_two_sided_tail_of_variance_le
    (GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (GaussianProposal.goeBilinear (1 / Real.sqrt (2 * (n : ℝ))) x y)
    (GaussianProposal.goeBilinear_gaussian _ _ _) (GaussianProposal.goeBilinear_mean _ _ _)
    (2 / (n : ℝ)) u (by positivity) hu hv
  convert h using 1
  congr 2
  field_simp
  norm_num

lemma goeBilinear_eq_inner {n : ℕ} (sigma : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    GaussianProposal.goeBilinear sigma x y z =
      ⟪x, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (GaussianProposal.goeMatrix sigma z) y⟫_ℝ := by
  rw [GaussianProposal.goeBilinear_eq_matrix, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sk_goe_operator_norm_tail {n : ℕ} (hn : 0 < n) (u : ℝ) (hu : 0 < u) :
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
      {z | 2 * u < ‖GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z‖} ≤
      2 * (9 : ℝ) ^ (2 * n) * Real.exp (-(n : ℝ) * u ^ 2 / 4) := by
  let μ := GaussianProposal.primitiveGaussian (Fin n × Fin n)
  let sigma : ℝ := 1 / Real.sqrt (2 * (n : ℝ))
  obtain ⟨N, hN, hcover, hcard⟩ := exists_euclidean_quarter_net n
  let E : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      Set (EuclideanSpace ℝ (Fin n × Fin n)) :=
    fun x y => {z | u ≤ |GaussianProposal.goeBilinear sigma x y z|}
  have hsub : {z | 2 * u < ‖GaussianProposal.goeMatrix sigma z‖} ⊆
      ⋃ x ∈ N, ⋃ y ∈ N, E x y := by
    intro z hz
    by_contra hzE
    have hbil : ∀ x ∈ N, ∀ y ∈ N,
        |⟪Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (GaussianProposal.goeMatrix sigma z) x, y⟫_ℝ| ≤ u := by
      intro x hx y hy
      rw [real_inner_comm, ← goeBilinear_eq_inner]
      have hnE : ¬ u ≤ |GaussianProposal.goeBilinear sigma y x z| := by
        intro he
        apply hzE
        simp only [Set.mem_iUnion]
        exact ⟨y, hy, x, hx, he⟩
      exact (lt_of_not_ge hnE).le
    have hbound := opNorm_le_of_quarter_net
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (GaussianProposal.goeMatrix sigma z)) N hN hcover u hu.le hbil
    rw [Matrix.l2_opNorm_toEuclideanCLM] at hbound
    exact (not_lt_of_ge hbound) hz
  calc
    μ.real {z | 2 * u < ‖GaussianProposal.goeMatrix sigma z‖}
        ≤ μ.real (⋃ x ∈ N, ⋃ y ∈ N, E x y) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ x ∈ N, ∑ y ∈ N, μ.real (E x y) := by
      apply (measureReal_biUnion_finset_le N _).trans
      exact Finset.sum_le_sum (fun x _ => measureReal_biUnion_finset_le N _)
    _ ≤ ∑ _x ∈ N, ∑ _y ∈ N, 2 * Real.exp (-(n : ℝ) * u ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact sk_goeBilinear_unit_ball_tail hn x y (hN x hx) (hN y hy) u hu
    _ = 2 * (N.card : ℝ) ^ 2 * Real.exp (-(n : ℝ) * u ^ 2 / 4) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (9 : ℝ) ^ (2 * n) * Real.exp (-(n : ℝ) * u ^ 2 / 4) := by
      have hsq : (N.card : ℝ) ^ 2 ≤ ((9 : ℝ) ^ n) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
      rw [← pow_mul, mul_comm n 2] at hsq
      gcongr

theorem skDisorderLaw_operator_norm_twelve_tail {n : ℕ} (hn : 0 < n) :
    (skDisorderLaw n).real {W | (12 : ℝ) < ‖W‖} ≤ 2 * Real.exp (-(n : ℝ)) := by
  have h := sk_goe_operator_norm_tail hn 6 (by norm_num)
  have h9 : (9 : ℝ) ≤ Real.exp 4 := by
    have he : (3 : ℝ) ≤ Real.exp 2 := by
      have h := Real.add_one_le_exp 2
      norm_num at h
      exact h
    have he2 := mul_le_mul he he (by norm_num) (Real.exp_pos 2).le
    calc
      (9 : ℝ) = 3 * 3 := by norm_num
      _ ≤ Real.exp 2 * Real.exp 2 := he2
      _ = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  have hpow : (9 : ℝ) ^ (2 * n) ≤ Real.exp ((2 * n : ℕ) * 4) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) h9 _
  have he : 2 * (9 : ℝ) ^ (2 * n) * Real.exp (-(n : ℝ) * (6 : ℝ) ^ 2 / 4) ≤
      2 * Real.exp (-(n : ℝ)) := by
    calc
      _ ≤ 2 * Real.exp ((2 * n : ℕ) * 4) * Real.exp (-(n : ℝ) * (6 : ℝ) ^ 2 / 4) := by
        gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
  have hmap : (skDisorderLaw n).real {W | (12 : ℝ) < ‖W‖} =
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
        {z | (12 : ℝ) < ‖GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z‖} := by
    unfold skDisorderLaw
    simp only [measureReal_def]
    rw [Measure.map_apply (continuous_goeMatrix _).measurable
      (measurableSet_lt measurable_const measurable_norm)]
    rfl
  rw [hmap]
  have he6 : (6 : ℝ) ^ 2 = 36 := by norm_num
  rw [he6] at h he
  have he12 : (2 : ℝ) * 6 = 12 := by norm_num
  rw [he12] at h
  exact h.trans he

theorem skDisorderLaw_operator_norm_twelve_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (skDisorderLaw n).real {W | (12 : ℝ) < ‖W‖})
      Filter.atTop (𝓝 0) := by
  have hzero : (skDisorderLaw 0).real {W | (12 : ℝ) < ‖W‖} = 0 := by
    have hs : {W : Matrix (Fin 0) (Fin 0) ℝ | (12 : ℝ) < ‖W‖} = ∅ := by
      ext W
      have hW : W = 0 := Subsingleton.elim _ _
      simp [hW]
    rw [hs]
    simp
  have hupper : ∀ n : ℕ, (skDisorderLaw n).real {W | (12 : ℝ) < ‖W‖} ≤
      2 * Real.exp (-(n : ℝ)) := by
    intro n
    cases n with
    | zero => rw [hzero]; positivity
    | succ n => exact skDisorderLaw_operator_norm_twelve_tail (Nat.succ_pos _)
  apply squeeze_zero (fun _ => measureReal_nonneg) hupper
  simpa only [mul_zero, Function.comp_def] using
    (Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
      tendsto_natCast_atTop_atTop)).const_mul 2

end SKConstants
