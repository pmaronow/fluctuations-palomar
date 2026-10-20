module

public import SKBarriers2.Corner.FrozenCoef4

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem gaussian_integral_centered_fifth (m z : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - z) ^ 5 ∂gaussianReal m v) =
      (m - z) ^ 5 + 10 * (m - z) ^ 3 * (v : ℝ) + 15 * (m - z) * (v : ℝ) ^ 2 := by
  have hs : Real.sqrt (v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [gaussian_integral_centered_pow, gaussian_integral_affine_fifth,
    Real.sq_sqrt (NNReal.coe_nonneg v), hs]

theorem gaussian_integral_centered_sixth (m z : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - z) ^ 6 ∂gaussianReal m v) =
      (m - z) ^ 6 + 15 * (m - z) ^ 4 * (v : ℝ) +
        45 * (m - z) ^ 2 * (v : ℝ) ^ 2 + 15 * (v : ℝ) ^ 3 := by
  have hs (n : ℕ) : Real.sqrt (v : ℝ) ^ (2 * n) = (v : ℝ) ^ n := by
    rw [pow_mul, Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [gaussian_integral_centered_pow, gaussian_integral_affine_sixth,
    Real.sq_sqrt (NNReal.coe_nonneg v), hs 2, hs 3]

def gaussianResidualPolynomial (d v w g₄ g₅ g₆ : ℝ) : ℝ :=
  w / 6 * (d ^ 3 + 3 * d * v) +
    g₄ / 24 * (d ^ 4 + 6 * d ^ 2 * v + 3 * v ^ 2) +
    g₅ / 120 * (d ^ 5 + 10 * d ^ 3 * v + 15 * d * v ^ 2) +
    g₆ / 720 * (d ^ 6 + 15 * d ^ 4 * v + 45 * d ^ 2 * v ^ 2 + 15 * v ^ 3)

private theorem centered_pow_integrable (n : ℕ) (m z : ℝ) (v : ℝ≥0) :
    Integrable (fun y : ℝ => (y - z) ^ n) (gaussianReal m v) := by
  have hid : HasExpGrowth (fun y : ℝ => y) :=
    HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  exact ((hid.sub_real (HasExpGrowth.const z)).pow n).integrable_gaussianMeasure (by fun_prop)

theorem quadraticFirst_terminalTaylorResidual_six (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ)
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q) (x : Vec3) :
    quadraticFirst l Q (terminalTaylorResidual β α s h z 6) x =
      ∑ i : Fin 3, gaussianResidualPolynomial (gaussianPathMean l Q x i - z)
        (gaussianPathCovariance l Q i i) (jet β α 3 (s + 4 * h) z)
        (jet β α 4 (s + 4 * h) z) (jet β α 5 (s + 4 * h) z)
        (jet β α 6 (s + 4 * h) z) := by
  let w := jet β α 3 (s + 4 * h) z
  let g₄ := jet β α 4 (s + 4 * h) z
  let g₅ := jet β α 5 (s + 4 * h) z
  let g₆ := jet β α 6 (s + 4 * h) z
  let φ : ℝ → ℝ := fun y => w / 6 * (y - z) ^ 3 + g₄ / 24 * (y - z) ^ 4 +
    g₅ / 120 * (y - z) ^ 5 + g₆ / 720 * (y - z) ^ 6
  have he : terminalTaylorResidual β α s h z 6 = fun y => ∑ i : Fin 3, φ (y i) := by
    funext y
    rw [terminalTaylorResidual, terminalTaylorQuadratic_value, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [scalarTaylorPolynomial, Finset.sum_range_succ,
      Finset.sum_range_zero, jet, iteratedDeriv_zero, Nat.factorial, Nat.cast_mul,
      Nat.cast_one, φ, w, g₄, g₅, g₆]
    ring
  have hi (m : ℝ) (v : ℝ≥0) : Integrable φ (gaussianReal m v) := by
    exact ((((centered_pow_integrable 3 m z v).const_mul (w / 6)).add
      ((centered_pow_integrable 4 m z v).const_mul (g₄ / 24))).add
      ((centered_pow_integrable 5 m z v).const_mul (g₅ / 120))).add
      ((centered_pow_integrable 6 m z v).const_mul (g₆ / 720))
  rw [he, quadraticFirst_separable l Q hl φ (by fun_prop) hi x]
  apply Finset.sum_congr rfl
  intro i _
  let m := gaussianPathMean l Q x i
  let v := Real.toNNReal (gaussianPathCovariance l Q i i)
  have hv : (v : ℝ) = gaussianPathCovariance l Q i i := by
    apply Real.coe_toNNReal
    simpa [gaussianPathVariance, Pi.single_apply] using
      gaussianPathVariance_nonneg l Q hl (Pi.single i 1)
  change (∫ y, φ y ∂gaussianReal m v) = _
  simp only [φ]
  have hi₃ := (centered_pow_integrable 3 m z v).const_mul (w / 6)
  have hi₄ := (centered_pow_integrable 4 m z v).const_mul (g₄ / 24)
  have hi₅ := (centered_pow_integrable 5 m z v).const_mul (g₅ / 120)
  have hi₆ := (centered_pow_integrable 6 m z v).const_mul (g₆ / 720)
  have ha := integral_add ((hi₃.add hi₄).add hi₅) hi₆
  have hb := integral_add (hi₃.add hi₄) hi₅
  have hc := integral_add hi₃ hi₄
  simp only [Pi.add_apply] at ha hb hc
  rw [ha, hb, hc]
  simp only [integral_const_mul]
  rw [gaussian_integral_centered_cube, gaussian_integral_centered_fourth,
    gaussian_integral_centered_fifth, gaussian_integral_centered_sixth, hv]
  rfl

def gaussianTaylorVarianceRemainder (h D L E g₄ g₅ g₆ : ℝ) : ℝ :=
  g₄ / 4 * D ^ 2 * E + g₄ / 8 * E ^ 2 +
    h * g₅ / 12 * D ^ 3 * E + g₅ / 8 * D * (2 * L * E + h * E ^ 2) +
    h ^ 2 * g₆ / 48 * D ^ 4 * E +
    h * g₆ / 16 * D ^ 2 * (2 * L * E + h * E ^ 2) +
    g₆ / 48 * (3 * L ^ 2 * E + 3 * h * L * E ^ 2 + h ^ 2 * E ^ 3)

theorem gaussianResidualPolynomial_variance_change (h D L E w g₄ g₅ g₆ : ℝ) :
    gaussianResidualPolynomial (h * D) (h * L + h ^ 2 * E) w g₄ g₅ g₆ -
        gaussianResidualPolynomial (h * D) (h * L) w g₄ g₅ g₆ =
      h ^ 3 * (w / 2 * D + g₄ / 4 * L) * E +
        h ^ 4 * gaussianTaylorVarianceRemainder h D L E g₄ g₅ g₆ := by
  unfold gaussianResidualPolynomial gaussianTaylorVarianceRemainder
  ring

def firstTaylorCoordinateRemainder (h a b χ w g₄ g₅ g₆ D Q R : ℝ) : ℝ :=
  (w / 2 * D + g₄ * b) * a ^ 2 * b ^ 3 * χ ^ 2 * R +
    2 * a ^ 2 * b ^ 3 * χ ^ 2 * w * D * Q +
    gaussianTaylorVarianceRemainder h D (4 * b)
      (a * b ^ 2 * χ * Q + h * a ^ 2 * b ^ 3 * χ ^ 2 * R) g₄ g₅ g₆

theorem gaussianResidualPolynomial_path_expansion (h a b u χ w g₄ g₅ g₆ D Q R : ℝ)
    (hD : D = 4 * a * b * u + 4 * a * b * χ * h * D) :
    gaussianResidualPolynomial (h * D)
        (h * (4 * b) + h ^ 2 * (a * b ^ 2 * χ * Q + h * a ^ 2 * b ^ 3 * χ ^ 2 * R))
        w g₄ g₅ g₆ - gaussianResidualPolynomial (h * D) (h * (4 * b)) w g₄ g₅ g₆ =
      h ^ 3 * (a * b ^ 3 * χ * (g₄ + 2 * a * u * w)) * Q +
        h ^ 4 * firstTaylorCoordinateRemainder h a b χ w g₄ g₅ g₆ D Q R := by
  rw [gaussianResidualPolynomial_variance_change]
  unfold firstTaylorCoordinateRemainder
  linear_combination (h ^ 3 * w / 2 * a * b ^ 2 * χ * Q) * hD

def frozenFirstTaylorRemainder (h a b u χ w g₄ g₅ g₆ t k : ℝ) : ℝ :=
  ∑ i : Fin 3, firstTaylorCoordinateRemainder h a b χ w g₄ g₅ g₆
    (4 * a * b * u / (1 - 4 * t)) (frozenCovarianceQuadratic k i i)
    (frozenCovarianceRemainder t k i i)

theorem frozenFirstTaylorMoment_difference (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hden : 1 - 4 * a * β ^ 2 * jet β α 2 (s + 4 * h) z * h ≠ 0)
    (hQk : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hQ₀ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)) :
    let u := jet β α 1 (s + 4 * h) z
    let χ := jet β α 2 (s + 4 * h) z
    let w := jet β α 3 (s + 4 * h) z
    let g₄ := jet β α 4 (s + 4 * h) z
    let g₅ := jet β α 5 (s + 4 * h) z
    let g₆ := jet β α 6 (s + 4 * h) z
    (quadraticFirst (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
        (terminalTaylorResidual β α s h z 6) (fun _ => z) -
      quadraticFirst (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)
        (terminalTaylorResidual β α s h z 6) (fun _ => z)) -
      firstMomentRow k h a (β ^ 2) u χ w g₄ =
      h ^ 4 * (frozenFirstTaylorRemainder h a (β ^ 2) u χ w g₄ g₅ g₆ (a * β ^ 2 * χ * h) k -
        frozenFirstTaylorRemainder h a (β ^ 2) u χ w g₄ g₅ g₆ (a * β ^ 2 * χ * h) 0) := by
  dsimp only
  let u := jet β α 1 (s + 4 * h) z
  let χ := jet β α 2 (s + 4 * h) z
  let w := jet β α 3 (s + 4 * h) z
  let g₄ := jet β α 4 (s + 4 * h) z
  let g₅ := jet β α 5 (s + 4 * h) z
  let g₆ := jet β α 6 (s + 4 * h) z
  let D := 4 * a * β ^ 2 * u / (1 - 4 * a * β ^ 2 * χ * h)
  have hD : D = 4 * a * β ^ 2 * u + 4 * a * β ^ 2 * χ * h * D := by
    dsimp only [D]
    change 1 - 4 * a * β ^ 2 * χ * h ≠ 0 at hden
    field_simp [hden]
    ring
  have H (k' : ℝ) (hk' : |k'| ≤ 1 / 2)
      (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k') (terminalTaylorQuadratic β α s h z)) :
      quadraticFirst (frozenSchedule β a (1 / 2) h k') (terminalTaylorQuadratic β α s h z)
          (terminalTaylorResidual β α s h z 6) (fun _ => z) -
        3 * gaussianResidualPolynomial (h * D) (h * (4 * β ^ 2)) w g₄ g₅ g₆ =
        h ^ 3 * (a * (β ^ 2) ^ 3 * χ * (g₄ + 2 * a * u * w)) *
          matrixTrace (frozenCovarianceQuadratic k') +
        h ^ 4 * frozenFirstTaylorRemainder h a (β ^ 2) u χ w g₄ g₅ g₆ (a * β ^ 2 * χ * h) k' := by
    have hm (i : Fin 3) : gaussianPathMean (frozenSchedule β a (1 / 2) h k')
        (terminalTaylorQuadratic β α s h z) (fun _ => z) i - z = h * D := by
      unfold terminalTaylorQuadratic at hQ ⊢
      rw [frozenSchedule_pathMean β a h k' _ _ _ z hh hk' hQ i]
      dsimp only [D, u, χ]
      ring
    have hv (i : Fin 3) : gaussianPathCovariance (frozenSchedule β a (1 / 2) h k')
        (terminalTaylorQuadratic β α s h z) i i =
        h * (4 * β ^ 2) + h ^ 2 * (a * (β ^ 2) ^ 2 * χ * frozenCovarianceQuadratic k' i i +
          h * a ^ 2 * (β ^ 2) ^ 3 * χ ^ 2 * frozenCovarianceRemainder (a * β ^ 2 * χ * h) k' i i) := by
      have HV := frozenSchedule_pathVariance_expansion β a h k' _ _ _ z ha hh hk' hQ i
      change gaussianPathCovariance _ (terminalTaylorQuadratic β α s h z) i i = _ at HV
      rw [HV]
      dsimp only [χ]
      ring
    rw [quadraticFirst_terminalTaylorResidual_six β α s h z _ _ hQ]
    simp_rw [hm, hv]
    have hp (i : Fin 3) := gaussianResidualPolynomial_path_expansion h a (β ^ 2) u χ w g₄ g₅ g₆ D
      (frozenCovarianceQuadratic k' i i) (frozenCovarianceRemainder (a * β ^ 2 * χ * h) k' i i) hD
    simp only [frozenFirstTaylorRemainder, matrixTrace, Fin.sum_univ_succ,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    dsimp only [D, w, g₄, g₅, g₆] at hp ⊢
    simp only [mul_assoc] at hp ⊢
    linear_combination hp 0 + hp 1 + hp 2
  have Hk := H k hk hQk
  have H₀ := H 0 (by norm_num) hQ₀
  have HT := frozenCovarianceQuadratic_trace_difference k
  change _ - firstMomentRow k h a (β ^ 2) u χ w g₄ = _
  unfold firstMomentRow
  linear_combination Hk - H₀ + (h ^ 3 * (a * (β ^ 2) ^ 3 * χ * (g₄ + 2 * a * u * w))) * HT

def firstTaylorParameterRemainder (x : (Fin 10 → ℝ) × ℝ) : ℝ :=
  frozenFirstTaylorRemainder (x.1 0) (x.1 1) (x.1 2) (x.1 3) (x.1 4)
    (x.1 5) (x.1 6) (x.1 7) (x.1 8) (x.1 9) x.2

private def parameterTiltDerivative (F : (Fin 10 → ℝ) × ℝ → ℝ)
    (x : (Fin 10 → ℝ) × ℝ) : ℝ := fderiv ℝ F x (0, 1)

private theorem compact_parameter_evenSecondControl
    {F : (Fin 10 → ℝ) × ℝ → ℝ} {U : Set ((Fin 10 → ℝ) × ℝ)}
    {K : Set (Fin 10 → ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hK : IsCompact K) (hKU : K ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ U)
    (he : ∀ p ∈ K, ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2), F (p, -k) = F (p, k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, EvenSecondControl (fun k => F (p, k)) (1 / 2) C 0 := by
  have hF₁ : ContDiffOn ℝ ∞ (parameterTiltDerivative F) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hF₂ : ContDiffOn ℝ ∞ (parameterTiltDerivative (parameterTiltDerivative F)) U :=
    (hF₁.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  obtain ⟨B, hB⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hF₂.continuousOn.mono hKU)
  refine ⟨1 + |B|, by positivity, ?_⟩
  intro p hp
  refine ⟨fun k => parameterTiltDerivative F (p, k),
    fun k => parameterTiltDerivative (parameterTiltDerivative F) (p, k), ?_, ?_, he p hp⟩
  · intro k hk
    have hx := hKU (show (p, k) ∈ K ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) from ⟨hp, hk⟩)
    have hline : HasDerivAt (fun t : ℝ => (p, t)) (0, 1) k :=
      (hasDerivAt_const k p).prodMk (hasDerivAt_id k)
    exact ⟨((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hline,
      ((hF₁.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hline⟩
  · intro k hk
    have HB : |parameterTiltDerivative (parameterTiltDerivative F) (p, k)| ≤ B :=
      hB (p, k) ⟨hp, hk⟩
    simp only [zero_mul, add_zero]
    linarith [le_abs_self B]

def firstTaylorParameterDomain : Set ((Fin 10 → ℝ) × ℝ) :=
  {x | (x.1 9, x.2) ∈ frozenResolventDomain ∧ 1 - 4 * x.1 9 ≠ 0}

theorem firstTaylorParameterDomain_isOpen : IsOpen firstTaylorParameterDomain := by
  exact (frozenResolventDomain_isOpen.preimage (by fun_prop)).inter
    (isOpen_ne_fun (by fun_prop) continuous_const)

private theorem firstTaylorCoordinateRemainder_contDiff :
    ContDiff ℝ ∞ (fun p : Fin 11 → ℝ => firstTaylorCoordinateRemainder
      (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8) (p 9) (p 10)) := by
  unfold firstTaylorCoordinateRemainder gaussianTaylorVarianceRemainder
  fun_prop

theorem firstTaylorParameterRemainder_contDiffOn :
    ContDiffOn ℝ ∞ firstTaylorParameterRemainder firstTaylorParameterDomain := by
  have hp (i : Fin 10) : ContDiff ℝ ∞ (fun x : (Fin 10 → ℝ) × ℝ => x.1 i) := by
    fun_prop
  have hm : ContDiff ℝ ∞ (fun x : (Fin 10 → ℝ) × ℝ => (x.1 9, x.2)) := by
    fun_prop
  have hn : ContDiff ℝ ∞ (fun x : (Fin 10 → ℝ) × ℝ => ((0 : ℝ), x.2)) := by
    fun_prop
  have hQ (i : Fin 3) : ContDiffOn ℝ ∞
      (fun x : (Fin 10 → ℝ) × ℝ => frozenCovarianceQuadratic x.2 i i)
      firstTaylorParameterDomain := by
    have H := (frozenCovarianceQuadratic_entry_contDiff i i).comp hn
    simpa only [Function.comp_def] using H.contDiffOn (s := firstTaylorParameterDomain)
  have hR (i : Fin 3) : ContDiffOn ℝ ∞
      (fun x : (Fin 10 → ℝ) × ℝ => frozenCovarianceRemainder (x.1 9) x.2 i i)
      firstTaylorParameterDomain := by
    have H := (frozenCovarianceRemainder_entry_contDiffOn i i).comp
      (hm.contDiffOn (s := firstTaylorParameterDomain))
      (show MapsTo (fun x : (Fin 10 → ℝ) × ℝ => (x.1 9, x.2))
        firstTaylorParameterDomain frozenResolventDomain from fun _ hx => hx.1)
    simpa only [Function.comp_def] using H
  have hD : ContDiffOn ℝ ∞
      (fun x : (Fin 10 → ℝ) × ℝ => 4 * x.1 1 * x.1 2 * x.1 3 / (1 - 4 * x.1 9))
      firstTaylorParameterDomain := by
    exact (((contDiffOn_const.mul (hp 1).contDiffOn).mul (hp 2).contDiffOn).mul
      (hp 3).contDiffOn).div (contDiffOn_const.sub (contDiffOn_const.mul (hp 9).contDiffOn))
        (fun _ hx => hx.2)
  unfold firstTaylorParameterRemainder frozenFirstTaylorRemainder
  apply ContDiffOn.sum
  intro i _
  let v : ((Fin 10 → ℝ) × ℝ) → (Fin 11 → ℝ) := fun x =>
    ![x.1 0, x.1 1, x.1 2, x.1 4, x.1 5, x.1 6, x.1 7, x.1 8,
      4 * x.1 1 * x.1 2 * x.1 3 / (1 - 4 * x.1 9),
      frozenCovarianceQuadratic x.2 i i, frozenCovarianceRemainder (x.1 9) x.2 i i]
  have hv : ContDiffOn ℝ ∞ v firstTaylorParameterDomain := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact (hp 0).contDiffOn
    · exact (hp 1).contDiffOn
    · exact (hp 2).contDiffOn
    · exact (hp 4).contDiffOn
    · exact (hp 5).contDiffOn
    · exact (hp 6).contDiffOn
    · exact (hp 7).contDiffOn
    · exact (hp 8).contDiffOn
    · exact hD
    · exact hQ i
    · exact hR i
  have H := firstTaylorCoordinateRemainder_contDiff.comp_contDiffOn hv
  simpa only [Function.comp_def, v, Matrix.cons_val] using H

theorem frozenFirstTaylorRemainder_even (h a b u χ w g₄ g₅ g₆ t k : ℝ) :
    frozenFirstTaylorRemainder h a b u χ w g₄ g₅ g₆ t (-k) =
      frozenFirstTaylorRemainder h a b u χ w g₄ g₅ g₆ t k := by
  unfold frozenFirstTaylorRemainder
  rw [frozenCovarianceQuadratic_neg, frozenCovarianceRemainder_neg]
  simp only [Matrix.submatrix_apply]
  exact Equiv.sum_comp frozenTiltSwap (fun i : Fin 3 =>
    firstTaylorCoordinateRemainder h a b χ w g₄ g₅ g₆ (4 * a * b * u / (1 - 4 * t))
      (frozenCovarianceQuadratic k i i) (frozenCovarianceRemainder t k i i))

theorem firstTaylorParameterRemainder_uniform_control (M : ℝ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ 1 / 8 ∧
      ∀ p : Fin 10 → ℝ, (∀ i, |p i| ≤ M) → |p 9| ≤ δ →
        EvenSecondControl (fun k => firstTaylorParameterRemainder (p, k)) (1 / 2) C 0 := by
  obtain ⟨δ₀, hδ₀, _, hrect⟩ := frozenResolventDomain_contains_rectangle
  let δ := min δ₀ (1 / 8)
  let K : Set (Fin 10 → ℝ) :=
    (Set.pi Set.univ (fun _ => Icc (-M) M)) ∩ {p | p 9 ∈ Icc (-δ) δ}
  have hK : IsCompact K :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
      (isClosed_Icc.preimage (by fun_prop))
  have hKU : K ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ firstTaylorParameterDomain := by
    rintro ⟨p, k⟩ ⟨hp, hk⟩
    have ht : p 9 ∈ Icc (-δ₀) δ₀ :=
      ⟨(neg_le_neg (min_le_left _ _)).trans hp.2.1, hp.2.2.trans (min_le_left _ _)⟩
    refine ⟨hrect ⟨ht, hk⟩, ?_⟩
    have H : p 9 ≤ 1 / 8 := hp.2.2.trans (min_le_right _ _)
    linarith
  obtain ⟨C, hC, H⟩ := compact_parameter_evenSecondControl firstTaylorParameterDomain_isOpen
    firstTaylorParameterRemainder_contDiffOn hK hKU (fun p _ k _ =>
      frozenFirstTaylorRemainder_even _ _ _ _ _ _ _ _ _ _ k)
  refine ⟨C, δ, hC, lt_min hδ₀ (by norm_num), min_le_right _ _, ?_⟩
  intro p hp ht
  exact H p ⟨fun i _ => abs_le.mp (hp i), abs_le.mp ht⟩

theorem firstTaylorCoefficientError_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      (∀ j ∈ Icc (1 : ℕ) 6, |jet β α j (s + 4 * h) z| ≤ B) →
      EvenSecondControl (firstTaylorCoefficientError β α a s h z) (1 / 4) (C * h ^ 4) 0 := by
  let M := β ^ 2 + B + 2
  obtain ⟨C, δ, hC, hδ, hδ₈, H⟩ := firstTaylorParameterRemainder_uniform_control M
  obtain ⟨η, hη, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  let T := (β ^ 2 + 1) * (B + 1)
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨C, min (min η 1) (δ / T), hC, by positivity, ?_⟩
  intro α a s h z ha hh hh₀ hj
  let u := jet β α 1 (s + 4 * h) z
  let χ := jet β α 2 (s + 4 * h) z
  let w := jet β α 3 (s + 4 * h) z
  let g₄ := jet β α 4 (s + 4 * h) z
  let g₅ := jet β α 5 (s + 4 * h) z
  let g₆ := jet β α 6 (s + 4 * h) z
  let t := a * β ^ 2 * χ * h
  let p : Fin 10 → ℝ := ![h, a, β ^ 2, u, χ, w, g₄, g₅, g₆, t]
  have hhη : h ≤ η := (hh₀.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hh₁ : h ≤ 1 := (hh₀.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hχ : |χ| ≤ B := hj 2 (by norm_num)
  have ht : |t| ≤ δ := by
    have hta : |t| ≤ T * h := by
      dsimp only [t, T]
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos ha.1,
        abs_of_nonneg (sq_nonneg β), abs_of_nonneg hh]
      calc
        _ ≤ 1 * (β ^ 2 + 1) * (B + 1) * h := by gcongr <;> linarith [ha.2, hχ]
        _ = _ := by ring
    exact hta.trans (by simpa only [mul_comm] using
      (le_div_iff₀ hT).mp (hh₀.trans (min_le_right _ _)))
  have hBM : B ≤ M := by dsimp only [M]; nlinarith [sq_nonneg β]
  have h₁M : 1 ≤ M := by dsimp only [M]; nlinarith [sq_nonneg β]
  have hp : ∀ i, |p i| ≤ M := by
    intro i
    fin_cases i
    · change |h| ≤ M
      rw [abs_of_nonneg hh]
      exact hh₁.trans h₁M
    · change |a| ≤ M
      rw [abs_of_pos ha.1]
      exact ha.2.trans h₁M
    · change |β ^ 2| ≤ M
      rw [abs_of_nonneg (sq_nonneg β)]
      dsimp only [M]
      linarith
    · exact (hj 1 (by norm_num)).trans hBM
    · exact hχ.trans hBM
    · exact (hj 3 (by norm_num)).trans hBM
    · exact (hj 4 (by norm_num)).trans hBM
    · exact (hj 5 (by norm_num)).trans hBM
    · exact (hj 6 (by norm_num)).trans hBM
    · exact ht.trans (hδ₈.trans ((by norm_num : (1 / 8 : ℝ) ≤ 1).trans h₁M))
  have HG := H p hp ht
  have HE : EvenSecondControl
      (fun k => h ^ 4 * (firstTaylorParameterRemainder (p, k) - firstTaylorParameterRemainder (p, 0)))
      (1 / 2) (C * h ^ 4) 0 := by
    convert (HG.sub_const (firstTaylorParameterRemainder (p, 0))).const_mul (h ^ 4) using 1
    · rw [abs_of_nonneg (pow_nonneg hh 4)]
      ring
    · ring
  have ht₈ : t ≤ 1 / 8 := (le_abs_self t).trans (ht.trans hδ₈)
  have hden : 1 - 4 * a * β ^ 2 * χ * h ≠ 0 := by
    dsimp only [t] at ht₈
    nlinarith
  refine HE.transfer (by norm_num) ?_
  intro k hk
  exact frozenFirstTaylorMoment_difference β α a s h k z (ne_of_gt ha.1) hh (abs_le.mpr hk) hden
    (hA α a s h k z ha hh hhη (abs_le.mpr hk) hχ)
    (hA α a s h 0 z ha hh hhη (by norm_num) hχ)

theorem EvenSecondControl.congr_on_open {f g : ℝ → ℝ} {κ A B : ℝ} {U : Set ℝ}
    (H : EvenSecondControl g κ A B) (hU : IsOpen U) (hsub : Icc (-κ) κ ⊆ U)
    (he : EqOn f g U) : EvenSecondControl f κ A B := by
  rcases H with ⟨g₁, g₂, hd, hb, hg⟩
  refine ⟨g₁, g₂, ?_, hb, ?_⟩
  · intro k hk
    have hn : f =ᶠ[𝓝 k] g := by
      filter_upwards [hU.mem_nhds (hsub hk)] with x hx
      exact he hx
    exact ⟨(hd k hk).1.congr_of_eventuallyEq hn, (hd k hk).2⟩
  · intro k hk
    have hneg : -k ∈ Icc (-κ) κ := ⟨by linarith [hk.2], by linarith [hk.1]⟩
    rw [he (hsub hneg), he (hsub hk)]
    exact hg k hk

theorem scalarData_firstTaylorCoefficientError_control {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      EvenSecondControl
        (firstTaylorCoefficientError β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
        (1 / 4) (C * h ^ 4) 0 := by
  let B := scalarTerminalJetBound D 6 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 6]
  obtain ⟨C, η, hC, hη, H⟩ := firstTaylorCoefficientError_uniform_control β B hB
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  let v := min (l / 2) T
  have hv : 0 < v := lt_min (by positivity) hT
  refine ⟨C, min η (min (l / 2) ((D.q - u) / 3)), hC, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have hhη : h ≤ η := hh₀.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 3 := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : v ≤ r - h := (min_le_left _ _).trans (by linarith [hr.1])
  have ha : cdf (D.μ : Measure ℝ) (r - h) ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨?_, cdf_le_one _ _⟩
    exact (mul_pos hc hv).trans_le ((hlin v ⟨hv.le, min_le_right _ _⟩).trans
      ((cdf (D.μ : Measure ℝ)).mono hs))
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  apply H _ _ (r - h) h z ha hh.le hhη
  intro j hj
  exact (scalarData_jet_le D hj.1 hj.2 ht z).trans (by dsimp only [B]; linarith)

theorem scalarData_firstCoefficientError_control {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      EvenSecondControl
        (firstCoefficientError β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z)
        (1 / 4) (C * Real.sqrt h * h ^ 3) (C * h ^ 3) := by
  obtain ⟨C₁, η, hC₁, hη, HP⟩ := scalarData_firstTaylorCoefficientError_control D hl hu
  obtain ⟨C₂, ζ, hC₂, hζ, HT⟩ := scalarData_sixthTailDifference_control D hl hu
  let B := scalarTerminalJetBound D 7 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 7]
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  let v := min (l / 2) T
  have hv : 0 < v := lt_min (by positivity) hT
  refine ⟨C₁ + C₂, min η (min ζ (min ξ (min 1 (min (l / 2) ((D.q - u) / 3))))),
    add_pos hC₁ hC₂, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have hhη : h ≤ η := hh₀.trans (min_le_left _ _)
  have hhrest := hh₀.trans (min_le_right _ _)
  have hhζ : h ≤ ζ := hhrest.trans (min_le_left _ _)
  have hhrest' := hhrest.trans (min_le_right _ _)
  have hhξ : h ≤ ξ := hhrest'.trans (min_le_left _ _)
  have hhrest'' := hhrest'.trans (min_le_right _ _)
  have hh₁ : h ≤ 1 := hhrest''.trans (min_le_left _ _)
  have hhrange := hhrest''.trans (min_le_right _ _)
  have hhl : h ≤ l / 2 := hhrange.trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 3 := hhrange.trans (min_le_right _ _)
  have hs : v ≤ r - h := (min_le_left _ _).trans (by linarith [hr.1])
  have ha : cdf (D.μ : Measure ℝ) (r - h) ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨?_, cdf_le_one _ _⟩
    exact (mul_pos hc hv).trans_le ((hlin v ⟨hv.le, min_le_right _ _⟩).trans
      ((cdf (D.μ : Measure ℝ)).mono hs))
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  have hj (j : ℕ) (hj₁ : 1 ≤ j) (hj₇ : j ≤ 7) (y : ℝ) :
      |jet β (cdf (D.μ : Measure ℝ)) j ((r - h) + 4 * h) y| ≤ B :=
    (scalarData_jet_le D hj₁ hj₇ ht y).trans (by dsimp only [B]; linarith)
  have Hsum := ((HP r hr h hh hhη z).fourth_order hC₁.le hh.le hh₁).add
    (HT r hr h hh hhζ z)
  have HC : EvenSecondControl
      (fun k => firstTaylorCoefficientError β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z k +
        (frozenSixthTailMoment β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z k -
          frozenSixthTailMoment β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z 0))
      (1 / 4) ((C₁ + C₂) * Real.sqrt h * h ^ 3) ((C₁ + C₂) * h ^ 3) := by
    apply Hsum.mono
    · exact le_of_eq (by ring)
    · nlinarith [mul_nonneg hC₂.le (pow_nonneg hh.le 3)]
  apply HC.congr_on_open isOpen_Ioo
    (show Icc (-(1 / 4) : ℝ) (1 / 4) ⊆ Ioo (-(1 / 2) : ℝ) (1 / 2) from
      fun _ hk => ⟨by linarith [hk.1], by linarith [hk.2]⟩)
  intro k hk
  have hQ (x : ℝ) (hx : |x| ≤ 1 / 2) :=
    hA _ _ (r - h) h x z ha hh.le hhξ hx (hj 2 (by norm_num) (by norm_num) z)
  exact firstCoefficientError_split β _ _ (r - h) h z k B
    (hQ k (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)) (hQ 0 (by norm_num))
    (scalarData_phi_regular D ht) (scalarData_phi_contDiff D ht) hB.le
    (hj 7 (by norm_num) le_rfl)

theorem quadraticVariance_add (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (F G : Vec3 → ℝ)
    (hF : MemLp (fun t => F (x + t • v)) 2
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)))
    (hG : MemLp (fun t => G (x + t • v)) 2
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x))) :
    quadraticVariance Q m v (fun y => F y + G y) x =
      quadraticVariance Q m v F x +
        2 * covariance (fun t => F (x + t • v)) (fun t => G (x + t • v))
          (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) +
        quadraticVariance Q m v G x := by
  let : IsProbabilityMeasure (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
    unfold quadraticGaussian
    infer_instance
  rw [quadraticVariance_eq_variance Q m v x _ (hF.add hG),
    quadraticVariance_eq_variance Q m v x F hF,
    quadraticVariance_eq_variance Q m v x G hG, variance_fun_add hF hG]

private theorem covariance_sq_le_variance_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ ^ 2 ≤ variance X μ * variance Y μ := by
  have H (t : ℝ) : 0 ≤ variance Y μ * (t * t) + (-2 * covariance X Y μ) * t + variance X μ := by
    have HV := variance_nonneg (fun sample => X sample - t * Y sample) μ
    rw [variance_fun_sub hX (hY.const_mul t), variance_const_mul, covariance_const_mul_right] at HV
    nlinarith
  have HD := discrim_le_zero H
  unfold discrim at HD
  nlinarith

theorem variance_cubic_tail_error_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ} {C h : ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hC : 0 ≤ C)
    (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hVX : variance X μ ≤ C * h ^ 3) (hVY : variance Y μ ≤ C * h ^ 4) :
    |variance (fun sample => X sample + Y sample) μ - variance X μ| ≤ 3 * C * Real.sqrt h * h ^ 3 := by
  have hs : h ≤ Real.sqrt h := by
    have hs₀ := Real.sqrt_nonneg h
    have hs₂ := Real.sq_sqrt hh
    nlinarith [mul_nonneg hh (sub_nonneg.mpr hh₁)]
  have hprod : variance X μ * variance Y μ ≤ (C * h ^ 3) * (C * h ^ 4) :=
    mul_le_mul hVX hVY (variance_nonneg Y μ) (by positivity)
  have he : (C * Real.sqrt h * h ^ 3) ^ 2 = (C * h ^ 3) * (C * h ^ 4) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hh]
    ring
  have hcov : |covariance X Y μ| ≤ C * Real.sqrt h * h ^ 3 := by
    have H := (covariance_sq_le_variance_mul hX hY).trans hprod
    rw [← he, ← sq_abs (covariance X Y μ)] at H
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp H
  have htail : variance Y μ ≤ C * Real.sqrt h * h ^ 3 := by
    have H := mul_le_mul_of_nonneg_left hs (mul_nonneg hC (pow_nonneg hh 3))
    nlinarith
  rw [variance_fun_add hX hY]
  have he' : variance X μ + 2 * covariance X Y μ + variance Y μ - variance X μ =
      2 * covariance X Y μ + variance Y μ := by ring
  rw [he']
  calc
    _ ≤ |2 * covariance X Y μ| + |variance Y μ| := abs_add_le _ _
    _ = 2 * |covariance X Y μ| + variance Y μ := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (variance_nonneg Y μ)]
    _ ≤ _ := by linarith

theorem quadraticVariance_cubic_tail_error_le (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3)
    (F G : Vec3 → ℝ) {C h : ℝ}
    (hF : MemLp (fun t => F (x + t • v)) 2
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)))
    (hG : MemLp (fun t => G (x + t • v)) 2
      (quadraticGaussian (Q.precision m v) (m * Q.slope v x)))
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hVF : quadraticVariance Q m v F x ≤ C * h ^ 3)
    (hG₂ : quadraticAverage Q m v (fun y => G y ^ 2) x ≤ C * h ^ 4) :
    |quadraticVariance Q m v (fun y => F y + G y) x - quadraticVariance Q m v F x| ≤
      3 * C * Real.sqrt h * h ^ 3 := by
  let : IsProbabilityMeasure (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
    unfold quadraticGaussian
    infer_instance
  have hVG : quadraticVariance Q m v G x ≤ C * h ^ 4 := by
    unfold quadraticVariance
    linarith [sq_nonneg (quadraticAverage Q m v G x)]
  rw [quadraticVariance_eq_variance Q m v x F hF] at hVF
  rw [quadraticVariance_eq_variance Q m v x G hG] at hVG
  rw [quadraticVariance_eq_variance Q m v x _ (hF.add hG),
    quadraticVariance_eq_variance Q m v x F hF]
  exact variance_cubic_tail_error_le hF hG hC hh hh₁ hVF hVG

end SKBarriers2.Corner
