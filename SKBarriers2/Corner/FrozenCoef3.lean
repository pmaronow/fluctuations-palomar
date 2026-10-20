module

public import SKBarriers2.Corner.FrozenCoef2

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem gaussian_affine_hasLaw (m C L : ℝ) (v w : ℝ≥0) :
    HasLaw (fun p : ℝ × ℝ => C + L * p.1 + p.2)
      (gaussianReal (L * m + C) (NNReal.mk (L ^ 2) (sq_nonneg L) * v + w))
      ((gaussianReal m v).prod (gaussianReal 0 w)) := by
  let μ := gaussianReal m v
  let ν := gaussianReal 0 w
  have ht : HasLaw Prod.fst μ (μ.prod ν) := measurePreserving_fst.hasLaw
  have hs : HasLaw Prod.snd ν (μ.prod ν) := measurePreserving_snd.hasLaw
  have hX : HasLaw (fun p : ℝ × ℝ => C + L * p.1)
      (gaussianReal (L * m + C) (NNReal.mk (L ^ 2) (sq_nonneg L) * v)) (μ.prod ν) := by
    simpa only [Function.comp_def] using gaussianReal_const_add (gaussianReal_const_mul ht L) C
  have hind : IndepFun (fun p : ℝ × ℝ => C + L * p.1) Prod.snd (μ.prod ν) :=
    indepFun_prod (μ := μ) (ν := ν) (X := fun t : ℝ => C + L * t) (Y := id) (by fun_prop) measurable_id
  have hZ : HasLaw (fun p : ℝ × ℝ => C + L * p.1 + p.2)
      (gaussianReal (L * m + C) (NNReal.mk (L ^ 2) (sq_nonneg L) * v + w)) (μ.prod ν) := by
    refine ⟨by fun_prop, ?_⟩
    change (μ.prod ν).map ((fun p : ℝ × ℝ => C + L * p.1) + Prod.snd) = _
    simpa only [add_zero] using
      gaussianReal_add_gaussianReal_of_indepFun hind hX hs
  exact hZ

theorem gaussian_integral_affine (φ : ℝ → ℝ) (m C L : ℝ) (v w : ℝ≥0)
    (hφ : Integrable φ (gaussianReal (L * m + C) (NNReal.mk (L ^ 2) (sq_nonneg L) * v + w))) :
    (∫ t, ∫ s, φ (C + L * t + s) ∂gaussianReal 0 w ∂gaussianReal m v) =
      ∫ y, φ y ∂gaussianReal (L * m + C) (NNReal.mk (L ^ 2) (sq_nonneg L) * v + w) := by
  have hZ := gaussian_affine_hasLaw m C L v w
  have hi : Integrable (fun p : ℝ × ℝ => φ (C + L * p.1 + p.2))
      ((gaussianReal m v).prod (gaussianReal 0 w)) := hZ.integrable_comp hφ
  rw [← integral_prod _ hi]
  exact hZ.integral_comp hφ.aestronglyMeasurable

theorem gaussian_integral_affine_integrable (φ : ℝ → ℝ) (m C L : ℝ) (v w : ℝ≥0)
    (hφ : Integrable φ (gaussianReal (L * m + C) (NNReal.mk (L ^ 2) (sq_nonneg L) * v + w))) :
    Integrable (fun t => ∫ s, φ (C + L * t + s) ∂gaussianReal 0 w) (gaussianReal m v) :=
  ((gaussian_affine_hasLaw m C L v w).integrable_comp hφ).integral_prod_left

theorem integral_gaussian_shift (φ : ℝ → ℝ) (m : ℝ) (v : ℝ≥0) (hφ : Measurable φ) :
    (∫ y, φ y ∂gaussianReal m v) = ∫ t, φ (m + t) ∂gaussianReal 0 v := by
  have hl : HasLaw (fun x : ℝ => m + x) (gaussianReal m v) (gaussianReal 0 v) := by
    simpa only [zero_add, id_eq] using gaussianReal_const_add (HasLaw.id (μ := gaussianReal 0 v)) m
  exact (hl.integral_comp hφ.aestronglyMeasurable).symm

def gaussianPathVariance (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (w : Vec3) : ℝ :=
  ∑ i, ∑ j, w i * gaussianPathCovariance l Q i j * w j

theorem gaussianPathVariance_cons (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (u : ℝ × Vec3) (w : Vec3) :
    gaussianPathVariance (u :: l) Q w = gaussianPathVariance l Q w +
      ((riccatiRecursion l Q).precision u.1 u.2)⁻¹ * (∑ i, w i * gaussianPathLinear l Q u.2 i) ^ 2 :=
  gaussianPathCovariance_projection l Q u w

theorem gaussianPathVariance_nonneg (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (w : Vec3) : 0 ≤ gaussianPathVariance l Q w := by
  induction l with
  | nil => simp [gaussianPathVariance, gaussianPathCovariance]
  | cons u l ih =>
    rw [gaussianPathVariance_cons]
    exact add_nonneg (ih hl.1) (mul_nonneg (inv_nonneg.mpr hl.2.2.le) (sq_nonneg _))

theorem quadraticFirst_projection (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hi : ∀ m : ℝ, ∀ v : ℝ≥0, Integrable φ (gaussianReal m v)) (w x : Vec3) :
    quadraticFirst l Q (fun y => φ (∑ i, w i * y i)) x =
      ∫ y, φ y ∂gaussianReal (∑ i, w i * gaussianPathMean l Q x i)
        (Real.toNNReal (gaussianPathVariance l Q w)) := by
  induction l generalizing x with
  | nil => simp [quadraticFirst, gaussianPathMean, gaussianPathVariance, gaussianPathCovariance]
  | cons u l ih =>
    rcases hl with ⟨hl, _, hp⟩
    let P := (riccatiRecursion l Q).precision u.1 u.2
    let S := u.1 * (riccatiRecursion l Q).slope u.2 x
    let M := ∑ i, w i * gaussianPathMean l Q x i
    let L := ∑ i, w i * gaussianPathLinear l Q u.2 i
    let V := gaussianPathVariance l Q w
    have hV : 0 ≤ V := gaussianPathVariance_nonneg l Q hl w
    have hP : 0 < P := hp
    have hmean (t : ℝ) : (∑ i, w i * gaussianPathMean l Q (x + t • u.2) i) = M + L * t := by
      rw [gaussianPathMean_shift]
      simp only [M, L, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change (∫ t, quadraticFirst l Q (fun y => φ (∑ i, w i * y i)) (x + t • u.2)
      ∂quadraticGaussian P S) = _
    simp_rw [ih hl, hmean, integral_gaussian_shift φ (M + L * _) _ hφ]
    rw [quadraticGaussian, gaussian_integral_affine φ (S / P) M L
      (Real.toNNReal P⁻¹) (Real.toNNReal V) (hi _ _)]
    have hm : L * (S / P) + M = ∑ i, w i * gaussianPathMean (u :: l) Q x i := by
      change L * (S / P) + M = ∑ i, w i * gaussianPathMean l Q
        (x + (S / P) • u.2) i
      rw [hmean]
      ring
    have hv : (NNReal.mk (L ^ 2) (sq_nonneg L) : ℝ≥0) * Real.toNNReal P⁻¹ + Real.toNNReal V =
        Real.toNNReal (gaussianPathVariance (u :: l) Q w) := by
      apply NNReal.eq
      rw [gaussianPathVariance_cons]
      change L ^ 2 * (Real.toNNReal P⁻¹ : ℝ) + (Real.toNNReal V : ℝ) =
        (Real.toNNReal (V + P⁻¹ * L ^ 2) : ℝ)
      rw [Real.toNNReal_of_nonneg (inv_nonneg.mpr hP.le), Real.toNNReal_of_nonneg hV,
        Real.toNNReal_of_nonneg (by positivity : 0 ≤ V + P⁻¹ * L ^ 2)]
      change L ^ 2 * P⁻¹ + V = V + P⁻¹ * L ^ 2
      ring
    rw [hm, hv]

theorem gaussianPathLinear_hessian (l : List (ℝ × Vec3)) (c u χ z : ℝ) (w : Vec3) (i : Fin 3) :
    χ * gaussianPathLinear l (separableTaylorQuadratic c u χ z) w i =
      (riccatiRecursion l (separableTaylorQuadratic c u χ z)).hessianDirection w i := by
  induction l generalizing w with
  | nil =>
    simp only [gaussianPathLinear, riccatiRecursion, QuadraticTerminal.hessianDirection,
      separableTaylorQuadratic]
    simp_rw [ite_mul, zero_mul]
    simp
  | cons v l ih =>
    rw [gaussianPathLinear, ih, riccatiRecursion]
    simp only [QuadraticTerminal.hessianDirection, QuadraticTerminal.update,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ]
    ring

theorem gaussianPathLinear_hessian_div (l : List (ℝ × Vec3)) (c u χ z : ℝ) (hχ : χ ≠ 0)
    (w : Vec3) (i : Fin 3) :
    gaussianPathLinear l (separableTaylorQuadratic c u χ z) w i =
      (riccatiRecursion l (separableTaylorQuadratic c u χ z)).hessianDirection w i / χ := by
  apply (eq_div_iff hχ).mpr
  rw [mul_comm]
  exact gaussianPathLinear_hessian l c u χ z w i

theorem gaussianPathCovariance_hessian_increment (l : List (ℝ × Vec3)) (v : ℝ × Vec3)
    (c u χ z : ℝ) (hm : v.1 ≠ 0) (hχ : χ ≠ 0) (i j : Fin 3) :
    gaussianPathCovariance (v :: l) (separableTaylorQuadratic c u χ z) i j -
        gaussianPathCovariance l (separableTaylorQuadratic c u χ z) i j =
      ((riccatiRecursion (v :: l) (separableTaylorQuadratic c u χ z)).hessian i j -
        (riccatiRecursion l (separableTaylorQuadratic c u χ z)).hessian i j) / (v.1 * χ ^ 2) := by
  rw [gaussianPathCovariance, gaussianPathLinear_hessian_div l c u χ z hχ v.2 i,
    gaussianPathLinear_hessian_div l c u χ z hχ v.2 j, riccatiRecursion]
  simp only [QuadraticTerminal.update]
  field_simp
  ring

theorem gaussianPathCovariance_block (l t : List (ℝ × Vec3)) (c u χ z m : ℝ)
    (hm : m ≠ 0) (hχ : χ ≠ 0) (hml : ∀ v ∈ l, v.1 = m) (i j : Fin 3) :
    gaussianPathCovariance (l ++ t) (separableTaylorQuadratic c u χ z) i j -
        gaussianPathCovariance t (separableTaylorQuadratic c u χ z) i j =
      ((riccatiRecursion (l ++ t) (separableTaylorQuadratic c u χ z)).hessian i j -
        (riccatiRecursion t (separableTaylorQuadratic c u χ z)).hessian i j) / (m * χ ^ 2) := by
  induction l with
  | nil => simp only [List.nil_append, sub_self, zero_div]
  | cons v l ih =>
    have hm₀ : v.1 = m := hml v List.mem_cons_self
    have hml' : ∀ w ∈ l, w.1 = m := fun w hw => hml w (List.mem_cons_of_mem v hw)
    have H := gaussianPathCovariance_hessian_increment (l ++ t) v c u χ z (hm₀ ▸ hm) hχ i j
    rw [hm₀] at H
    simp only [List.cons_append]
    linear_combination H + ih hml'

theorem quadraticFirst_coordinate (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hi : ∀ m : ℝ, ∀ v : ℝ≥0, Integrable φ (gaussianReal m v)) (i : Fin 3) (x : Vec3) :
    quadraticFirst l Q (fun y => φ (y i)) x =
      ∫ y, φ y ∂gaussianReal (gaussianPathMean l Q x i)
        (Real.toNNReal (gaussianPathCovariance l Q i i)) := by
  simpa [gaussianPathVariance, Pi.single_apply] using
    quadraticFirst_projection l Q hl φ hφ hi (Pi.single i 1) x

theorem quadraticFirst_projection_integrable (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hi : ∀ m : ℝ, ∀ v : ℝ≥0, Integrable φ (gaussianReal m v)) (w x v : Vec3) (m : ℝ) (σ : ℝ≥0) :
    Integrable (fun t => quadraticFirst l Q (fun y => φ (∑ i, w i * y i)) (x + t • v))
      (gaussianReal m σ) := by
  let M := ∑ i, w i * gaussianPathMean l Q x i
  let L := ∑ i, w i * gaussianPathLinear l Q v i
  let V := Real.toNNReal (gaussianPathVariance l Q w)
  have he (t : ℝ) : quadraticFirst l Q (fun y => φ (∑ i, w i * y i)) (x + t • v) =
      ∫ s, φ (M + L * t + s) ∂gaussianReal 0 V := by
    rw [quadraticFirst_projection l Q hl φ hφ hi w (x + t • v), gaussianPathMean_shift]
    have hm : (∑ i, w i * (gaussianPathMean l Q x + t • gaussianPathLinear l Q v) i) = M + L * t := by
      simp only [M, L, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hm, integral_gaussian_shift φ _ _ hφ]
  exact (gaussian_integral_affine_integrable φ m M L σ V (hi _ _)).congr
    (ae_of_all _ (fun t => (he t).symm))

theorem quadraticFirst_separable (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hi : ∀ m : ℝ, ∀ v : ℝ≥0, Integrable φ (gaussianReal m v)) (x : Vec3) :
    quadraticFirst l Q (fun y => ∑ i, φ (y i)) x =
      ∑ i, ∫ y, φ y ∂gaussianReal (gaussianPathMean l Q x i)
        (Real.toNNReal (gaussianPathCovariance l Q i i)) := by
  induction l generalizing x with
  | nil => simp [quadraticFirst, gaussianPathMean, gaussianPathCovariance]
  | cons u l ih =>
    have hfull := hl
    rcases hl with ⟨hl, _, hp⟩
    let μ := quadraticGaussian ((riccatiRecursion l Q).precision u.1 u.2)
      (u.1 * (riccatiRecursion l Q).slope u.2 x)
    have hInt (i : Fin 3) : Integrable (fun t => ∫ y, φ y
        ∂gaussianReal (gaussianPathMean l Q (x + t • u.2) i)
          (Real.toNNReal (gaussianPathCovariance l Q i i))) μ := by
      have H := quadraticFirst_projection_integrable l Q hl φ hφ hi (Pi.single i 1) x u.2
        (u.1 * (riccatiRecursion l Q).slope u.2 x / (riccatiRecursion l Q).precision u.1 u.2)
        (Real.toNNReal ((riccatiRecursion l Q).precision u.1 u.2)⁻¹)
      have H' : Integrable (fun t => quadraticFirst l Q (fun y => φ (y i)) (x + t • u.2)) μ := by
        simpa only [μ, quadraticGaussian, Pi.single_apply, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true] using H
      exact H'.congr (ae_of_all _ (fun t => quadraticFirst_coordinate l Q hl φ hφ hi i (x + t • u.2)))
    change (∫ t, quadraticFirst l Q (fun y => ∑ i, φ (y i)) (x + t • u.2) ∂μ) = _
    simp_rw [ih hl]
    rw [integral_finsetSum _ (fun i _ => hInt i)]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [← quadraticFirst_coordinate l Q hl φ hφ hi i]
    exact quadraticFirst_coordinate (u :: l) Q hfull φ hφ hi i x

def scalarTerminalResidual (β : ℝ) (α : ℝ → ℝ) (s h z y : ℝ) : ℝ :=
  Phi β α (s + 4 * h) y - (Phi β α (s + 4 * h) z +
    jet β α 1 (s + 4 * h) z * (y - z) + jet β α 2 (s + 4 * h) z / 2 * (y - z) ^ 2)

theorem scalarTerminalResidual_integrable (β : ℝ) (α : ℝ → ℝ) (s h z m : ℝ) (v : ℝ≥0)
    (hφ : BoundedDerivs (Phi β α (s + 4 * h))) :
    Integrable (scalarTerminalResidual β α s h z) (gaussianReal m v) := by
  have hid : HasExpGrowth (fun y : ℝ => y) :=
    HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hshift : HasExpGrowth (fun y : ℝ => y - z) := hid.sub_real (HasExpGrowth.const z)
  have hg : HasExpGrowth (scalarTerminalResidual β α s h z) :=
    hφ.hasExpGrowth.sub_real (((HasExpGrowth.const (Phi β α (s + 4 * h) z)).add
      ((HasExpGrowth.const (jet β α 1 (s + 4 * h) z)).mul hshift)).add
        ((HasExpGrowth.const (jet β α 2 (s + 4 * h) z / 2)).mul (hshift.pow 2)))
  have hc : Continuous (Phi β α (s + 4 * h)) := hφ.1.continuous
  exact hg.integrable_gaussianMeasure (by
    unfold scalarTerminalResidual
    fun_prop)

theorem terminalResidual_eq_scalar_sum (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) :
    terminalResidual β α s h z = fun x => ∑ i, scalarTerminalResidual β α s h z (x i) := by
  funext x
  rw [terminalResidual, terminalTaylorQuadratic_value]
  simp only [scalarTerminalResidual, frozenTerminal, Finset.sum_sub_distrib]

theorem frozenFirstMoment_eq_scalar_gaussians (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hφ : BoundedDerivs (Phi β α (s + 4 * h))) :
    frozenFirstMoment β α a s h k z =
      ∑ i, ∫ y, scalarTerminalResidual β α s h z y
        ∂gaussianReal (gaussianPathMean (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z) (fun _ => z) i)
          (Real.toNNReal (gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z) i i)) := by
  unfold frozenFirstMoment
  rw [terminalResidual_eq_scalar_sum]
  apply quadraticFirst_separable _ _ hl
  · unfold scalarTerminalResidual
    have hm : Measurable (Phi β α (s + 4 * h)) := hφ.1.continuous.measurable
    fun_prop
  · exact fun m v => scalarTerminalResidual_integrable β α s h z m v hφ

theorem frozenSchedule_pathCovariance_hessian (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hχ : χ ≠ 0) (i j : Fin 3) :
    gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) i j =
      (3 * (riccatiRecursion (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)).hessian i j -
        (riccatiRecursion (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k)
          (separableTaylorQuadratic c u χ z)).hessian i j -
        (riccatiRecursion (frozenInner β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)).hessian i j -
        (if i = j then χ else 0)) / (a * χ ^ 2) := by
  let Q := separableTaylorQuadratic c u χ z
  let l₀ := frozenCommon β a (1 / 2) h k
  let l₁ := frozenShared β a (1 / 2) h k
  let l₂ := frozenInner β a (1 / 2) h k
  have H₀ := gaussianPathCovariance_block l₀ (l₁ ++ l₂) c u χ z (a / 3)
    (div_ne_zero ha (by norm_num)) hχ (by simp [l₀, frozenCommon]) i j
  have H₁ := gaussianPathCovariance_block l₁ l₂ c u χ z (a / 2)
    (div_ne_zero ha (by norm_num)) hχ (by simp [l₁, frozenShared]) i j
  have H₂ := gaussianPathCovariance_block l₂ [] c u χ z a ha hχ (by simp [l₂, frozenInner]) i j
  simp only [List.append_nil] at H₂
  change gaussianPathCovariance l₂ Q i j - 0 =
    ((riccatiRecursion l₂ Q).hessian i j - (if i = j then χ else 0)) / (a * χ ^ 2) at H₂
  rw [sub_zero] at H₂
  change gaussianPathCovariance (l₀ ++ (l₁ ++ l₂)) Q i j =
    (3 * (riccatiRecursion (l₀ ++ (l₁ ++ l₂)) Q).hessian i j -
      (riccatiRecursion (l₁ ++ l₂) Q).hessian i j - (riccatiRecursion l₂ Q).hessian i j -
      (if i = j then χ else 0)) / (a * χ ^ 2)
  field_simp [ha, hχ] at H₀ H₁ H₂ ⊢
  nlinarith

theorem riccatiRecursion_hessian_resolvent (l : List (ℝ × Vec3)) (c u χ z : ℝ)
    (hl : RiccatiAdmissible l (separableTaylorQuadratic c u χ z)) :
    (riccatiRecursion l (separableTaylorQuadratic c u χ z)).hessianMatrix =
      χ • (riccatiPrecisionMatrix l χ)⁻¹ := by
  have H := congrArg (fun A : Mat3 => A * (riccatiPrecisionMatrix l χ)⁻¹)
    (riccatiRecursion_precisionMatrix l c u χ z hl)
  rw [Matrix.mul_nonsing_inv_cancel_right (riccatiPrecisionMatrix l χ) _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (riccatiPrecisionMatrix_det_pos l c u χ z hl))),
    Matrix.smul_mul, Matrix.one_mul] at H
  exact H

def frozenCovarianceResolvent (j : Fin 3) (t k : ℝ) : Mat3 :=
  (1 - t • frozenRiccatiCovariance j k)⁻¹

theorem frozenSchedule_pathCovariance_resolvent (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hχ : χ ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (i j : Fin 3) :
    gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) i j =
      (3 * frozenCovarianceResolvent 0 (a * β ^ 2 * χ * h) k i j -
        frozenCovarianceResolvent 1 (a * β ^ 2 * χ * h) k i j -
        frozenCovarianceResolvent 2 (a * β ^ 2 * χ * h) k i j - (if i = j then 1 else 0)) / (a * χ) := by
  let Q := separableTaylorQuadratic c u χ z
  let l₁ := frozenShared β a (1 / 2) h k
  let l₂ := frozenInner β a (1 / 2) h k
  have htail : RiccatiAdmissible (l₁ ++ l₂) Q := riccatiAdmissible_suffix
    (frozenCommon β a (1 / 2) h k) (l₁ ++ l₂) Q (by simpa only [frozenSchedule, List.append_assoc] using hl)
  have hinner : RiccatiAdmissible l₂ Q := riccatiAdmissible_suffix l₁ l₂ Q htail
  have A₀ : riccatiPrecisionMatrix (frozenSchedule β a (1 / 2) h k) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₀ k := by
    rw [riccatiPrecisionMatrix, frozenSchedule_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have A₁ : riccatiPrecisionMatrix (l₁ ++ l₂) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₁ k := by
    rw [riccatiPrecisionMatrix, riccatiWeightedCovariance_append,
      frozenShared_weightedCovariance β a h k hh, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [frozenRiccatiCovariance₁, frozenRiccatiCovariance₂, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have A₂ : riccatiPrecisionMatrix l₂ χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₂ k := by
    rw [riccatiPrecisionMatrix, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have H₀ := congrFun (congrFun (riccatiRecursion_hessian_resolvent _ c u χ z hl) i) j
  have H₁ := congrFun (congrFun (riccatiRecursion_hessian_resolvent _ c u χ z htail) i) j
  have H₂ := congrFun (congrFun (riccatiRecursion_hessian_resolvent _ c u χ z hinner) i) j
  rw [A₀] at H₀
  rw [A₁] at H₁
  rw [A₂] at H₂
  simp only [QuadraticTerminal.hessianMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at H₀ H₁ H₂
  change (riccatiRecursion _ Q).hessian i j = χ * frozenCovarianceResolvent 0 (a * β ^ 2 * χ * h) k i j at H₀
  change (riccatiRecursion (l₁ ++ l₂) Q).hessian i j = χ * frozenCovarianceResolvent 1 (a * β ^ 2 * χ * h) k i j at H₁
  change (riccatiRecursion l₂ Q).hessian i j = χ * frozenCovarianceResolvent 2 (a * β ^ 2 * χ * h) k i j at H₂
  rw [frozenSchedule_pathCovariance_hessian β a h k c u χ z ha hχ i j, H₀, H₁, H₂]
  split_ifs
  · field_simp [ha, hχ]
  · field_simp [ha, hχ]
    ring

theorem gaussianPathMean_of_aligned_zero (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (x : Vec3) (hx : Q.AlignedSlope x 0) : gaussianPathMean l Q x = x := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    have hs : (riccatiRecursion l Q).slope v.2 x = 0 := by
      rw [QuadraticTerminal.alignedSlope_slope _ v.2 x 0
        (riccatiRecursion_aligned_value l Q x 0 hx).1, zero_mul]
    rw [gaussianPathMean, quadraticMeanTransition, hs, mul_zero, zero_div, zero_smul, add_zero]
    exact ih

private theorem ones_coordinate_eq_one (i : Fin 3) : ones i = 1 := by
  fin_cases i <;> rfl

theorem gaussianPathMean_diagonal (l : List (ℝ × Vec3)) (c u χ z : ℝ) (hχ : χ ≠ 0) (i : Fin 3) :
    gaussianPathMean l (separableTaylorQuadratic c u χ z) (fun _ => z) i =
      z - u / χ + (u / χ) * gaussianPathLinear l (separableTaylorQuadratic c u χ z) ones i := by
  let x : Vec3 := fun _ => z - u / χ
  have hx : (separableTaylorQuadratic c u χ z).AlignedSlope x 0 := by
    intro j
    simp only [QuadraticTerminal.slopeVector, separableTaylorQuadratic, x, zero_mul]
    simp_rw [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
    ring
  have he : (fun _ : Fin 3 => z) = x + (u / χ) • ones := by
    ext j
    simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ones_coordinate_eq_one, mul_one]
    ring
  rw [he, gaussianPathMean_shift, gaussianPathMean_of_aligned_zero l _ x hx]
  rfl

theorem frozenSchedule_pathMean_of_curvature_ne_zero (β a h k c u χ z : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) (hχ : χ ≠ 0)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) (i : Fin 3) :
    gaussianPathMean (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) (fun _ => z) i =
      z + 4 * a * β ^ 2 * h * u / (1 - 4 * a * β ^ 2 * χ * h) := by
  let l := frozenSchedule β a (1 / 2) h k
  let Q := separableTaylorQuadratic c u χ z
  have H := congrArg (fun A : Mat3 => A *ᵥ ones)
    (riccatiRecursion_precisionMatrix l c u χ z hl)
  rw [← Matrix.mulVec_mulVec, frozenSchedule_precisionMatrix_ones β a h k χ hh hk,
    Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.one_mulVec] at H
  have he : (1 - 4 * a * β ^ 2 * χ * h) * (riccatiRecursion l Q).hessianDirection ones i = χ := by
    simpa only [l, Q, Pi.smul_apply, smul_eq_mul, ones_coordinate_eq_one, mul_one,
      QuadraticTerminal.hessianDirection, QuadraticTerminal.hessianMatrix,
      Matrix.mulVec, dotProduct, Matrix.of_apply] using congrFun H i
  rw [← gaussianPathLinear_hessian l c u χ z ones i] at he
  have hS : (1 - 4 * a * β ^ 2 * χ * h) * gaussianPathLinear l Q ones i = 1 := by
    apply (mul_left_cancel₀ hχ)
    linear_combination he
  have hd : 1 - 4 * a * β ^ 2 * χ * h ≠ 0 := by
    intro hd
    rw [hd, zero_mul] at hS
    exact zero_ne_one hS
  have hs : gaussianPathLinear l Q ones i = 1 / (1 - 4 * a * β ^ 2 * χ * h) := by
    apply (eq_div_iff hd).mpr
    rw [mul_comm]
    exact hS
  rw [gaussianPathMean_diagonal _ c u χ z hχ i, hs]
  generalize hden : 1 - 4 * a * β ^ 2 * χ * h = d at hd ⊢
  field_simp [hχ, hd]
  rw [← hden]
  ring

theorem gaussianPathLinear_zero_curvature (l : List (ℝ × Vec3)) (c u z : ℝ) (w : Vec3) :
    gaussianPathLinear l (separableTaylorQuadratic c u 0 z) w = w := by
  induction l generalizing w with
  | nil => rfl
  | cons v l ih =>
    have hH := (riccatiRecursion_affine l c u z).1
    have hD : (riccatiRecursion l (separableTaylorQuadratic c u 0 z)).hessianDirection v.2 = 0 := by
      ext i
      simp only [QuadraticTerminal.hessianDirection, hH, zero_mul, Finset.sum_const_zero, Pi.zero_apply]
    rw [gaussianPathLinear, hD]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_smul, add_zero]
    exact ih w

theorem gaussianPathCovariance_zero_curvature (l : List (ℝ × Vec3)) (c u z : ℝ) (i j : Fin 3) :
    gaussianPathCovariance l (separableTaylorQuadratic c u 0 z) i j = matrixChainCovariance l i j := by
  induction l with
  | nil => simp [gaussianPathCovariance]
  | cons v l ih =>
    have hH := (riccatiRecursion_affine l c u z).1
    have hP : (riccatiRecursion l (separableTaylorQuadratic c u 0 z)).precision v.1 v.2 = 1 := by
      simp only [QuadraticTerminal.precision, QuadraticTerminal.curvature,
        QuadraticTerminal.hessianDirection, hH, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero]
    rw [gaussianPathCovariance, ih, gaussianPathLinear_zero_curvature, hP, inv_one,
      one_mul, matrixChainCovariance_cons]
    simp only [Pi.add_apply, rankOneMatrix]
    ring

theorem gaussianPathMean_zero_curvature (l : List (ℝ × Vec3)) (c u z : ℝ) (x : Vec3) :
    gaussianPathMean l (separableTaylorQuadratic c u 0 z) x =
      x + u • (riccatiWeightedCovariance l *ᵥ ones) := by
  induction l generalizing x with
  | nil => simp [gaussianPathMean, riccatiWeightedCovariance]
  | cons v l ih =>
    have hH := (riccatiRecursion_affine l c u z).1
    have hL := (riccatiRecursion_affine l c u z).2.1
    have hP : (riccatiRecursion l (separableTaylorQuadratic c u 0 z)).precision v.1 v.2 = 1 := by
      simp only [QuadraticTerminal.precision, QuadraticTerminal.curvature,
        QuadraticTerminal.hessianDirection, hH, zero_mul, Finset.sum_const_zero, mul_zero, sub_zero]
    have hS : (riccatiRecursion l (separableTaylorQuadratic c u 0 z)).slope v.2 x = u * ∑ i, v.2 i := by
      simp only [QuadraticTerminal.slope, QuadraticTerminal.linearDirection,
        QuadraticTerminal.hessianDirection, hH, hL, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      rw [Finset.mul_sum]
    rw [gaussianPathMean, quadraticMeanTransition, hP, hS, div_one, ih]
    ext i
    simp only [riccatiWeightedCovariance, Matrix.mulVec, Matrix.add_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ones_coordinate_eq_one, mul_one, Fin.sum_univ_succ]
    ring

theorem frozenSchedule_pathMean (β a h k c u χ z : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) (i : Fin 3) :
    gaussianPathMean (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) (fun _ => z) i =
      z + 4 * a * β ^ 2 * h * u / (1 - 4 * a * β ^ 2 * χ * h) := by
  by_cases hχ : χ = 0
  · subst χ
    rw [gaussianPathMean_zero_curvature, frozenSchedule_weightedCovariance β a h k hh hk,
      Matrix.smul_mulVec, frozenRiccatiCovariance₀_ones]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ones_coordinate_eq_one,
      mul_one, mul_zero]
    ring
  · exact frozenSchedule_pathMean_of_curvature_ne_zero β a h k c u χ z hh hk hχ hl i

theorem frozenFirstMoment_eq_common_mean_gaussians (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hφ : BoundedDerivs (Phi β α (s + 4 * h))) :
    frozenFirstMoment β α a s h k z =
      ∑ i, ∫ y, scalarTerminalResidual β α s h z y
        ∂gaussianReal (z + 4 * a * β ^ 2 * h * jet β α 1 (s + 4 * h) z /
          (1 - 4 * a * β ^ 2 * jet β α 2 (s + 4 * h) z * h))
          (Real.toNNReal (gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z) i i)) := by
  rw [frozenFirstMoment_eq_scalar_gaussians β α a s h k z hl hφ]
  apply Finset.sum_congr rfl
  intro i _
  unfold terminalTaylorQuadratic at hl ⊢
  rw [frozenSchedule_pathMean β a h k _ _ _ z hh hk hl i]

theorem matrix_resolvent_taylor (A : Mat3) (t : ℝ) (hA : IsUnit (1 - t • A).det) :
    (1 - t • A)⁻¹ = 1 + t • A + t ^ 2 • (A * A) +
      t ^ 3 • (A * A * A * (1 - t • A)⁻¹) := by
  have he : (1 + t • A + t ^ 2 • (A * A)) * (1 - t • A) = 1 - t ^ 3 • (A * A * A) := by
    simp only [add_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    module
  have H := congrArg (fun B : Mat3 => B * (1 - t • A)⁻¹) he
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.mul_one,
    sub_mul, Matrix.one_mul, Matrix.smul_mul] at H
  exact sub_eq_iff_eq_add.mp H.symm

def frozenCovarianceLinear (k : ℝ) : Mat3 :=
  (3 : ℝ) • frozenRiccatiCovariance₀ k - frozenRiccatiCovariance₁ k - frozenRiccatiCovariance₂ k

def frozenCovarianceQuadratic (k : ℝ) : Mat3 :=
  (3 : ℝ) • (frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k) -
    frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k - frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k

def frozenCovarianceRemainder (t k : ℝ) : Mat3 :=
  (3 : ℝ) • (frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k * frozenRiccatiCovariance₀ k *
    frozenCovarianceResolvent 0 t k) -
    frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k * frozenRiccatiCovariance₁ k * frozenCovarianceResolvent 1 t k -
    frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k * frozenRiccatiCovariance₂ k * frozenCovarianceResolvent 2 t k

theorem frozenCovarianceLinear_diagonal (k : ℝ) (i : Fin 3) : frozenCovarianceLinear k i i = 4 := by
  fin_cases i <;>
    simp [frozenCovarianceLinear, frozenRiccatiCovariance₀, frozenRiccatiCovariance₁,
      frozenRiccatiCovariance₂, physicalInner, q0, q1, q2, outer, commonVector,
      sharedVector, tentWeight, rampWeight] <;> ring

theorem frozenCovarianceQuadratic_trace (k : ℝ) :
    matrixTrace (frozenCovarianceQuadratic k) = physicalNorm k := by
  have H₁ := frozenRiccatiTracePolynomial_eq 1 1 1 1 k
  have H₂ := frozenRiccatiTracePolynomial_eq 1 1 1 (-1) k
  unfold frozenRiccatiTracePolynomial at H₁ H₂
  simp only [frozenCovarianceQuadratic, matrixTrace, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ] at H₁ H₂ ⊢
  linear_combination 2 * H₁ + 2 * H₂

theorem frozenCovarianceQuadratic_trace_difference (k : ℝ) :
    matrixTrace (frozenCovarianceQuadratic k) - matrixTrace (frozenCovarianceQuadratic 0) =
      penaltyPolynomial (1 / 2) k := by
  rw [frozenCovarianceQuadratic_trace, frozenCovarianceQuadratic_trace]
  exact physical_norm_difference k

theorem frozenCovarianceCombination_expansion (a b χ h k : ℝ) (ha : a ≠ 0) (hχ : χ ≠ 0)
    (hunit : ∀ j : Fin 3, IsUnit (1 - (a * b * χ * h) • frozenRiccatiCovariance j k).det) (i j : Fin 3) :
    (3 * frozenCovarianceResolvent 0 (a * b * χ * h) k i j -
      frozenCovarianceResolvent 1 (a * b * χ * h) k i j -
      frozenCovarianceResolvent 2 (a * b * χ * h) k i j - (if i = j then 1 else 0)) / (a * χ) =
      b * h * frozenCovarianceLinear k i j + a * b ^ 2 * χ * h ^ 2 * frozenCovarianceQuadratic k i j +
        a ^ 2 * b ^ 3 * χ ^ 2 * h ^ 3 * frozenCovarianceRemainder (a * b * χ * h) k i j := by
  have H₀ := congrFun (congrFun (matrix_resolvent_taylor (frozenRiccatiCovariance 0 k) (a * b * χ * h) (hunit 0)) i) j
  have H₁ := congrFun (congrFun (matrix_resolvent_taylor (frozenRiccatiCovariance 1 k) (a * b * χ * h) (hunit 1)) i) j
  have H₂ := congrFun (congrFun (matrix_resolvent_taylor (frozenRiccatiCovariance 2 k) (a * b * χ * h) (hunit 2)) i) j
  change frozenCovarianceResolvent 0 (a * b * χ * h) k i j = _ at H₀
  change frozenCovarianceResolvent 1 (a * b * χ * h) k i j = _ at H₁
  change frozenCovarianceResolvent 2 (a * b * χ * h) k i j = _ at H₂
  simp [frozenRiccatiCovariance, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at H₀ H₁ H₂
  rw [H₀, H₁, H₂]
  simp only [frozenCovarianceLinear, frozenCovarianceQuadratic, frozenCovarianceRemainder,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hr₀ : frozenCovarianceResolvent 0 (a * b * χ * h) k = (1 - (a * b * χ * h) • frozenRiccatiCovariance₀ k)⁻¹ := rfl
  have hr₁ : frozenCovarianceResolvent 1 (a * b * χ * h) k = (1 - (a * b * χ * h) • frozenRiccatiCovariance₁ k)⁻¹ := rfl
  have hr₂ : frozenCovarianceResolvent 2 (a * b * χ * h) k = (1 - (a * b * χ * h) • frozenRiccatiCovariance₂ k)⁻¹ := rfl
  rw [hr₀, hr₁, hr₂]
  split_ifs <;> field_simp [ha, hχ] <;> first | done | ring

theorem frozenCovarianceLinear_eq (k : ℝ) :
    frozenCovarianceLinear k = !![4, 1 + k, 1 - k; 1 + k, 4, 3 / 2; 1 - k, 3 / 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frozenCovarianceLinear, frozenRiccatiCovariance₀, frozenRiccatiCovariance₁,
      frozenRiccatiCovariance₂, physicalInner, q0, q1, q2, outer, commonVector,
      sharedVector, tentWeight, rampWeight] <;> ring

theorem frozenSchedule_resolvent_units (β a h k c u χ z : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) :
    ∀ j : Fin 3, IsUnit (1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance j k).det := by
  let Q := separableTaylorQuadratic c u χ z
  let l₁ := frozenShared β a (1 / 2) h k
  let l₂ := frozenInner β a (1 / 2) h k
  have htail : RiccatiAdmissible (l₁ ++ l₂) Q := riccatiAdmissible_suffix
    (frozenCommon β a (1 / 2) h k) (l₁ ++ l₂) Q (by simpa only [frozenSchedule, List.append_assoc] using hl)
  have hinner : RiccatiAdmissible l₂ Q := riccatiAdmissible_suffix l₁ l₂ Q htail
  have h₀ := riccatiPrecisionMatrix_det_pos _ c u χ z hl
  have h₁ := riccatiPrecisionMatrix_det_pos _ c u χ z htail
  have h₂ := riccatiPrecisionMatrix_det_pos _ c u χ z hinner
  have A₀ : riccatiPrecisionMatrix (frozenSchedule β a (1 / 2) h k) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₀ k := by
    rw [riccatiPrecisionMatrix, frozenSchedule_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have A₁ : riccatiPrecisionMatrix (l₁ ++ l₂) χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₁ k := by
    rw [riccatiPrecisionMatrix, riccatiWeightedCovariance_append,
      frozenShared_weightedCovariance β a h k hh, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [frozenRiccatiCovariance₁, frozenRiccatiCovariance₂, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have A₂ : riccatiPrecisionMatrix l₂ χ =
      1 - (a * β ^ 2 * χ * h) • frozenRiccatiCovariance₂ k := by
    rw [riccatiPrecisionMatrix, frozenInner_weightedCovariance β a h k hh hk]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [A₀] at h₀
  rw [A₁] at h₁
  rw [A₂] at h₂
  intro j
  fin_cases j
  · exact isUnit_iff_ne_zero.mpr (ne_of_gt h₀)
  · exact isUnit_iff_ne_zero.mpr (ne_of_gt h₁)
  · exact isUnit_iff_ne_zero.mpr (ne_of_gt h₂)

theorem frozenSchedule_pathCovariance_expansion (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) (i j : Fin 3) :
    gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) i j =
      β ^ 2 * h * frozenCovarianceLinear k i j + a * β ^ 4 * χ * h ^ 2 * frozenCovarianceQuadratic k i j +
        a ^ 2 * β ^ 6 * χ ^ 2 * h ^ 3 * frozenCovarianceRemainder (a * β ^ 2 * χ * h) k i j := by
  by_cases hχ : χ = 0
  · subst χ
    rw [gaussianPathCovariance_zero_curvature, frozenSchedule_covariance β a (1 / 2) h k hh
      (by norm_num) (OW.repairLength_mem (by norm_num) hk), frozenCovarianceLinear_eq]
    simp only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    norm_num
  · rw [frozenSchedule_pathCovariance_resolvent β a h k c u χ z ha hχ hh hk hl,
      frozenCovarianceCombination_expansion a (β ^ 2) χ h k ha hχ
        (frozenSchedule_resolvent_units β a h k c u χ z hh hk hl)]
    ring

theorem frozenSchedule_pathVariance_expansion (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)) (i : Fin 3) :
    gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) i i =
      4 * β ^ 2 * h + a * β ^ 4 * χ * h ^ 2 * frozenCovarianceQuadratic k i i +
        a ^ 2 * β ^ 6 * χ ^ 2 * h ^ 3 * frozenCovarianceRemainder (a * β ^ 2 * χ * h) k i i := by
  rw [frozenSchedule_pathCovariance_expansion β a h k c u χ z ha hh hk hl i i,
    frozenCovarianceLinear_diagonal]
  ring

theorem smoothOn_uniform_vertical_bounds {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (δ : ℝ)
    (hKU : (Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)) ⊆ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc (-δ) δ, ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      |F (t, k)| ≤ B ∧ |verticalDerivative F (t, k)| ≤ B ∧
        |verticalDerivative (verticalDerivative F) (t, k)| ≤ B := by
  have hF₁ : ContDiffOn ℝ ∞ (verticalDerivative F) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hF₂ : ContDiffOn ℝ ∞ (verticalDerivative (verticalDerivative F)) U :=
    (hF₁.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hK : IsCompact (Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn (hF.continuousOn.mono hKU)
  obtain ⟨B₁, hB₁⟩ := hK.exists_bound_of_continuousOn (hF₁.continuousOn.mono hKU)
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn (hF₂.continuousOn.mono hKU)
  refine ⟨1 + |B₀| + |B₁| + |B₂|, by positivity, ?_⟩
  intro t ht k hk
  have h₀ : |F (t, k)| ≤ B₀ := hB₀ (t, k) ⟨ht, hk⟩
  have h₁ : |verticalDerivative F (t, k)| ≤ B₁ := hB₁ (t, k) ⟨ht, hk⟩
  have h₂ : |verticalDerivative (verticalDerivative F) (t, k)| ≤ B₂ := hB₂ (t, k) ⟨ht, hk⟩
  refine ⟨?_, ?_, ?_⟩ <;> linarith [le_abs_self B₀, le_abs_self B₁, le_abs_self B₂,
    abs_nonneg B₀, abs_nonneg B₁, abs_nonneg B₂]

def frozenResolventDomain : Set (ℝ × ℝ) :=
  {x | ∀ j : Fin 3, 1 - x.1 * frozenDetArgument j x ≠ 0}

theorem frozenResolventDomain_isOpen : IsOpen frozenResolventDomain := by
  have he : frozenResolventDomain = ⋂ j : Fin 3, {x : ℝ × ℝ | 1 - x.1 * frozenDetArgument j x ≠ 0} := by
    ext x
    simp [frozenResolventDomain]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_ne_fun (contDiff_const.sub (contDiff_fst.mul (frozenDetArgument_contDiff j))).continuous continuous_const

theorem frozenResolventDomain_contains_rectangle :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)) ⊆ frozenResolventDomain := by
  choose B hB hb using fun j : Fin 3 => smooth_uniform_vertical_bounds (frozenDetArgument_contDiff j)
  let M : ℝ := 1 + ∑ j : Fin 3, B j
  have hM : 0 < M := by
    have H : 0 ≤ ∑ j : Fin 3, B j := Finset.sum_nonneg (fun j _ => (hB j).le)
    dsimp only [M]
    linarith
  have hBM (j : Fin 3) : B j ≤ M := by
    have H := Finset.single_le_sum (f := B) (fun i _ => (hB i).le) (Finset.mem_univ j)
    dsimp only [M]
    linarith
  refine ⟨min 1 (1 / (2 * M)), by positivity, min_le_left _ _, ?_⟩
  rintro ⟨t, k⟩ ⟨ht, hk⟩ j
  have htδ : |t| ≤ min 1 (1 / (2 * M)) := abs_le.mpr ht
  have ht₁ : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (htδ.trans (min_le_left _ _))
  have hp : |frozenDetArgument j (t, k)| ≤ M := ((hb j t ht₁ k hk).1).trans (hBM j)
  have hs : |t * frozenDetArgument j (t, k)| ≤ 1 / 2 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / (2 * M)) * M := mul_le_mul (htδ.trans (min_le_right _ _)) hp
        (abs_nonneg _) (by positivity)
      _ = 1 / 2 := by field_simp
  have H := (abs_le.mp hs).2
  dsimp only
  linarith

theorem frozenRiccatiCovariance_entry_contDiff (j i l : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => frozenRiccatiCovariance j x.2 i l) := by
  fin_cases j <;> fin_cases i <;> fin_cases l <;>
    simp [frozenRiccatiCovariance, frozenRiccatiCovariance₀, frozenRiccatiCovariance₁,
      frozenRiccatiCovariance₂, physicalInner, q0, q1, q2, outer, commonVector,
      sharedVector, tentWeight, rampWeight] <;> fun_prop

theorem frozenPrecision_entry_contDiff (j i l : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => (1 - x.1 • frozenRiccatiCovariance j x.2) i l) := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.sub (contDiff_fst.mul (frozenRiccatiCovariance_entry_contDiff j i l))

theorem frozenPrecisionAdjugate_entry_contDiff (j i l : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => (1 - x.1 • frozenRiccatiCovariance j x.2).adjugate i l) := by
  have hC := frozenRiccatiCovariance_entry_contDiff j
  fin_cases i <;> fin_cases l <;> simp [Matrix.adjugate_fin_three] <;> fun_prop

theorem frozenCovarianceResolvent_entry_contDiffOn (j i l : Fin 3) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => frozenCovarianceResolvent j x.1 x.2 i l) frozenResolventDomain := by
  have hd : ContDiff ℝ ∞ (fun x : ℝ × ℝ => 1 - x.1 * frozenDetArgument j x) :=
    contDiff_const.sub (contDiff_fst.mul (frozenDetArgument_contDiff j))
  have hdinv : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (1 - x.1 * frozenDetArgument j x)⁻¹) frozenResolventDomain :=
    hd.contDiffOn.inv (fun x hx => hx j)
  have H := hdinv.mul (frozenPrecisionAdjugate_entry_contDiff j i l).contDiffOn
  convert H using 1
  funext x
  simp only [frozenCovarianceResolvent, Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.smul_apply, smul_eq_mul, det_one_sub_eq, frozenDetArgument]

theorem frozenCovarianceRemainder_entry_contDiffOn (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => frozenCovarianceRemainder x.1 x.2 i j) frozenResolventDomain := by
  have hC := frozenRiccatiCovariance_entry_contDiff
  have hR := frozenCovarianceResolvent_entry_contDiffOn
  unfold frozenCovarianceRemainder
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  change ContDiffOn ℝ ∞ (fun x : ℝ × ℝ =>
    3 * (∑ m, (∑ n, (∑ p, frozenRiccatiCovariance 0 x.2 i p * frozenRiccatiCovariance 0 x.2 p n) *
      frozenRiccatiCovariance 0 x.2 n m) * frozenCovarianceResolvent 0 x.1 x.2 m j) -
    (∑ m, (∑ n, (∑ p, frozenRiccatiCovariance 1 x.2 i p * frozenRiccatiCovariance 1 x.2 p n) *
      frozenRiccatiCovariance 1 x.2 n m) * frozenCovarianceResolvent 1 x.1 x.2 m j) -
    (∑ m, (∑ n, (∑ p, frozenRiccatiCovariance 2 x.2 i p * frozenRiccatiCovariance 2 x.2 p n) *
      frozenRiccatiCovariance 2 x.2 n m) * frozenCovarianceResolvent 2 x.1 x.2 m j)) _
  fun_prop

theorem verticalDerivative_hasDerivAt_on {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (t k : ℝ) (hx : (t, k) ∈ U) :
    HasDerivAt (fun x => F (t, x)) (verticalDerivative F (t, k)) k := by
  have hline : HasDerivAt (fun x : ℝ => (t, x)) (0, 1) k :=
    (hasDerivAt_const k t).prodMk (hasDerivAt_id k)
  exact ((hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt k hline

theorem frozenCovarianceRemainder_uniform_bounds :
    ∃ B δ : ℝ, 0 < B ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ i j : Fin 3, ∀ t : ℝ, |t| ≤ δ → ∀ k : ℝ, |k| ≤ 1 / 2 →
        let F : ℝ × ℝ → ℝ := fun x => frozenCovarianceRemainder x.1 x.2 i j
        |F (t, k)| ≤ B ∧ |verticalDerivative F (t, k)| ≤ B ∧
          |verticalDerivative (verticalDerivative F) (t, k)| ≤ B ∧
          HasDerivAt (fun x => F (t, x)) (verticalDerivative F (t, k)) k ∧
          HasDerivAt (fun x => verticalDerivative F (t, x))
            (verticalDerivative (verticalDerivative F) (t, k)) k := by
  obtain ⟨δ, hδ, hδ₁, hK⟩ := frozenResolventDomain_contains_rectangle
  choose B hB hb using fun i j : Fin 3 => smoothOn_uniform_vertical_bounds
    frozenResolventDomain_isOpen (frozenCovarianceRemainder_entry_contDiffOn i j) δ hK
  let M : ℝ := 1 + ∑ i : Fin 3, ∑ j : Fin 3, B i j
  have hsum : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, B i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hB i j).le))
  have hM : 0 < M := by dsimp only [M]; linarith
  have hBM (i j : Fin 3) : B i j ≤ M := by
    have H₁ := Finset.single_le_sum (f := B i) (fun j _ => (hB i j).le) (Finset.mem_univ j)
    have H₂ := Finset.single_le_sum (f := fun i => ∑ j : Fin 3, B i j)
      (fun i _ => Finset.sum_nonneg (fun j _ => (hB i j).le)) (Finset.mem_univ i)
    dsimp only [M]
    linarith
  refine ⟨M, δ, hM, hδ, hδ₁, ?_⟩
  intro i j t ht k hk
  let F : ℝ × ℝ → ℝ := fun x => frozenCovarianceRemainder x.1 x.2 i j
  have ht' := abs_le.mp ht
  have hk' := abs_le.mp hk
  have H := hb i j t ht' k hk'
  have hF : ContDiffOn ℝ ∞ F frozenResolventDomain := frozenCovarianceRemainder_entry_contDiffOn i j
  have hF₁ : ContDiffOn ℝ ∞ (verticalDerivative F) frozenResolventDomain :=
    (hF.fderiv_of_isOpen frozenResolventDomain_isOpen (by simp)).clm_apply contDiffOn_const
  have hx := hK (show (t, k) ∈ Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) from ⟨ht', hk'⟩)
  exact ⟨H.1.trans (hBM i j), H.2.1.trans (hBM i j), H.2.2.trans (hBM i j),
    verticalDerivative_hasDerivAt_on frozenResolventDomain_isOpen hF t k hx,
    verticalDerivative_hasDerivAt_on frozenResolventDomain_isOpen hF₁ t k hx⟩

theorem frozenFirstMoment_eq_expanded_gaussians (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hφ : BoundedDerivs (Phi β α (s + 4 * h))) :
    frozenFirstMoment β α a s h k z =
      ∑ i, ∫ y, scalarTerminalResidual β α s h z y
        ∂gaussianReal (z + 4 * a * β ^ 2 * h * jet β α 1 (s + 4 * h) z /
          (1 - 4 * a * β ^ 2 * jet β α 2 (s + 4 * h) z * h))
          (Real.toNNReal (4 * β ^ 2 * h +
            a * β ^ 4 * jet β α 2 (s + 4 * h) z * h ^ 2 * frozenCovarianceQuadratic k i i +
            a ^ 2 * β ^ 6 * jet β α 2 (s + 4 * h) z ^ 2 * h ^ 3 *
              frozenCovarianceRemainder (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h) k i i)) := by
  rw [frozenFirstMoment_eq_common_mean_gaussians β α a s h k z hh hk hl hφ]
  apply Finset.sum_congr rfl
  intro i _
  unfold terminalTaylorQuadratic at hl ⊢
  rw [frozenSchedule_pathVariance_expansion β a h k _ _ _ z ha hh hk hl i]

def frozenPathCovarianceError (β : ℝ) (α : ℝ → ℝ) (a s h z : ℝ) (i j : Fin 3) (k : ℝ) : ℝ :=
  gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z) i j -
    β ^ 2 * h * frozenCovarianceLinear k i j -
    a * β ^ 4 * jet β α 2 (s + 4 * h) z * h ^ 2 * frozenCovarianceQuadratic k i j

theorem frozenPathCovarianceError_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ → |jet β α 2 (s + 4 * h) z| ≤ B →
      ∀ i j : Fin 3, ∃ g₁ g₂ : ℝ → ℝ, ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        HasDerivAt (frozenPathCovarianceError β α a s h z i j) (g₁ k) k ∧
        HasDerivAt g₁ (g₂ k) k ∧
        |frozenPathCovarianceError β α a s h z i j k| ≤ C * h ^ 3 ∧
        |g₁ k| ≤ C * h ^ 3 ∧ |g₂ k| ≤ C * h ^ 3 := by
  obtain ⟨M, δ, hM, hδ, _, hR⟩ := frozenCovarianceRemainder_uniform_bounds
  obtain ⟨η, hη, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  let T : ℝ := (β ^ 2 + 1) * (B + 1)
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨(β ^ 6 + 1) * (B ^ 2 + 1) * M, min η (δ / T), by positivity, by positivity, ?_⟩
  intro α a s h z ha hh hh₀ hχ i j
  let χ := jet β α 2 (s + 4 * h) z
  change |χ| ≤ B at hχ
  let t := a * β ^ 2 * χ * h
  let q := a ^ 2 * β ^ 6 * χ ^ 2 * h ^ 3
  let F : ℝ × ℝ → ℝ := fun x => frozenCovarianceRemainder x.1 x.2 i j
  have haq : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2
  have ht : |t| ≤ δ := by
    have H : |t| ≤ T * h := by
      dsimp only [t, T]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β), abs_of_nonneg hh]
      calc
        _ ≤ 1 * (β ^ 2 + 1) * (B + 1) * h := by gcongr <;> linarith [haq, hχ]
        _ = _ := by ring
    exact H.trans (by simpa only [mul_comm] using (le_div_iff₀ hT).mp (hh₀.trans (min_le_right _ _)))
  have he (k : ℝ) (hk : |k| ≤ 1 / 2) :
      frozenPathCovarianceError β α a s h z i j k = q * F (t, k) := by
    have hQ := hA α a s h k z ha hh (hh₀.trans (min_le_left _ _)) hk hχ
    have H := frozenSchedule_pathCovariance_expansion β a h k _ _ χ z (ne_of_gt ha.1) hh hk hQ i j
    change gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z) i j = _ at H
    dsimp only [frozenPathCovarianceError, q, F, t]
    rw [H]
    ring
  have hq : |q| ≤ (β ^ 6 + 1) * (B ^ 2 + 1) * h ^ 3 := by
    have ha₂ : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
    have hχ₂ : χ ^ 2 ≤ B ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hχ 2
    dsimp only [q]
    rw [abs_of_nonneg (by positivity : 0 ≤ a ^ 2 * β ^ 6 * χ ^ 2 * h ^ 3)]
    calc
      _ ≤ 1 * (β ^ 6 + 1) * (B ^ 2 + 1) * h ^ 3 := by gcongr <;> nlinarith [ha₂, hχ₂]
      _ = _ := by ring
  refine ⟨fun k => q * verticalDerivative F (t, k),
    fun k => q * verticalDerivative (verticalDerivative F) (t, k), ?_⟩
  intro k hk
  have hk' : |k| ≤ 1 / 2 := (abs_le.mpr hk).trans (by norm_num)
  have HR := hR i j t ht k hk'
  have hn : Icc (-(1 / 2) : ℝ) (1 / 2) ∈ 𝓝 k :=
    Icc_mem_nhds (by linarith [hk.1]) (by linarith [hk.2])
  have hnear : (fun k => q * F (t, k)) =ᶠ[𝓝 k] frozenPathCovarianceError β α a s h z i j := by
    filter_upwards [hn] with x hx
    exact (he x (abs_le.mpr hx)).symm
  have hb (x : ℝ) (hx : |x| ≤ M) : |q * x| ≤ (β ^ 6 + 1) * (B ^ 2 + 1) * M * h ^ 3 := by
    rw [abs_mul]
    calc
      _ ≤ ((β ^ 6 + 1) * (B ^ 2 + 1) * h ^ 3) * M := mul_le_mul hq hx (abs_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨(HR.2.2.2.1.const_mul q).congr_of_eventuallyEq hnear.symm,
    HR.2.2.2.2.const_mul q, ?_, hb _ HR.2.1, hb _ HR.2.2.1⟩
  rw [he k hk']
  exact hb _ HR.1

theorem gaussian_pow_integrable (n : ℕ) (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal m v) := by
  have hid : HasExpGrowth (fun x : ℝ => x) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  exact (hid.pow n).integrable_gaussianMeasure (by fun_prop)

def standardGaussianMomentValue : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1 : ℕ) * standardGaussianMomentValue n

theorem standardGaussian_integral_pow (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂gaussianReal 0 1) = standardGaussianMomentValue n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [standardGaussianMomentValue]
  | one => simpa only [pow_one, standardGaussianMomentValue] using (integral_id_gaussianReal (μ := (0 : ℝ)) (v := 1))
  | more n ih _ =>
    have hd (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ (n + 1)) ((n + 1 : ℕ) * x ^ n) x := by
      simpa only [Nat.add_sub_cancel] using hasDerivAt_pow (n + 1) x
    have hi : Integrable (fun x : ℝ => x * x ^ (n + 1)) (gaussianReal 0 1) := by
      simpa only [← pow_succ', Nat.add_assoc] using gaussian_pow_integrable (n + 2) 0 1
    have H := gaussian_integral_mul_eq_integral_deriv _ _ hd
      (gaussian_pow_integrable (n + 1) 0 1)
      ((gaussian_pow_integrable n 0 1).const_mul (n + 1 : ℕ)) hi
    simp only [← pow_succ', Nat.add_assoc, integral_const_mul, ih, standardGaussianMomentValue] at H ⊢
    exact H

theorem gaussian_integral_affine_pow (n : ℕ) (m σ : ℝ) :
    (∫ x : ℝ, (m + σ * x) ^ n ∂gaussianReal 0 1) =
      ∑ j ∈ Finset.range (n + 1), m ^ j * σ ^ (n - j) *
        standardGaussianMomentValue (n - j) * (n.choose j : ℝ) := by
  have he : (fun x : ℝ => (m + σ * x) ^ n) =
      fun x => ∑ j ∈ Finset.range (n + 1), (m ^ j * σ ^ (n - j) * (n.choose j : ℝ)) * x ^ (n - j) := by
    funext x
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, standardGaussian_integral_pow]
    ring
  · intro j _
    exact (gaussian_pow_integrable (n - j) 0 1).const_mul _

theorem gaussian_integral_affine_cube (m σ : ℝ) :
    (∫ x : ℝ, (m + σ * x) ^ 3 ∂gaussianReal 0 1) = m ^ 3 + 3 * m * σ ^ 2 := by
  rw [gaussian_integral_affine_pow]
  norm_num [Finset.sum_range_succ, standardGaussianMomentValue, Nat.choose]
  ring

theorem gaussian_integral_affine_fourth (m σ : ℝ) :
    (∫ x : ℝ, (m + σ * x) ^ 4 ∂gaussianReal 0 1) = m ^ 4 + 6 * m ^ 2 * σ ^ 2 + 3 * σ ^ 4 := by
  rw [gaussian_integral_affine_pow]
  norm_num [Finset.sum_range_succ, standardGaussianMomentValue, Nat.choose]
  ring

theorem gaussian_integral_affine_fifth (m σ : ℝ) :
    (∫ x : ℝ, (m + σ * x) ^ 5 ∂gaussianReal 0 1) = m ^ 5 + 10 * m ^ 3 * σ ^ 2 + 15 * m * σ ^ 4 := by
  rw [gaussian_integral_affine_pow]
  norm_num [Finset.sum_range_succ, standardGaussianMomentValue, Nat.choose]
  ring

theorem gaussian_integral_affine_sixth (m σ : ℝ) :
    (∫ x : ℝ, (m + σ * x) ^ 6 ∂gaussianReal 0 1) =
      m ^ 6 + 15 * m ^ 4 * σ ^ 2 + 45 * m ^ 2 * σ ^ 4 + 15 * σ ^ 6 := by
  rw [gaussian_integral_affine_pow]
  norm_num [Finset.sum_range_succ, standardGaussianMomentValue, Nat.choose]
  ring

theorem standardGaussian_integral_eighth : (∫ x : ℝ, x ^ 8 ∂gaussianReal 0 1) = 105 := by
  rw [standardGaussian_integral_pow]
  norm_num [standardGaussianMomentValue]

theorem gaussian_integral_centered_pow (n : ℕ) (m z : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - z) ^ n ∂gaussianReal m v) =
      ∫ x : ℝ, ((m - z) + Real.sqrt (v : ℝ) * x) ^ n ∂gaussianReal 0 1 := by
  have hv : NNReal.mk ((Real.sqrt (v : ℝ)) ^ 2) (sq_nonneg _) * 1 = v := by
    apply NNReal.eq
    simp only [NNReal.coe_mk, mul_one,
      Real.sq_sqrt (NNReal.coe_nonneg v)]
  have hZ : HasLaw (fun x : ℝ => m + Real.sqrt (v : ℝ) * x) (gaussianReal m v) (gaussianReal 0 1) := by
    simpa only [id_eq, mul_zero, zero_add, hv] using
      gaussianReal_const_add (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt (v : ℝ))) m
  rw [← hZ.integral_comp (by fun_prop : AEStronglyMeasurable (fun y : ℝ => (y - z) ^ n) (gaussianReal m v))]
  apply integral_congr_ae
  filter_upwards [] with x
  change (m + Real.sqrt (v : ℝ) * x - z) ^ n = ((m - z) + Real.sqrt (v : ℝ) * x) ^ n
  congr 1
  ring

theorem gaussian_integral_centered_cube (m z : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - z) ^ 3 ∂gaussianReal m v) = (m - z) ^ 3 + 3 * (m - z) * (v : ℝ) := by
  rw [gaussian_integral_centered_pow, gaussian_integral_affine_cube, Real.sq_sqrt (NNReal.coe_nonneg v)]

theorem gaussian_integral_centered_fourth (m z : ℝ) (v : ℝ≥0) :
    (∫ y : ℝ, (y - z) ^ 4 ∂gaussianReal m v) =
      (m - z) ^ 4 + 6 * (m - z) ^ 2 * (v : ℝ) + 3 * (v : ℝ) ^ 2 := by
  have hs : Real.sqrt (v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [gaussian_integral_centered_pow, gaussian_integral_affine_fourth,
    Real.sq_sqrt (NNReal.coe_nonneg v), hs]

theorem quadraticFirst_terminalCubicResidual (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ)
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (hl : RiccatiAdmissible l Q) (x : Vec3) :
    quadraticFirst l Q (terminalCubicResidual β α s h z) x =
      jet β α 3 (s + 4 * h) z / 6 * ∑ i : Fin 3,
        ((gaussianPathMean l Q x i - z) ^ 3 +
          3 * (gaussianPathMean l Q x i - z) * gaussianPathCovariance l Q i i) := by
  let w := jet β α 3 (s + 4 * h) z / 6
  let φ : ℝ → ℝ := fun y => w * (y - z) ^ 3
  have he : terminalCubicResidual β α s h z = fun y => ∑ i : Fin 3, φ (y i) := by
    funext y
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [terminalCubicResidual, φ, w]
    ring
  have hi (m : ℝ) (v : ℝ≥0) : Integrable φ (gaussianReal m v) := by
    have hid : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
    have H := (HasExpGrowth.const w).mul ((hid.sub_real (HasExpGrowth.const z)).pow 3)
    exact H.integrable_gaussianMeasure (by fun_prop)
  rw [he, quadraticFirst_separable l Q hl φ (by fun_prop) hi x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show φ = fun y => w * (y - z) ^ 3 from rfl, integral_const_mul, gaussian_integral_centered_cube,
    Real.toNNReal_of_nonneg (by
      simpa [gaussianPathVariance, Pi.single_apply] using
        gaussianPathVariance_nonneg l Q hl (Pi.single i 1))]
  rfl

theorem scalarData_pathCovarianceError_control {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ z : ℝ, ∀ i j : Fin 3, ∃ g₁ g₂ : ℝ → ℝ, ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        HasDerivAt (frozenPathCovarianceError β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z i j) (g₁ k) k ∧
        HasDerivAt g₁ (g₂ k) k ∧
        |frozenPathCovarianceError β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z i j k| ≤ C * h ^ 3 ∧
        |g₁ k| ≤ C * h ^ 3 ∧ |g₂ k| ≤ C * h ^ 3 := by
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨C, η, hC, hη, H⟩ := frozenPathCovarianceError_uniform_control β B hB
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  let v := min (l / 2) T
  have hv : 0 < v := lt_min (by positivity) hT
  refine ⟨C, min η (min (l / 2) ((D.q - u) / 3)), hC, by positivity, ?_⟩
  intro r hr h hh hh₀ z i j
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
  exact H _ _ (r - h) h z ha hh.le hhη
    ((scalarData_jet_le D (by norm_num) le_rfl ht z).trans (by
      dsimp only [B]
      linarith)) i j

theorem frozenCubicFirstMoment_formula (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)) :
    let u := jet β α 1 (s + 4 * h) z
    let χ := jet β α 2 (s + 4 * h) z
    let w := jet β α 3 (s + 4 * h) z
    let d := 4 * a * β ^ 2 * h * u / (1 - 4 * a * β ^ 2 * χ * h)
    quadraticFirst (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
      (terminalCubicResidual β α s h z) (fun _ => z) =
        w / 6 * (3 * d ^ 3 + 3 * d * (12 * β ^ 2 * h +
          a * β ^ 4 * χ * h ^ 2 * physicalNorm k +
          a ^ 2 * β ^ 6 * χ ^ 2 * h ^ 3 * matrixTrace (frozenCovarianceRemainder (a * β ^ 2 * χ * h) k))) := by
  dsimp only
  let χ := jet β α 2 (s + 4 * h) z
  let d := 4 * a * β ^ 2 * h * jet β α 1 (s + 4 * h) z / (1 - 4 * a * β ^ 2 * χ * h)
  rw [quadraticFirst_terminalCubicResidual β α s h z _ _ hl]
  have hm (i : Fin 3) : gaussianPathMean (frozenSchedule β a (1 / 2) h k)
      (terminalTaylorQuadratic β α s h z) (fun _ => z) i - z = d := by
    unfold terminalTaylorQuadratic at hl ⊢
    rw [frozenSchedule_pathMean β a h k _ _ _ z hh hk hl i]
    dsimp only [d, χ]
    ring
  simp_rw [hm]
  have hV : (∑ i : Fin 3, gaussianPathCovariance (frozenSchedule β a (1 / 2) h k)
        (terminalTaylorQuadratic β α s h z) i i) =
      12 * β ^ 2 * h + a * β ^ 4 * χ * h ^ 2 * physicalNorm k +
        a ^ 2 * β ^ 6 * χ ^ 2 * h ^ 3 * matrixTrace (frozenCovarianceRemainder (a * β ^ 2 * χ * h) k) := by
    unfold terminalTaylorQuadratic at hl ⊢
    simp_rw [frozenSchedule_pathVariance_expansion β a h k _ _ _ z ha hh hk hl]
    have H := frozenCovarianceQuadratic_trace k
    simp only [matrixTrace, Fin.sum_univ_succ] at H ⊢
    linear_combination (a * β ^ 4 * χ * h ^ 2) * H
  congr 1
  change (∑ i : Fin 3, (d ^ 3 + 3 * d * gaussianPathCovariance _ _ i i)) =
    3 * d ^ 3 + 3 * d * _
  simp only [Fin.sum_univ_succ] at hV ⊢
  linear_combination 3 * d * hV

def scalarCubicTail (β : ℝ) (α : ℝ → ℝ) (s h z y : ℝ) : ℝ :=
  scalarTerminalResidual β α s h z y - jet β α 3 (s + 4 * h) z * (y - z) ^ 3 / 6

theorem scalarCubicTail_eq (β : ℝ) (α : ℝ → ℝ) (s h z y : ℝ) :
    scalarCubicTail β α s h z y =
      Phi β α (s + 4 * h) y - scalarTaylorPolynomial (Phi β α (s + 4 * h)) 3 z y := by
  simp only [scalarCubicTail, scalarTerminalResidual, scalarTaylorPolynomial,
    Finset.sum_range_succ, Finset.sum_range_zero, jet, iteratedDeriv_zero,
    Nat.factorial, Nat.cast_mul, Nat.cast_one]
  ring

theorem scalarData_scalarCubicTail_le {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z y : ℝ) :
    |scalarCubicTail β (cdf (D.μ : Measure ℝ)) s h z y| ≤
      scalarTerminalJetBound D 4 / 24 * |y - z| ^ 4 := by
  rw [scalarCubicTail_eq]
  have H := scalarTaylorPolynomial_remainder_le (n := 3)
    ((scalarData_phi_contDiff D ht).of_le (by simp))
    (fun y => scalarData_jet_le D (by norm_num : 1 ≤ 4) le_rfl ht y) z y
  convert H using 1
  norm_num
  ring

theorem scalarData_scalarCubicTail_scaled_L2_le {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (z ρ : ℝ) :
    (∫ x : ℝ, scalarCubicTail β (cdf (D.μ : Measure ℝ)) s h z (z + ρ * x) ^ 2 ∂gaussianReal 0 1) ≤
      105 * (scalarTerminalJetBound D 4 / 24) ^ 2 * ρ ^ 8 := by
  let C := scalarTerminalJetBound D 4 / 24
  let e : ℝ → ℝ := fun x => scalarCubicTail β (cdf (D.μ : Measure ℝ)) s h z (z + ρ * x)
  have hC : 0 ≤ C := div_nonneg (scalarTerminalJetBound_nonneg D 4) (by norm_num)
  have hs (x : ℝ) : e x ^ 2 ≤ (C ^ 2 * ρ ^ 8) * x ^ 8 := by
    have H : |e x| ≤ C * |ρ * x| ^ 4 := by
      simpa only [e, C, add_sub_cancel_left] using scalarData_scalarCubicTail_le D ht z (z + ρ * x)
    calc
      _ = |e x| ^ 2 := (sq_abs _).symm
      _ ≤ (C * |ρ * x| ^ 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) H 2
      _ = C ^ 2 * |ρ * x| ^ 8 := by ring
      _ = C ^ 2 * (ρ * x) ^ 8 := by rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (ρ * x) ^ 8)]
      _ = _ := by ring
  have hp : Integrable (fun x : ℝ => (C ^ 2 * ρ ^ 8) * x ^ 8) (gaussianReal 0 1) :=
    (gaussian_pow_integrable 8 0 1).const_mul _
  have hc : Continuous e := by
    have hφ : Continuous (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) := (scalarData_phi_contDiff D ht).continuous
    unfold e scalarCubicTail scalarTerminalResidual
    fun_prop
  have hi : Integrable (fun x => e x ^ 2) (gaussianReal 0 1) := hp.mono' (hc.pow 2).aestronglyMeasurable
    (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (e x))]
      exact hs x))
  have H := integral_mono hi hp hs
  rw [integral_const_mul, standardGaussian_integral_eighth] at H
  change (∫ x, e x ^ 2 ∂gaussianReal 0 1) ≤ 105 * C ^ 2 * ρ ^ 8
  calc
    _ ≤ C ^ 2 * ρ ^ 8 * 105 := H
    _ = _ := by ring

theorem scalarData_scalarCubicTail_sqrt_L2_le {β : ℝ} (D : ScalarData β)
    {s h : ℝ} (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hh : 0 ≤ h) (z : ℝ) :
    (∫ x : ℝ, scalarCubicTail β (cdf (D.μ : Measure ℝ)) s h z (z + Real.sqrt h * x) ^ 2 ∂gaussianReal 0 1) ≤
      105 * (scalarTerminalJetBound D 4 / 24) ^ 2 * h ^ 4 := by
  have hs : Real.sqrt h ^ 8 = h ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hh]
  simpa only [hs] using scalarData_scalarCubicTail_scaled_L2_le D ht z (Real.sqrt h)

end SKBarriers2.Corner
