module

public import SKBarriers2.Corner.FrozenRowsPotential9
public import SKBarriers2.Corner.FrozenRowsPotential6
public import SKBarriers2.Corner.FrozenRowsPotential7

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

open SKOptimized.Overshoot

namespace SKBarriers2.Corner
open StepCalculus

attribute [local irreducible] frozenGeometryCoefficient

theorem frozenUnitMass_bounds (j : Fin 12) :
    (1 / 3 : ℝ) ≤ frozenUnitMass j ∧ frozenUnitMass j ≤ 1 := by
  fin_cases j <;> norm_num [frozenUnitMass]

set_option maxHeartbeats 0 in
theorem frozenCenteredModelPotential_uniform_kBounds (β a₀ B : ℝ)
    (ha₀ : 0 < a₀) (hB : 0 < B) :
    ∃ ρ₀ L : ℝ, 0 < ρ₀ ∧ 0 ≤ L ∧
      ∀ a ∈ Icc a₀ 1, ∀ u χ : ℝ, |u| ≤ B → |χ| ≤ B →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ f : Vec3 → ℝ, QPotential 5 B f →
      ∀ j : Fin 12, ∀ k ∈ frozenRowsKDomain, ∀ g : ℝ,
      let F := fun t => frozenCenteredModelPotential β a u χ ρ f j t g
      |deriv F k| ≤ L * (1 + g ^ 2) ∧ |deriv (deriv F) k| ≤ L * (1 + g ^ 2) := by
  obtain ⟨δC, C, hδC, hC, HC⟩ := frozenGeometry_uniform_coefficients β a₀ B ha₀
  obtain ⟨δD, hδD, HD⟩ := frozenGeometry_uniform_domain β a₀ B ha₀
  obtain ⟨M, δV, hM, hδV, HV⟩ := frozenCompletedDirection_uniform_control β
  let R := 3 / a₀
  obtain ⟨K₀, hK₀, HK₀⟩ := secondVariationBound_le_source (B := B + 1) (R := R)
    (by linarith : 0 ≤ B + 1) (by dsimp only [R]; positivity)
  let KT := tiltedStabilityCoefficient 3 (B + 1)
  let KM := massSensitivityJetCoefficient 2 (B + 1)
  let KD := directionSensitivityCoefficient 3 (B + 1)
  let K := 1 + K₀ + |KT| + |KM| + |KD|
  have hK : 0 < K := by dsimp only [K]; positivity
  have hK₀K : K₀ ≤ K := by dsimp only [K]; linarith [abs_nonneg KT, abs_nonneg KM, abs_nonneg KD]
  have hKT : KT ≤ K := by dsimp only [K]; linarith [le_abs_self KT, abs_nonneg KM, abs_nonneg KD]
  have hKM : KM ≤ K := by dsimp only [K]; linarith [le_abs_self KM, abs_nonneg KT, abs_nonneg KD]
  have hKD : KD ≤ K := by dsimp only [K]; linarith [le_abs_self KD, abs_nonneg KT, abs_nonneg KM]
  have hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : Vec3, secondVariationBound (B + 1) A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b := by
    intro A H m dm ddm hA hH hm hmR v w b
    apply (HK₀ A H m dm ddm hA hH hm hmR v w b).trans
    have hs : 0 ≤ secondVariationSource A dm ddm v w b := by
      dsimp only [secondVariationSource]
      positivity
    gcongr
  let S₀ := stepStabilityCoefficient 5 (B + 1) + 1
  have hS₀ : 0 < S₀ := by
    dsimp only [S₀]
    linarith [stepStabilityCoefficient_nonneg 5 (by linarith : 0 ≤ B + 1)]
  let S := 1 + M ^ 2 + 12 * M ^ 2 * S₀ + 24 * M ^ 2 * (B + 1)
  have hS : 0 < S := by dsimp only [S]; positivity
  let ρ₀ := min δC (min δD (min 1 (min (δV / (B + 1)) S⁻¹)))
  let A₀ := (B + 1) * (C + 1) ^ 2
  let LA := 4 * A₀ ^ 2 * (1 + 6 * K) ^ 24
  let L := 3 * C + LA
  have hρ₀ : 0 < ρ₀ := lt_min hδC (lt_min hδD (lt_min (by norm_num)
    (lt_min (by positivity) (inv_pos.mpr hS))))
  refine ⟨ρ₀, L, hρ₀, by dsimp only [L, LA]; positivity, ?_⟩
  intro a ha u χ hu hχ ρ hρ hρsmall f hf j k hk g
  let b : FrozenGeometryBase := (a, (u, χ))
  let p := fun t : ℝ => ((b, ρ), t)
  let U : Set ℝ := Ioo (-(1 / 2) : ℝ) (1 / 2)
  have hkU : k ∈ U := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hkC : k ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := ⟨hkU.1.le, hkU.2.le⟩
  have hb : b ∈ frozenGeometryBaseBox a₀ B := ⟨ha, abs_le.mp hu, abs_le.mp hχ⟩
  have hρC : ρ ∈ Icc (-δC) δC :=
    ⟨by linarith [hδC], hρsmall.trans (min_le_left _ _)⟩
  have hρD : ρ ∈ Icc (-δD) δD := by
    refine ⟨by linarith [hδD], ?_⟩
    exact (hρsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρ₁ : ρ ≤ 1 := by
    exact ((hρsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρV : ρ ≤ δV / (B + 1) := by
    exact (((hρsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_left _ _)
  have hρS : ρ ≤ S⁻¹ := by
    exact (((hρsmall.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  have hρ₂ : ρ ^ 2 ≤ ρ := by nlinarith
  have hSρ : S * ρ ≤ 1 := (mul_le_mul_of_nonneg_left hρS hS.le).trans_eq
    (mul_inv_cancel₀ hS.ne')
  have hscale : |a * χ * ρ ^ 2| ≤ δV := by
    have haabs : |a| ≤ 1 := by rw [abs_of_pos (ha₀.trans_le ha.1)]; exact ha.2
    have H := (le_div_iff₀ (by linarith : 0 < B + 1)).mp hρV
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ρ)]
    calc
      _ ≤ 1 * B * ρ ^ 2 := by gcongr
      _ = B * ρ ^ 2 := by ring
      _ ≤ B * ρ := mul_le_mul_of_nonneg_left hρ₂ hB.le
      _ ≤ δV := by nlinarith
  have hsqrt : Real.sqrt (ρ ^ 2) = ρ := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hρ]
  let F := fun i : Fin 9 => fun t => frozenGeometryCoefficient β j i (p t)
  let F₁ := fun i : Fin 9 => fun t => parameterVerticalDerivative (frozenGeometryCoefficient β j i) (p t)
  let F₂ := fun i : Fin 9 => fun t => parameterVerticalDerivative
    (parameterVerticalDerivative (frozenGeometryCoefficient β j i)) (p t)
  have Hcoeff (t : ℝ) (ht : t ∈ U) (i : Fin 9) :=
    HC b hb ρ hρC t ⟨ht.1.le, ht.2.le⟩ j i
  have hFc (i : Fin 9) : ContDiffAt ℝ 2 (F i) k := by
    have H := (frozenGeometryCoefficient_contDiffOn β j i).contDiffAt
      ((frozenGeometryDomain_isOpen β).mem_nhds (HD b hb ρ hρD k hkC))
    exact (H.comp k (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)
  let X := fun t => frozenGeometryMeanVector β j (p t) + g • frozenGeometryLinearVector β j (p t)
  let X₁ := fun t => fun i : Fin 3 =>
    F₁ ⟨3 + i.val, by omega⟩ t + g * F₁ ⟨6 + i.val, by omega⟩ t
  let X₂ := fun t => fun i : Fin 3 =>
    F₂ ⟨3 + i.val, by omega⟩ t + g * F₂ ⟨6 + i.val, by omega⟩ t
  have hXc : ContDiffAt ℝ 2 X k := by
    apply contDiffAt_pi.mpr
    intro i
    exact (hFc ⟨3 + i.val, by omega⟩).add (contDiffAt_const.mul (hFc ⟨6 + i.val, by omega⟩))
  have hXjets (t : ℝ) (ht : t ∈ U) :
      HasDerivAt X (X₁ t) t ∧ HasDerivAt X₁ (X₂ t) t := by
    constructor
    · apply hasDerivAt_pi.mpr
      intro i
      exact (Hcoeff t ht ⟨3 + i.val, by omega⟩).2.2.2.1.add
        ((Hcoeff t ht ⟨6 + i.val, by omega⟩).2.2.2.1.const_mul g)
    · apply hasDerivAt_pi.mpr
      intro i
      exact (Hcoeff t ht ⟨3 + i.val, by omega⟩).2.2.2.2.add
        ((Hcoeff t ht ⟨6 + i.val, by omega⟩).2.2.2.2.const_mul g)
  have hXd := curve_derivatives_of_twoJets isOpen_Ioo hXjets hkU
  have hvec (q : Fin 9 → ℝ) (hq : ∀ i, |q i| ≤ C) :
      ‖fun i : Fin 3 => q ⟨3 + i.val, by omega⟩ + g * q ⟨6 + i.val, by omega⟩‖ ≤ C * (1 + |g|) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ C * (1 + |g|))).mpr
    intro i
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |q ⟨3 + i.val, by omega⟩| + |g * q ⟨6 + i.val, by omega⟩| := abs_add_le _ _
      _ ≤ C + |g| * C := by rw [abs_mul]; gcongr; exact hq _; exact hq _
      _ = _ := by ring
  have hX₁ : ‖deriv X k‖ ≤ C * (1 + |g|) := by
    rw [hXd.1]
    exact hvec (fun i => F₁ i k) (fun i => (Hcoeff k hkU i).2.1)
  have hX₂ : ‖deriv (deriv X) k‖ ≤ C * (1 + |g|) := by
    rw [hXd.2]
    exact hvec (fun i => F₂ i k) (fun i => (Hcoeff k hkU i).2.2.1)
  let P := fun t => F 0 t + F 1 t * g + F 2 t * g ^ 2
  let P₁ := fun t => F₁ 0 t + F₁ 1 t * g + F₁ 2 t * g ^ 2
  let P₂ := fun t => F₂ 0 t + F₂ 1 t * g + F₂ 2 t * g ^ 2
  have hPc : ContDiffAt ℝ 2 P k := ((hFc 0).add ((hFc 1).mul contDiffAt_const)).add ((hFc 2).mul contDiffAt_const)
  have hPjets (t : ℝ) (ht : t ∈ U) : HasDerivAt P (P₁ t) t ∧ HasDerivAt P₁ (P₂ t) t := by
    exact ⟨(((Hcoeff t ht 0).2.2.2.1).add ((Hcoeff t ht 1).2.2.2.1.mul_const g)).add
        ((Hcoeff t ht 2).2.2.2.1.mul_const (g ^ 2)),
      (((Hcoeff t ht 0).2.2.2.2).add ((Hcoeff t ht 1).2.2.2.2.mul_const g)).add
        ((Hcoeff t ht 2).2.2.2.2.mul_const (g ^ 2))⟩
  have hPd := curve_derivatives_of_twoJets isOpen_Ioo hPjets hkU
  have hP₁ : |deriv P k| ≤ 3 * C * (1 + g ^ 2) := by
    rw [hPd.1]
    exact abs_quadratic_polynomial_le hC.le (Hcoeff k hkU 0).2.1
      (Hcoeff k hkU 1).2.1 (Hcoeff k hkU 2).2.1
  have hP₂ : |deriv (deriv P) k| ≤ 3 * C * (1 + g ^ 2) := by
    rw [hPd.2]
    exact abs_quadratic_polynomial_le hC.le (Hcoeff k hkU 0).2.2.1
      (Hcoeff k hkU 1).2.2.1 (Hcoeff k hkU 2).2.2.1
  let n := 12 - (j.val + 1)
  let q : Fin n → Fin 12 := fun i => ⟨j.val + 1 + i.val, by dsimp only [n] at i; omega⟩
  let m := fun i : Fin n => a * frozenUnitMass (q i)
  let V := fun t => fun i : Fin n => frozenCompletedDirection β a χ (ρ ^ 2) (q i) t
  let V₁ := fun t => fun i : Fin n => frozenCompletedDirectionFirst β a χ (ρ ^ 2) (q i) t
  let V₂ := fun t => fun i : Fin n => frozenCompletedDirectionSecond β a χ (ρ ^ 2) (q i) t
  have Hdir (t : ℝ) (ht : t ∈ U) (i : Fin n) := HV a χ (ρ ^ 2) t hscale
    (abs_le.mpr ⟨ht.1.le, ht.2.le⟩) (q i)
  have hVjets (t : ℝ) (ht : t ∈ U) : HasDerivAt V (V₁ t) t ∧ HasDerivAt V₁ (V₂ t) t :=
    ⟨hasDerivAt_pi.mpr (fun i => (Hdir t ht i).2.2.2.1),
      hasDerivAt_pi.mpr (fun i => (Hdir t ht i).2.2.2.2.1)⟩
  have hVd := curve_derivatives_of_twoJets isOpen_Ioo hVjets hkU
  have hVc : ContDiffAt ℝ 2 V k := contDiffAt_pi.mpr (fun i => (Hdir k hkU i).2.2.2.2.2)
  have hVB (i : Fin n) : ‖V k i‖ ≤ M * ρ ∧ ‖deriv V k i‖ ≤ M * ρ ∧
      ‖deriv (deriv V) k i‖ ≤ M * ρ := by
    rw [hVd.1, hVd.2]
    simpa only [hsqrt] using
      And.intro (Hdir k hkU i).1 (And.intro (Hdir k hkU i).2.1 (Hdir k hkU i).2.2.1)
  have hMρ : M * ρ ≤ 1 := by
    have hMS : M ^ 2 ≤ S := by
      dsimp only [S]
      nlinarith [mul_nonneg (by positivity : 0 ≤ 12 * M ^ 2) hS₀.le,
        mul_nonneg (by positivity : 0 ≤ 24 * M ^ 2) (by linarith : 0 ≤ B + 1)]
    have H := (mul_le_mul_of_nonneg_right hMS hρ.le).trans hSρ
    have HH := mul_le_mul_of_nonneg_left hρ₂ (sq_nonneg M)
    nlinarith [mul_nonneg hM.le hρ.le]
  let E := StepCalculus.chainEnergy (List.ofFn (fun i : Fin n => (m i, V k i)))
  have hE : E ≤ 12 * M ^ 2 * ρ := by
    have hsum : E ≤ (n : ℝ) * (M * ρ) ^ 2 := by
      simp only [E, StepCalculus.chainEnergy, List.map_ofFn, List.sum_ofFn]
      calc
        _ ≤ ∑ _ : Fin n, (M * ρ) ^ 2 := Finset.sum_le_sum (fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hVB i).1 2)
        _ = _ := by simp
    calc
      _ ≤ (n : ℝ) * (M * ρ) ^ 2 := hsum
      _ ≤ 12 * (M * ρ) ^ 2 := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (Nat.sub_le 12 (j.val + 1))) (sq_nonneg _)
      _ = 12 * M ^ 2 * ρ ^ 2 := by ring
      _ ≤ 12 * M ^ 2 * ρ := mul_le_mul_of_nonneg_left hρ₂ (by positivity)
  have hbudget : S₀ * E ≤ 1 := by
    have hES : 12 * M ^ 2 * S₀ ≤ S := by
      dsimp only [S]
      nlinarith [sq_nonneg M,
        mul_nonneg (by positivity : 0 ≤ 24 * M ^ 2) (by linarith : 0 ≤ B + 1)]
    calc
      _ ≤ S₀ * (12 * M ^ 2 * ρ) := mul_le_mul_of_nonneg_left hE hS₀.le
      _ = (12 * M ^ 2 * S₀) * ρ := by ring
      _ ≤ S * ρ := mul_le_mul_of_nonneg_right hES hρ.le
      _ ≤ 1 := hSρ
  have hcurv : (B + 1) * E ≤ 1 / 2 := by
    have hES : 24 * M ^ 2 * (B + 1) ≤ S := by
      dsimp only [S]
      nlinarith [sq_nonneg M, mul_nonneg (by positivity : 0 ≤ 12 * M ^ 2) hS₀.le]
    have H := (mul_le_mul_of_nonneg_right hES hρ.le).trans hSρ
    have HE := mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ B + 1)
    nlinarith
  have hgeo (i : Fin n) : ‖V k i‖ ≤ 1 ∧ ‖deriv V k i‖ ≤ 1 ∧
      ‖deriv (deriv V) k i‖ ≤ 1 ∧ (B + 1) * ‖V k i‖ ^ 2 ≤ 1 / 2 := by
    have hi : ‖V k i‖ ^ 2 ≤ E := by
      dsimp only [E, StepCalculus.chainEnergy]
      simp only [List.map_ofFn, List.sum_ofFn]
      exact Finset.single_le_sum (fun j _ => sq_nonneg ‖V k j‖) (Finset.mem_univ i)
    exact ⟨(hVB i).1.trans hMρ, (hVB i).2.1.trans hMρ, (hVB i).2.2.trans hMρ,
      (mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ B + 1)).trans hcurv⟩
  have hm (i : Fin n) : 0 < m i ∧ m i ≤ 1 ∧ (m i)⁻¹ ≤ R := by
    have hunit := frozenUnitMass_bounds (q i)
    have hapos : 0 < a := ha₀.trans_le ha.1
    have hpos : 0 < m i := mul_pos hapos (by linarith : 0 < frozenUnitMass (q i))
    have hlower : a₀ / 3 ≤ m i := by
      have H := mul_le_mul ha.1 hunit.1 (by norm_num : (0 : ℝ) ≤ 1 / 3) hapos.le
      dsimp only [m]
      nlinarith
    refine ⟨hpos, (mul_le_mul ha.2 hunit.2 (by linarith) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring), ?_⟩
    have H := inv_anti₀ (by positivity : 0 < a₀ / 3) hlower
    have he : (a₀ / 3)⁻¹ = R := by dsimp only [R]; field_simp
    exact H.trans_eq he
  let A := fun t => vectorIncrementChain (List.ofFn (fun i : Fin n => (m i, V t i))) f (X t)
  have hAc := fixedMassChain_moving_endpoint_contDiffAt m hf hVc hXc (fun i => (hm i).1)
  have Hchain := fixedMassChain_moving_endpoint_jets m hf hVc hXc hm hK.le hKT hKM hKD
    hsource hgeo hbudget hcurv
  have Hweights := moving_endpoint_budgets_quadratic hB.le hC.le hK.le
    (by dsimp only [n]; omega : n ≤ 12) (norm_nonneg (deriv X k))
    (norm_nonneg (deriv (deriv X) k)) hX₁ hX₂
  have hA₁ : |deriv A k| ≤ LA * (1 + g ^ 2) := by
    have H := Hchain.1.norm_le 0
    simp only [zero_add, Real.norm_eq_abs] at H
    exact H.trans Hweights.1
  have hA₂ : |deriv (deriv A) k| ≤ LA * (1 + g ^ 2) := by
    have H := Hchain.2.norm_le 0
    simp only [zero_add, Real.norm_eq_abs] at H
    exact H.trans Hweights.2
  have hmodel : (fun t => frozenCenteredModelPotential β a u χ ρ f j t g) =
      fun t => P t + A t := by
    funext t
    exact frozenCenteredModelPotential_eq_coefficients β a u χ ρ hρ.le f j t g
  have hPA₁ : deriv (fun t => P t + A t) k = deriv P k + deriv A k := by
    have H := (((hPc.differentiableAt (by norm_num)).hasDerivAt).add
      ((hAc.differentiableAt (by norm_num)).hasDerivAt)).deriv
    have he : P + A = fun t => P t + A t := by funext t; rfl
    rw [he] at H
    exact H
  constructor
  · rw [hmodel, hPA₁]
    exact ((abs_add_le _ _).trans (add_le_add hP₁ hA₁)).trans_eq ((add_mul (3 * C) LA (1 + g ^ 2)).symm)
  · have hnear : deriv (fun t => P t + A t) =ᶠ[𝓝 k] fun t => deriv P t + deriv A t := by
      filter_upwards [hPc.eventually (by norm_num), hAc.eventually (by norm_num)] with t ht hs
      exact deriv_fun_add (ht.differentiableAt (by norm_num)) (hs.differentiableAt (by norm_num))
    have hPA₂ : deriv (fun t => deriv P t + deriv A t) k =
        deriv (deriv P) k + deriv (deriv A) k := by
      have H := ((((hPc.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt).add
        (((hAc.derivWithin (m := 1) (by norm_num)).differentiableAt
          (by norm_num)).hasDerivAt)).deriv
      have he : deriv P + deriv A = fun t => deriv P t + deriv A t := by funext t; rfl
      rw [he] at H
      exact H
    rw [hmodel, hnear.deriv_eq, hPA₂]
    exact ((abs_add_le _ _).trans (add_le_add hP₂ hA₂)).trans_eq ((add_mul (3 * C) LA (1 + g ^ 2)).symm)

end SKBarriers2.Corner
