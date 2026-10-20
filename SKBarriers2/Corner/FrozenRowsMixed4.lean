module

public import SKBarriers2.Corner.FrozenRowsMixedCore
public import SKBarriers2.Corner.FrozenRowsScaled

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem scaledTaylorTail_wQ_global {f : ℝ → ℝ} {B ρ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (r : ℕ) (hb : ∀ a, 2 ≤ a → a ≤ max 2 r → ∀ x, |iteratedDeriv a f x| ≤ B)
    (z : ℝ) : WQ r (2 * B * ρ⁻¹) 1 (scaledTaylorTail f z ρ) := by
  have hρ₀ := hρ.1.le
  have hρne := hρ.1.ne'
  have hfirst (x : ℝ) : |quadraticTaylorTailFirst f z x| ≤ 2 * B * |x - z| := by
    have hLip := Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℝ) (f := deriv f) (s := (univ : Set ℝ))
      (fun y _ => (contDiff_deriv_infty hf).differentiable (by simp) y)
      (fun y _ => by simpa only [Real.norm_eq_abs, iteratedDeriv_succ, iteratedDeriv_zero] using hb 2 le_rfl (le_max_left _ _) y)
      convex_univ (mem_univ z) (mem_univ x)
    have he : quadraticTaylorTailFirst f z x =
        (deriv f x - deriv f z) - iteratedDeriv 2 f z * (x - z) := by
      simp [quadraticTaylorTailFirst, scalarTaylorPolynomial, Finset.sum_range_succ,
        iteratedDeriv_succ, iteratedDeriv_zero]
      ring
    rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have H := hb 2 le_rfl (le_max_left _ _) z
    change |deriv f x - deriv f z| ≤ B * |x - z| at hLip
    nlinarith [mul_le_mul_of_nonneg_right H (abs_nonneg (x - z))]
  have hsecond (x : ℝ) : |quadraticTaylorTailSecond f z x| ≤ 2 * B := by
    have he : quadraticTaylorTailSecond f z x = iteratedDeriv 2 f x - iteratedDeriv 2 f z := by
      simp [quadraticTaylorTailSecond, scalarTaylorPolynomial, iteratedDeriv_succ, iteratedDeriv_zero]
    rw [he]
    exact (abs_sub _ _).trans ((add_le_add
      (hb 2 le_rfl (le_max_left _ _) x) (hb 2 le_rfl (le_max_left _ _) z)).trans_eq (by ring))
  refine ⟨by positivity, (scaledTaylorTail_contDiff hf z ρ).of_le (by simp), ?_⟩
  intro j hj hjr y
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    iteratedDeriv_scaledTaylorTail hf, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hρ₀ _))]
  have hpre : |ρ ^ j * quadraticResidualSpatialJet f z j (ρ * y + z)| ≤
      (2 * B * ρ ^ 2) * (1 + |y|) := by
    cases j with
    | zero => omega
    | succ j =>
      cases j with
      | zero =>
        change |ρ ^ 1 * quadraticTaylorTailFirst f z (ρ * y + z)| ≤ _
        rw [pow_one, abs_mul, abs_of_nonneg hρ₀]
        apply (mul_le_mul_of_nonneg_left (hfirst _) hρ₀).trans
        rw [add_sub_cancel_right, abs_mul, abs_of_nonneg hρ₀]
        nlinarith [mul_nonneg hB (sq_nonneg ρ)]
      | succ j =>
        cases j with
        | zero =>
          change |ρ ^ 2 * quadraticTaylorTailSecond f z (ρ * y + z)| ≤ _
          rw [abs_mul, abs_of_nonneg (sq_nonneg ρ)]
          apply (mul_le_mul_of_nonneg_left (hsecond _) (sq_nonneg ρ)).trans
          nlinarith [mul_nonneg hB (sq_nonneg ρ), abs_nonneg y]
        | succ j =>
          change |ρ ^ (j + 3) * iteratedDeriv (j + 3) f (ρ * y + z)| ≤ _
          rw [abs_mul, abs_of_nonneg (pow_nonneg hρ₀ _)]
          calc
            _ ≤ ρ ^ (j + 3) * B := mul_le_mul_of_nonneg_left
              (hb _ (by omega) (hjr.trans (le_max_right _ _)) _) (pow_nonneg hρ₀ _)
            _ ≤ ρ ^ 2 * B := mul_le_mul_of_nonneg_right
              (pow_le_pow_of_le_one hρ₀ hρ.2 (by omega)) hB
            _ ≤ _ := by nlinarith [mul_nonneg hB (sq_nonneg ρ), abs_nonneg y]
  calc
    _ ≤ (ρ ^ 3)⁻¹ * ((2 * B * ρ ^ 2) * (1 + |y|)) :=
      mul_le_mul_of_nonneg_left hpre (inv_nonneg.mpr (pow_nonneg hρ₀ _))
    _ = (2 * B * ρ⁻¹) * (1 + ‖y‖) ^ 1 := by
      rw [Real.norm_eq_abs, pow_one]
      field_simp

theorem scalarData_scaledTerminalResidual_wQ_global {β s h ρ : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (r : ℕ) (z : ℝ) :
    WQ r (6 * scalarTerminalJetBound D (max 2 r) * ρ⁻¹) 1
      (scaledTerminalResidual β (cdf (D.μ : Measure ℝ)) s h z ρ) := by
  rw [scaledTerminalResidual_eq_sum]
  let B := scalarTerminalJetBound D (max 2 r)
  have H := scaledTaylorTail_wQ_global (scalarData_phi_contDiff D ht)
    (scalarTerminalJetBound_nonneg D _) hρ r
    (fun a ha har x => scalarData_jet_le D (by omega) har ht x) z
  have hs (i : Fin 3) : ContDiff ℝ r
      (fun y : Vec3 => scaledTaylorTail (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z ρ (y i)) :=
    H.smooth.comp (tripleCoordinate i).contDiff
  refine ⟨by positivity [hρ.1.le, scalarTerminalJetBound_nonneg D (max 2 r)],
    ContDiff.sum (fun i _ => hs i), ?_⟩
  intro j hj hjr y
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hs i).of_le (by exact_mod_cast hjr)).contDiffAt)]
  calc
    _ ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ j
        (fun y : Vec3 => scaledTaylorTail (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z ρ (y i)) y‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, (2 * B * ρ⁻¹) * (1 + ‖y‖) ^ 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_iteratedFDeriv_coordinate_le H.smooth hjr i y).trans
      have Hb := H.bound j hj hjr (y i)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at Hb
      exact Hb.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_le_pi_norm y i) 1) 1) H.nonneg)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      dsimp only [B]
      ring

end SKBarriers2.Corner
