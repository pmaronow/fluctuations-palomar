module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Coverage.FiniteRateAsymptotic

@[expose] public section

/-! The upstream mean rate and the scales used by the strengthened barrier.
No all-lean scalar or fluctuation results are imported. -/

noncomputable section
open scoped Topology
open Filter Asymptotics OAI.SK.Analytic

namespace SKBarriers2

/-- The unconditional upstream rate, in the frozen interface convention. -/
theorem exists_meanRate_upstream {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ MeanRate β (1 / 24) C := by
  obtain ⟨C, hC, hrate⟩ := quenchedPressure_quantitative_finiteInf hβ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrate] with n hn
  have hexp : (-(1 : ℝ) / 24) = -(1 / 24 : ℝ) := by ring
  rw [hexp] at hn
  linarith [hn.1]

def rateRho (R γ : ℝ) (n : ℕ) : ℝ := R * (n : ℝ) ^ (-γ / 3)
def rateEta (θ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-θ)
def rateLength (A γ : ℝ) (n : ℕ) : ℝ := A * (n : ℝ) ^ (γ / 3)

/-- These are exactly the strict exponent conditions in the scale choice. -/
structure RateExponents (γ θ : ℝ) : Prop where
  gamma_pos : 0 < γ
  gamma_lt : γ < 3 / 4
  theta_lower : γ / 3 < θ
  theta_half : θ < γ / 2
  theta_quarter : θ < 1 / 4

theorem exists_rateExponents {γ : ℝ} (hγ : 0 < γ) (hγ' : γ < 3 / 4) :
    ∃ θ : ℝ, RateExponents γ θ := by
  have hlt : γ / 3 < min (γ / 2) (1 / 4) := lt_min (by linarith) (by linarith)
  obtain ⟨θ, hθ, hθ'⟩ := exists_between hlt
  exact ⟨θ, hγ, hγ', hθ, hθ'.trans_le (min_le_left _ _),
    hθ'.trans_le (min_le_right _ _)⟩

private theorem nat_power_tendsto_zero {p : ℝ} (hp : p < 0) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop (𝓝 0) := by
  simpa only [neg_neg, Function.comp_def] using
    (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem nat_power_tendsto_top {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ p) atTop atTop := by
  exact (tendsto_rpow_atTop hp).comp (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem monomial_littleO (c d p q : ℝ) (hd : d ≠ 0) (hpq : p < q) :
    (fun n : ℕ => c * (n : ℝ) ^ p) =o[atTop]
      (fun n : ℕ => d * (n : ℝ) ^ q) := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    exact fun h => False.elim ((mul_ne_zero hd (Real.rpow_pos_of_pos hn' q).ne') h)
  · have ht := (nat_power_tendsto_zero (sub_neg.mpr hpq)).const_mul (c / d)
    simpa only [mul_zero] using ht.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      rw [Real.rpow_sub (Nat.cast_pos.mpr hn)]
      exact div_mul_div_comm c d _ _)

/-- Both shrinking scales vanish. -/
theorem rate_scales_tendsto_zero {γ θ : ℝ} (h : RateExponents γ θ) (R : ℝ) :
    Tendsto (rateRho R γ) atTop (𝓝 0) ∧ Tendsto (rateEta θ) atTop (𝓝 0) := by
  constructor
  · change Tendsto (fun n : ℕ => R * (n : ℝ) ^ (-γ / 3)) atTop (𝓝 0)
    simpa only [mul_zero] using
      (nat_power_tendsto_zero (show -γ / 3 < 0 by linarith [h.gamma_pos])).const_mul R
  · exact nat_power_tendsto_zero (by linarith [h.gamma_pos, h.theta_lower])

private theorem n_rho_cube (R γ : ℝ) (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * rateRho R γ n ^ 3 = R ^ 3 * (n : ℝ) ^ (1 - γ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [rateRho, mul_pow]
  rw [show ((n : ℝ) ^ (-γ / 3)) ^ 3 = (n : ℝ) ^ (-γ) by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    congr 1
    norm_num]
  rw [Real.rpow_sub hn', Real.rpow_one]
  rw [Real.rpow_neg hn'.le]
  ring

private theorem n_eta_pow (θ : ℝ) (k n : ℕ) (hn : 0 < n) :
    (n : ℝ) * rateEta θ n ^ k = (n : ℝ) ^ (1 - k * θ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [rateEta, ← Real.rpow_natCast, ← Real.rpow_mul hn'.le,
    show -θ * (k : ℝ) = -((k : ℝ) * θ) by ring,
    Real.rpow_sub hn', Real.rpow_one, Real.rpow_neg hn'.le]
  ring

theorem rate_n_rho_cube_tendsto {γ θ R : ℝ} (h : RateExponents γ θ) (hR : 0 < R) :
    Tendsto (fun n : ℕ => (n : ℝ) * rateRho R γ n ^ 3) atTop atTop := by
  have ht := (nat_power_tendsto_top (show 0 < 1 - γ by linarith [h.gamma_lt])).const_mul_atTop (pow_pos hR 3)
  exact ht.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (n_rho_cube R γ n hn).symm)

theorem rate_n_eta_square_tendsto {γ θ : ℝ} (h : RateExponents γ θ) :
    Tendsto (fun n : ℕ => (n : ℝ) * rateEta θ n ^ 2) atTop atTop := by
  have ht := nat_power_tendsto_top (show 0 < 1 - (2 : ℝ) * θ by linarith [h.theta_quarter])
  exact ht.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (n_eta_pow θ 2 n hn).symm)

/-- The stronger precision inequality needed for a Gaussian numerator bound. -/
theorem rate_n_eta_fourth_tendsto {γ θ : ℝ} (h : RateExponents γ θ) :
    Tendsto (fun n : ℕ => (n : ℝ) * rateEta θ n ^ 4) atTop atTop := by
  have ht := nat_power_tendsto_top (show 0 < 1 - (4 : ℝ) * θ by linarith [h.theta_quarter])
  exact ht.congr' (by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (n_eta_pow θ 4 n hn).symm)

theorem rate_length_tendsto {γ θ A : ℝ} (h : RateExponents γ θ) (hA : 0 < A) :
    Tendsto (rateLength A γ) atTop atTop := by
  exact (nat_power_tendsto_top (show 0 < γ / 3 by linarith [h.gamma_pos])).const_mul_atTop hA

theorem rate_length_littleO_n {γ θ : ℝ} (h : RateExponents γ θ) (A : ℝ) :
    rateLength A γ =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  change (fun n : ℕ => A * (n : ℝ) ^ (γ / 3)) =o[atTop] (fun n : ℕ => (n : ℝ))
  simpa only [one_mul, Real.rpow_one] using
    monomial_littleO A 1 (γ / 3) 1 one_ne_zero (by linarith [h.gamma_lt])

theorem rate_eta_littleO_rho {γ θ R : ℝ} (h : RateExponents γ θ) (hR : R ≠ 0) :
    rateEta θ =o[atTop] rateRho R γ := by
  change (fun n : ℕ => (n : ℝ) ^ (-θ)) =o[atTop]
    (fun n : ℕ => R * (n : ℝ) ^ (-γ / 3))
  simpa only [one_mul] using
    monomial_littleO 1 R (-θ) (-γ / 3) hR (by linarith [h.theta_lower])

/-- Mean pressure bias is negligible at the pair precision. -/
theorem rate_bias_littleO_eta_square {γ θ : ℝ} (h : RateExponents γ θ) :
    (fun n : ℕ => (n : ℝ) ^ (-γ)) =o[atTop] (fun n => rateEta θ n ^ 2) := by
  have ht := monomial_littleO 1 1 (-γ) (-2 * θ) one_ne_zero (by linarith [h.theta_half])
  convert ht using 1
  · simp only [one_mul]
  · funext n
    rw [rateEta, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    simp only [one_mul]
    congr 1
    norm_num
    ring

/-- The bank length is negligible compared with the local exponential deficit. -/
theorem rate_length_littleO_n_rho_cube {γ θ R : ℝ} (h : RateExponents γ θ)
    (hR : R ≠ 0) (A : ℝ) :
    rateLength A γ =o[atTop] (fun n : ℕ => (n : ℝ) * rateRho R γ n ^ 3) := by
  apply (monomial_littleO A (R ^ 3) (γ / 3) (1 - γ) (pow_ne_zero _ hR)
    (by linarith [h.gamma_lt])).congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (n_rho_cube R γ n hn).symm

theorem rate_length_littleO_n_eta_square {γ θ : ℝ} (h : RateExponents γ θ) (A : ℝ) :
    rateLength A γ =o[atTop] (fun n : ℕ => (n : ℝ) * rateEta θ n ^ 2) := by
  apply (monomial_littleO A 1 (γ / 3) (1 - 2 * θ) one_ne_zero
    (by linarith [h.gamma_lt, h.theta_quarter])).congr'
    (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simpa only [one_mul, Nat.cast_ofNat] using (n_eta_pow θ 2 n hn).symm

end SKBarriers2
