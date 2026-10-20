module

public import SKBarriers2.Corner.FrozenRowsPotential21

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set Filter OAI.SK.Analytic
namespace SKBarriers2.Corner
local notation "V3" => (Fin 3 → ℝ)

theorem affine_endpoint_normalized_small_score_geometry
    {A : ℝ → V3 →L[ℝ] V3} {b c v : ℝ → V3} {k ρ C D : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hA : ContDiffAt ℝ 2 A k) (hb : ContDiffAt ℝ 2 b k)
    (hc : ContDiffAt ℝ 2 c k) (hv : ContDiffAt ℝ 2 v k)
    (hA₀ : ‖A k‖ ≤ C) (hA₁ : ‖deriv A k‖ ≤ C * ρ ^ 2)
    (hA₂ : ‖deriv (deriv A) k‖ ≤ C * ρ ^ 2)
    (hb₁ : ‖deriv b k‖ ≤ C) (hb₂ : ‖deriv (deriv b) k‖ ≤ C)
    (hv₁ : ‖deriv v k‖ ≤ C) (hv₂ : ‖deriv (deriv v) k‖ ≤ C)
    (hc₀ : ‖c k‖ ≤ D) (hc₁ : ‖deriv c k‖ ≤ D) (hc₂ : ‖deriv (deriv c) k‖ ≤ D)
    (g : ℝ) :
    let W := 1 + |g|
    let σ := ρ / W
    let δ := ρ ^ 3 / W
    let X := fun κ t y => A κ y + b κ + g • A κ (c κ) + t • v κ
    ∃ u₀ a₀ : ℝ → V3, ∃ U V : V3 →L[ℝ] V3,
      ContDiff ℝ ∞ u₀ ∧ ContDiff ℝ ∞ a₀ ∧
      ‖A k‖ ≤ C ∧ ‖U‖ ≤ C ∧ ‖V‖ ≤ C ∧
      (∀ t, ‖u₀ t‖ ≤ (2 * C + 4 * C * D) * (1 + |t|) ∧
        ‖a₀ t‖ ≤ (2 * C + 4 * C * D) * (1 + |t|)) ∧
      (∀ t y, ContDiffAt ℝ 2 (fun κ => X κ t y) k) ∧
      (∀ t y, σ • deriv (fun κ => X κ t y) k = u₀ t + δ • U y) ∧
      (∀ t y, σ ^ 2 • deriv (deriv (fun κ => X κ t y)) k = a₀ t + δ • V y) := by
  let W := 1 + |g|
  let σ := ρ / W
  let δ := ρ ^ 3 / W
  let d₁ := deriv A k (c k) + A k (deriv c k)
  let d₂ := deriv (deriv A) k (c k) + (2 : ℝ) • deriv A k (deriv c k) + A k (deriv (deriv c) k)
  let u₀ := fun t : ℝ => σ • (deriv b k + g • d₁ + t • deriv v k)
  let a₀ := fun t : ℝ => σ ^ 2 • (deriv (deriv b) k + g • d₂ + t • deriv (deriv v) k)
  let U := (ρ^2)⁻¹ • deriv A k
  let V := W⁻¹ • (ρ⁻¹ • deriv (deriv A) k)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hW₁ : 1 ≤ W := by dsimp only [W]; linarith [abs_nonneg g]
  have hσ : 0 ≤ σ := (div_pos hρ hW).le
  have hσ₁ : σ ≤ 1 := (div_le_one₀ hW).mpr (hρ₁.trans hW₁)
  have hσg : σ * |g| ≤ 1 := by
    rw [show σ * |g| = ρ * |g| / W by dsimp only [σ]; ring]
    apply (div_le_one₀ hW).mpr
    exact (mul_le_of_le_one_left (abs_nonneg g) hρ₁).trans (by dsimp only [W]; linarith)
  have hσ₂ : σ ^ 2 ≤ 1 := pow_le_one₀ hσ hσ₁
  have hσ₂g : σ ^ 2 * |g| ≤ 1 := by
    calc
      _ = σ * (σ * |g|) := by ring
      _ ≤ σ := mul_le_of_le_one_right hσ hσg
      _ ≤ 1 := hσ₁
  have hρ₂ : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ.le hρ₁
  have hA₁' : ‖deriv A k‖ ≤ C := hA₁.trans (mul_le_of_le_one_right hC hρ₂)
  have hA₂' : ‖deriv (deriv A) k‖ ≤ C := hA₂.trans (mul_le_of_le_one_right hC hρ₂)
  have hd₁ : ‖d₁‖ ≤ 4 * C * D := by
    have H := (norm_add_le (deriv A k (c k)) (A k (deriv c k))).trans
      (add_le_add ((deriv A k).le_opNorm (c k)) ((A k).le_opNorm (deriv c k)))
    have H' : ‖d₁‖ ≤ C * D + C * D := H.trans (by gcongr)
    nlinarith [mul_nonneg hC hD]
  have hd₂ : ‖d₂‖ ≤ 4 * C * D := by
    have H := (norm_add_le
      (deriv (deriv A) k (c k) + (2 : ℝ) • deriv A k (deriv c k))
      (A k (deriv (deriv c) k))).trans (add_le_add
        (norm_add_le (deriv (deriv A) k (c k)) ((2 : ℝ) • deriv A k (deriv c k))) le_rfl)
    change ‖d₂‖ ≤ _ at H
    have H' : ‖d₂‖ ≤ C * D + 2 * (C * D) + C * D := by
      apply H.trans
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      · exact ((deriv (deriv A) k).le_opNorm (c k)).trans (by gcongr)
      · exact ((deriv A k).le_opNorm (deriv c k)).trans (by gcongr)
      · exact ((A k).le_opNorm (deriv (deriv c) k)).trans (by gcongr)
    nlinarith
  have hδU : δ * (ρ^2)⁻¹ = σ := by dsimp only [δ,σ]; field_simp
  have hδV : δ * (W⁻¹*ρ⁻¹) = σ ^ 2 := by dsimp only [δ,σ]; field_simp
  have hU : ‖U‖ ≤ C := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hρ))]
    calc
      _ ≤ (ρ^2)⁻¹*(C*ρ^2) := mul_le_mul_of_nonneg_left hA₁ (by positivity)
      _ = C := by field_simp
  refine ⟨u₀,a₀,U,V,by fun_prop,by fun_prop,hA₀,hU,?_,?_,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW)]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ hW).mpr hW₁)).trans
      (inverse_scale_matrix_bound hρ hρ₁ hC hA₂)
  · intro t
    exact ⟨scaled_affine_noise_velocity_bound hσ hσ₁ hσg hC (by positivity) hb₁ hd₁ hv₁,
      scaled_affine_noise_velocity_bound (sq_nonneg σ) hσ₂ hσ₂g hC (by positivity) hb₂ hd₂ hv₂⟩
  · intro t y
    exact ((hA.clm_apply contDiffAt_const).add hb |>.add
      ((hA.clm_apply hc).const_smul g)).add (hv.const_smul t)
  · intro t y
    have H := (affine_endpoint_curve_two_jets hA hb hc hv 1 g t y).1
    simp only [one_smul] at H
    rw [H]
    simp only [u₀,U,smul_apply,smul_add,smul_smul]
    rw [hδU]
    dsimp only [d₁]
    module
  · intro t y
    have H := (affine_endpoint_curve_two_jets hA hb hc hv 1 g t y).2
    simp only [one_smul] at H
    rw [H]
    simp only [a₀,V,smul_apply,smul_add,smul_smul]
    rw [hδV]
    dsimp only [d₂]
    module

end SKBarriers2.Corner
