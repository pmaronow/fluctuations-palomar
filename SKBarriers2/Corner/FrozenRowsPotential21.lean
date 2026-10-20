module

public import SKBarriers2.Corner.FrozenRowsPotential13

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner
open StepCalculus
local notation "V3" => (Fin 3 → ℝ)

theorem clm_curve_two_jets {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {v : ℝ → E} {k : ℝ}
    (hA : ContDiffAt ℝ 2 A k) (hv : ContDiffAt ℝ 2 v k) :
    deriv (fun κ => A κ (v κ)) k = deriv A k (v k) + A k (deriv v k) ∧
      deriv (deriv (fun κ => A κ (v κ))) k =
        deriv (deriv A) k (v k) + (2 : ℝ) • (deriv A k (deriv v k)) +
          A k (deriv (deriv v) k) := by
  have hAd := (hA.differentiableAt (by norm_num)).hasDerivAt
  have hvd := (hv.differentiableAt (by norm_num)).hasDerivAt
  have hAdd := ((hA.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hvdd := ((hv.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  refine ⟨(hAd.clm_apply hvd).deriv,?_⟩
  have hnear : deriv (fun κ => A κ (v κ)) =ᶠ[𝓝 k]
      fun κ => deriv A κ (v κ) + A κ (deriv v κ) := by
    filter_upwards [hA.eventually (by norm_num),hv.eventually (by norm_num)] with κ hκ hκ'
    exact (((hκ.differentiableAt (by norm_num)).hasDerivAt).clm_apply
      (hκ'.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [hnear.deriv_eq]
  exact (((hAdd.clm_apply hvd).add (hAd.clm_apply hvdd)).deriv).trans (by module)

theorem scaled_affine_noise_velocity_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {σ g t C D : ℝ} {b d w : E} (hσ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (hσg : σ * |g| ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ‖b‖ ≤ C) (hd : ‖d‖ ≤ D) (hw : ‖w‖ ≤ C) :
    ‖σ • (b + g • d + t • w)‖ ≤ (2 * C + D) * (1 + |t|) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hσ]
  have H : ‖b + g • d + t • w‖ ≤ C + |g| * D + |t| * C := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · apply (norm_add_le _ _).trans
      rw [norm_smul,Real.norm_eq_abs]
      gcongr
    · rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hw (abs_nonneg t)
  calc
    _ ≤ σ * (C + |g| * D + |t| * C) := mul_le_mul_of_nonneg_left H hσ
    _ = σ * C + (σ * |g|) * D + σ * (|t| * C) := by ring
    _ ≤ C + D + |t| * C := by
      apply add_le_add
      · exact add_le_add (mul_le_of_le_one_left hC hσ₁) (mul_le_of_le_one_left hD hσg)
      · exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg t) hC) hσ₁
    _ ≤ _ := by nlinarith [mul_nonneg hD (abs_nonneg t),mul_nonneg hC (abs_nonneg t)]

theorem inverse_scale_matrix_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ C : ℝ} {A : E →L[ℝ] E} (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hC : 0 ≤ C)
    (hA : ‖A‖ ≤ C * ρ ^ 2) : ‖ρ⁻¹ • A‖ ≤ C := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hρ)]
  calc
    _ ≤ ρ⁻¹ * (C * ρ ^ 2) := mul_le_mul_of_nonneg_left hA (inv_nonneg.mpr hρ.le)
    _ = C * ρ := by field_simp
    _ ≤ C := mul_le_of_le_one_right hC hρ₁

theorem affine_endpoint_curve_two_jets
    {A : ℝ → V3 →L[ℝ] V3} {b c v : ℝ → V3} {k : ℝ}
    (hA : ContDiffAt ℝ 2 A k) (hb : ContDiffAt ℝ 2 b k)
    (hc : ContDiffAt ℝ 2 c k) (hv : ContDiffAt ℝ 2 v k)
    (ρ g t : ℝ) (y : V3) :
    let X := fun κ => ρ • A κ y + b κ + g • A κ (c κ) + t • v κ
    deriv X k = ρ • deriv A k y + deriv b k +
      g • (deriv A k (c k) + A k (deriv c k)) + t • deriv v k ∧
    deriv (deriv X) k = ρ • deriv (deriv A) k y + deriv (deriv b) k +
      g • (deriv (deriv A) k (c k) + (2 : ℝ) • deriv A k (deriv c k) +
        A k (deriv (deriv c) k)) + t • deriv (deriv v) k := by
  have hAy : ContDiffAt ℝ 2 (fun κ => A κ y) k := hA.clm_apply contDiffAt_const
  have hAc : ContDiffAt ℝ 2 (fun κ => A κ (c κ)) k := hA.clm_apply hc
  have h₁ := (clm_curve_two_jets hA hc).1
  have h₂ := (clm_curve_two_jets hA hc).2
  have hAy₁ : deriv (fun κ => A κ y) k = deriv A k y := by
    simpa only [deriv_const,map_zero,add_zero] using
      (clm_curve_two_jets hA (v := fun _ => y) contDiffAt_const).1
  have hAy₂ : deriv (deriv (fun κ => A κ y)) k = deriv (deriv A) k y := by
    simpa only [deriv_const',deriv_const,map_zero,smul_zero,add_zero] using
      (clm_curve_two_jets hA (v := fun _ => y) contDiffAt_const).2
  dsimp only
  constructor
  · have HD := (((((hAy.differentiableAt (by norm_num)).hasDerivAt.const_smul ρ).add
        (hb.differentiableAt (by norm_num)).hasDerivAt).add
        ((hAc.differentiableAt (by norm_num)).hasDerivAt.const_smul g)).add
        ((hv.differentiableAt (by norm_num)).hasDerivAt.const_smul t)).deriv
    have he : (((ρ • fun κ => A κ y) + b + g • fun κ => A κ (c κ)) + t • v) =
        fun κ => ρ • A κ y + b κ + g • A κ (c κ) + t • v κ := by
      funext κ
      rfl
    rw [he,hAy₁,h₁] at HD
    exact HD
  · have hiter (f : ℝ → V3) : iteratedDeriv 2 f k = deriv (deriv f) k := by
      rw [iteratedDeriv_succ,iteratedDeriv_one]
    conv_lhs => rw [← hiter]
    rw [iteratedDeriv_fun_add (((hAy.const_smul ρ).add hb).add (hAc.const_smul g)) (hv.const_smul t),
      iteratedDeriv_fun_add ((hAy.const_smul ρ).add hb) (hAc.const_smul g),
      iteratedDeriv_fun_add (hAy.const_smul ρ) hb]
    simp only [iteratedDeriv_fun_const_smul_field,iteratedDeriv_succ,iteratedDeriv_zero,hAy₂,h₂]

set_option maxHeartbeats 0 in
theorem affine_endpoint_small_score_geometry
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
    let X := fun κ t y => ρ • A κ y + b κ + g • A κ (c κ) + t • v κ
    ∃ u₀ a₀ : ℝ → V3, ∃ U V : V3 →L[ℝ] V3,
      ContDiff ℝ ∞ u₀ ∧ ContDiff ℝ ∞ a₀ ∧
      ‖ρ • A k‖ ≤ C ∧ ‖U‖ ≤ C ∧ ‖V‖ ≤ C ∧
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
  let U := ρ⁻¹ • deriv A k
  let V := W⁻¹ • deriv (deriv A) k
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
  have hδU : δ * ρ⁻¹ = σ * ρ := by dsimp only [δ,σ]; field_simp
  have hδV : δ * W⁻¹ = σ ^ 2 * ρ := by dsimp only [δ,σ]; field_simp
  refine ⟨u₀,a₀,U,V,by fun_prop,by fun_prop,?_,
    inverse_scale_matrix_bound hρ hρ₁ hC hA₁,?_,?_,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos hρ]
    exact (mul_le_of_le_one_left (norm_nonneg _) hρ₁).trans hA₀
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hW)]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ hW).mpr hW₁)).trans hA₂'
  · intro t
    exact ⟨scaled_affine_noise_velocity_bound hσ hσ₁ hσg hC (by positivity) hb₁ hd₁ hv₁,
      scaled_affine_noise_velocity_bound (sq_nonneg σ) hσ₂ hσ₂g hC (by positivity) hb₂ hd₂ hv₂⟩
  · intro t y
    exact (((hA.clm_apply contDiffAt_const).const_smul ρ).add hb |>.add
      ((hA.clm_apply hc).const_smul g)).add (hv.const_smul t)
  · intro t y
    rw [(affine_endpoint_curve_two_jets hA hb hc hv ρ g t y).1]
    simp only [u₀,U,smul_apply,smul_add,smul_smul]
    rw [hδU]
    dsimp only [d₁]
    module
  · intro t y
    rw [(affine_endpoint_curve_two_jets hA hb hc hv ρ g t y).2]
    simp only [a₀,V,smul_apply,smul_add,smul_smul]
    rw [hδV]
    dsimp only [d₂]
    module

end SKBarriers2.Corner
