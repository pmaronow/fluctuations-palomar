module

public import SKBarriers2.Corner.FrozenRowsMixed3

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set Filter OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

theorem epsilonLogCumulantsKJet_scale_grade (c m : ℝ)
    (A : Fin 3 → MomentKJet) (i : Fin 3) :
    (epsilonLogCumulantsKJet m A i).scale (c ^ (i.val + 1)) =
      epsilonLogCumulantsKJet m (fun j => (A j).scale (c ^ (j.val + 1))) i := by
  fin_cases i <;>
    simp only [epsilonLogCumulantsKJet, Matrix.cons_val_zero', Matrix.cons_val_succ',
      MomentKJet.scale, MomentKJet.add, MomentKJet.mul] <;>
    congr 1 <;> norm_num <;> ring

theorem epsilonBellTestsKJet_scale_grade (c m : ℝ)
    (A : Fin 3 → MomentKJet) (i : Fin 3) :
    (epsilonBellTestsKJet m A i).scale (c ^ (i.val + 1)) =
      epsilonBellTestsKJet m (fun j => (A j).scale (c ^ (j.val + 1))) i := by
  fin_cases i <;>
    simp only [epsilonBellTestsKJet, Matrix.cons_val_zero', Matrix.cons_val_succ',
      MomentKJet.scale, MomentKJet.add, MomentKJet.mul] <;>
    congr 1 <;> norm_num <;> ring

theorem normalizedEpsilonKJet_eq_inverse_scale {ρ : ℝ} (hρ : ρ ≠ 0)
    (l : ℝ → List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (c : Vec3) (y : ℝ → Vec3) (n : ℕ) (ε k : ℝ) :
    normalizedEpsilonKJet l Q K ρ c y n ε k =
      (originalEpsilonKJet l Q K ρ c y n ε k).scale (((ρ ^ 3) ^ n)⁻¹) := by
  rw [originalEpsilonKJet_eq_scale hρ, MomentKJet.scale_scale]
  rw [inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hρ))]
  cases normalizedEpsilonKJet l Q K ρ c y n ε k
  simp only [MomentKJet.scale, one_mul]

namespace MomentKJet

theorem SpatialBound.rescale_contract {r p : ℕ} {B c ρ : ℝ}
    {J : Vec3 → MomentKJet} (H : SpatialBound r B p (fun x => rescale ρ (J x)))
    (hc : |c| ≤ 1) :
    SpatialBound r B p (fun x => rescale (c*ρ) (J x)) := by
  have hB := H.1.nonneg
  refine ⟨H.1, ?_, ?_⟩
  · have H₁ := H.2.1.const_smul c
    have he : (fun x => c • (rescale ρ (J x)).first) =
        fun x => (rescale (c*ρ) (J x)).first := by
      funext x
      simp only [rescale,smul_eq_mul]
      ring
    rw [he] at H₁
    exact H₁.mono (mul_le_of_le_one_left hB hc) le_rfl
  · have H₂ := H.2.2.const_smul (c^2)
    have he : (fun x => c^2 • (rescale ρ (J x)).second) =
        fun x => (rescale (c*ρ) (J x)).second := by
      funext x
      simp only [rescale,smul_eq_mul]
      ring
    rw [he] at H₂
    apply H₂.mono _ le_rfl
    rw [abs_pow]
    exact mul_le_of_le_one_left hB (pow_le_one₀ (abs_nonneg c) hc)

theorem SpatialBound.rescale_le {r p : ℕ} {B L σ ρ : ℝ}
    {J : Vec3 → MomentKJet} (H : SpatialBound r B p (fun x => rescale σ (J x)))
    (hL : 1 ≤ L) (hρ : ρ = L * σ) :
    SpatialBound r (L ^ 2 * B) p (fun x => rescale ρ (J x)) := by
  have hB := H.1.nonneg
  have hL₀ : 0 ≤ L := by linarith
  have hL₂ : L ≤ L ^ 2 := by nlinarith
  have hL₁ : 1 ≤ L ^ 2 := by nlinarith
  refine ⟨H.1.mono (le_mul_of_one_le_left hB hL₁) le_rfl, ?_, ?_⟩
  · have H₁ := H.2.1.const_smul L
    have he : (fun x => L • (rescale σ (J x)).first) =
        fun x => (rescale ρ (J x)).first := by
      funext x
      simp only [rescale, smul_eq_mul, hρ]
      ring
    rw [he] at H₁
    apply H₁.mono _ le_rfl
    rw [abs_of_nonneg hL₀]
    exact mul_le_mul_of_nonneg_right hL₂ hB
  · have H₂ := H.2.2.const_smul (L ^ 2)
    have he : (fun x => L ^ 2 • (rescale σ (J x)).second) =
        fun x => (rescale ρ (J x)).second := by
      funext x
      simp only [rescale, smul_eq_mul, hρ]
      ring
    rw [he] at H₂
    simpa only [abs_of_nonneg (sq_nonneg L)] using H₂

theorem external_row_coefficient {C M g : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hn : 1 ≤ n) :
    (1 + |g|) ^ 2 * (C * M * (1 + |g|) ^ 3) ^ n ≤
      (8 * C * M * (1 + g ^ 2) ^ 3) ^ n := by
  have hw : 1 ≤ 1 + |g| := by linarith [abs_nonneg g]
  have hsquare : (1 + |g|) ^ 2 ≤ 2 * (1 + g ^ 2) := by
    nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  calc
    _ = (C * M) ^ n * (1 + |g|) ^ (3 * n + 2) := by
      simp only [mul_pow, pow_mul, pow_add]
      ring
    _ ≤ (C * M) ^ n * (1 + |g|) ^ (6 * n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (by omega)) (by positivity)
    _ = (C * M) ^ n * ((1 + |g|) ^ 2) ^ (3 * n) := by
      rw [← pow_mul]
      congr 2
      omega
    _ ≤ (C * M) ^ n * (2 * (1 + g ^ 2)) ^ (3 * n) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hsquare _) (by positivity)
    _ = _ := by
      simp only [mul_pow, pow_mul]
      ring

theorem SpatialBound.restore_external_row {r n : ℕ} {C M ρ g : ℝ}
    {J : Vec3 → MomentKJet} (hC : 0 ≤ C) (hM : 0 ≤ M) (hn : 1 ≤ n)
    (H : SpatialBound r ((C * M * (1 + |g|) ^ 3) ^ n) (3 * n)
      (fun x => rescale (ρ / (1 + |g|)) (J x))) :
    SpatialBound r ((8 * C * M * (1 + g ^ 2) ^ 3) ^ n) (3 * n)
      (fun x => rescale ρ (J x)) := by
  have hw : 1 ≤ 1 + |g| := by linarith [abs_nonneg g]
  have hw₀ : 1 + |g| ≠ 0 := by positivity
  have he : ρ = (1 + |g|) * (ρ / (1 + |g|)) := by field_simp
  exact (H.rescale_le hw he).mono (external_row_coefficient hC hM hn) le_rfl

end MomentKJet
end SKBarriers2.Corner
