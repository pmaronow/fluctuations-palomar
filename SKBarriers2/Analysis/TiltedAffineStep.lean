module

public import SKBarriers2.Analysis.StepStability

@[expose] public section

noncomputable section
open scoped BigOperators
open Set OAI.SK.Analytic

namespace SKBarriers2

local notation "E" => (Fin 3 → ℝ)

variable {r : ℕ} {B : ℝ} {f : E → ℝ}

namespace QPotential

theorem translate (hf : QPotential r B f) (b : E) :
    QPotential r B (fun x => f (x + b)) := by
  refine ⟨hf.nonneg, hf.smooth.comp (contDiff_id.add contDiff_const), ?_⟩
  intro j hj hjr x
  rw [iteratedFDeriv_comp_add_right]
  exact hf.bound j hj hjr (x + b)

theorem comp_affine (hf : QPotential r B f) (A : E →L[ℝ] E) (b : E) :
    QPotential r (B * max 1 ‖A‖ ^ r) (fun x => f (A x + b)) := by
  have hK : 0 ≤ max (1 : ℝ) ‖A‖ := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨mul_nonneg hf.nonneg (pow_nonneg hK _),
    hf.smooth.comp (A.contDiff.add contDiff_const), ?_⟩
  intro j hj hjr x
  change ‖iteratedFDeriv ℝ j ((fun y => f (y + b)) ∘ A) x‖ ≤ _
  rw [A.iteratedFDeriv_comp_right (hf.translate b).smooth x (by exact_mod_cast hjr)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (fun y => f (y + b)) (A x)‖ * ∏ _ : Fin j, ‖A‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ B * ∏ _ : Fin j, ‖A‖ :=
      mul_le_mul_of_nonneg_right ((hf.translate b).bound j hj hjr (A x)) (by positivity)
    _ = B * ‖A‖ ^ j := by simp
    _ ≤ B * max 1 ‖A‖ ^ r := by
      apply mul_le_mul_of_nonneg_left _ hf.nonneg
      exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) j).trans
        (pow_le_pow_right₀ (le_max_left _ _) hjr)

end QPotential

namespace StepCalculus

def tiltedAffineStep (m : ℝ) (A : E →L[ℝ] E) (b v : E) (f : E → ℝ) : E → ℝ :=
  fun x => vectorStep m v f (A x + b)

theorem qPotential_tiltedAffineStep (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (A : E →L[ℝ] E) (b v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QPotential r ((B + stepStabilityCoefficient r B * ‖v‖ ^ 2) * max 1 ‖A‖ ^ r)
      (tiltedAffineStep m A b v f) := by
  exact (qPotential_step hf hr hm v hsmall).comp_affine A b

end StepCalculus

theorem unbounded_sub_linear_of_bounded {a : ℝ → ℝ} {A u χ z : ℝ}
    (ha : ∀ y, |a y| ≤ A) (hχ : χ ≠ 0) (B : ℝ) :
    ∃ y, B < |a y - (u + χ * (y - z))| := by
  let y := z + (A + |u| + |B| + 1) / χ
  have he : χ * (y - z) = A + |u| + |B| + 1 := by
    dsimp only [y]
    field_simp
    ring
  have hupper := (le_abs_self (a y)).trans (ha y)
  refine ⟨y, ?_⟩
  rw [he]
  have hneg := neg_le_abs (a y - (u + (A + |u| + |B| + 1)))
  linarith [neg_abs_le u, le_abs_self B]

end SKBarriers2
