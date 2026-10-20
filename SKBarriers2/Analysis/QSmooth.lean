module

public import OAI.Probability.SKBarriers.Gaussian.BoundedDerivatives
public import OAI.Probability.SKBarriers.Gaussian.C1Taylor

@[expose] public section

noncomputable section

namespace SKBarriers2

open scoped BigOperators

structure QBddSmooth (r : ℕ) (B : ℝ) (f : (Fin 3 → ℝ) → ℝ) : Prop where
  nonneg : 0 ≤ B
  smooth : ContDiff ℝ r f
  bound : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B

structure QPotential (r : ℕ) (B : ℝ) (f : (Fin 3 → ℝ) → ℝ) : Prop where
  nonneg : 0 ≤ B
  smooth : ContDiff ℝ r f
  bound : ∀ j, 1 ≤ j → j ≤ r → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B

namespace QBddSmooth

variable {r s : ℕ} {B C : ℝ} {f : (Fin 3 → ℝ) → ℝ}

theorem of_le (hf : QBddSmooth r B f) (hs : s ≤ r) : QBddSmooth s B f := by
  refine ⟨hf.nonneg, hf.smooth.of_le (by exact_mod_cast hs), ?_⟩
  intro j hj x
  exact hf.bound j (hj.trans hs) x

theorem mono (hf : QBddSmooth r B f) (hBC : B ≤ C) : QBddSmooth r C f := by
  refine ⟨hf.nonneg.trans hBC, hf.smooth, ?_⟩
  intro j hj x
  exact (hf.bound j hj x).trans hBC

theorem abs_le (hf : QBddSmooth r B f) (x : Fin 3 → ℝ) : |f x| ≤ B := by
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hf.bound 0 (Nat.zero_le r) x

theorem potential (hf : QBddSmooth r B f) : QPotential r B f := by
  exact ⟨hf.nonneg, hf.smooth, fun j _ hj x => hf.bound j hj x⟩

theorem jet_continuous (hf : QBddSmooth r B f) {j : ℕ} (hj : j ≤ r) :
    Continuous (iteratedFDeriv ℝ j f) := by
  exact hf.smooth.continuous_iteratedFDeriv (by exact_mod_cast hj)

theorem partial_le (hf : QBddSmooth r B f) {j : ℕ} (hj : j ≤ r)
    (x : Fin 3 → ℝ) (i : Fin j → Fin 3) :
    |iteratedFDeriv ℝ j f x (fun a => Pi.single (i a) (1 : ℝ))| ≤ B := by
  have H := (iteratedFDeriv ℝ j f x).le_mul_prod_of_opNorm_le_of_le (hf.bound j hj x)
    (m := fun a => Pi.single (i a) (1 : ℝ)) (b := fun _ => (1 : ℝ))
    (fun _ => by simp only [Pi.norm_single, norm_one, le_refl])
  simpa only [Real.norm_eq_abs, Finset.prod_const_one, mul_one] using H

theorem add {g : (Fin 3 → ℝ) → ℝ} (hf : QBddSmooth r B f) (hg : QBddSmooth r C g) :
    QBddSmooth r (B + C) (fun x => f x + g x) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.add hg.smooth, ?_⟩
  intro j hj x
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ B + C
  rw [iteratedFDeriv_add (hf.smooth.of_le (by exact_mod_cast hj))
    (hg.smooth.of_le (by exact_mod_cast hj))]
  exact (norm_add_le _ _).trans (add_le_add (hf.bound j hj x) (hg.bound j hj x))

theorem translate (hf : QBddSmooth r B f) (a : Fin 3 → ℝ) :
    QBddSmooth r B (fun x => f (x + a)) := by
  refine ⟨hf.nonneg, hf.smooth.comp (contDiff_id.add contDiff_const), ?_⟩
  intro j hj x
  rw [iteratedFDeriv_comp_add_right]
  exact hf.bound j hj (x + a)

end QBddSmooth

namespace QPotential

variable {r s : ℕ} {B C : ℝ} {f : (Fin 3 → ℝ) → ℝ}

theorem of_le (hf : QPotential r B f) (hs : s ≤ r) : QPotential s B f := by
  refine ⟨hf.nonneg, hf.smooth.of_le (by exact_mod_cast hs), ?_⟩
  intro j hj hjs x
  exact hf.bound j hj (hjs.trans hs) x

theorem fderiv_le (hf : QPotential r B f) (hr : 1 ≤ r) (x : Fin 3 → ℝ) :
    ‖fderiv ℝ f x‖ ≤ B := by
  simpa only [norm_iteratedFDeriv_one] using hf.bound 1 le_rfl hr x

theorem second_le (hf : QPotential r B f) (hr : 2 ≤ r) (x : Fin 3 → ℝ) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B := by
  have h := hf.bound 2 (by omega) hr x
  rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h
  exact h

theorem boundedDerivs (hf : QPotential r B f) (hr : 2 ≤ r) :
    OAI.SK.Analytic.BoundedDerivs f := by
  exact ⟨hf.smooth.of_le (by exact_mod_cast hr), B, B, hf.nonneg, hf.nonneg,
    hf.fderiv_le (by omega), hf.second_le hr⟩

theorem directional_le (hf : QPotential r B f) (hr : 1 ≤ r) (x v : Fin 3 → ℝ) :
    |fderiv ℝ f x v| ≤ B * ‖v‖ := by
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (hf.fderiv_le hr x) (norm_nonneg v))

theorem second_directional_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (x v w : Fin 3 → ℝ) :
    |fderiv ℝ (fderiv ℝ f) x v w| ≤ B * ‖v‖ * ‖w‖ := by
  calc
    |fderiv ℝ (fderiv ℝ f) x v w| ≤ ‖fderiv ℝ (fderiv ℝ f) x v‖ * ‖w‖ :=
      by simpa only [Real.norm_eq_abs] using (fderiv ℝ (fderiv ℝ f) x v).le_opNorm w
    _ ≤ (‖fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖) * ‖w‖ := by
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ v) (norm_nonneg w)
    _ ≤ B * ‖v‖ * ‖w‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hf.second_le hr x) (norm_nonneg v)) (norm_nonneg w)

theorem directional (hf : QPotential (r + 1) B f) (v : Fin 3 → ℝ) :
    QBddSmooth r (B * ‖v‖) (fun x => fderiv ℝ f x v) := by
  have hs : ContDiff ℝ r (fderiv ℝ f) := hf.smooth.fderiv_right (by simp)
  refine ⟨mul_nonneg hf.nonneg (norm_nonneg v), hs.clm_apply contDiff_const, ?_⟩
  intro j hj x
  calc
    ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ f x v) x‖ ≤
        ‖v‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ :=
      norm_iteratedFDeriv_clm_apply_const hs.contDiffAt (by exact_mod_cast hj)
    _ = ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) f x‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ ≤ ‖v‖ * B := mul_le_mul_of_nonneg_left
      (hf.bound (j + 1) (by omega) (by omega) x) (norm_nonneg v)
    _ = B * ‖v‖ := mul_comm _ _

theorem lipschitzWith (hf : QPotential r B f) (hr : 1 ≤ r) :
    LipschitzWith ⟨B, hf.nonneg⟩ f := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((hf.smooth.of_le (by exact_mod_cast hr) : ContDiff ℝ 1 f).differentiable (by norm_num))
  intro x
  exact_mod_cast hf.fderiv_le hr x

theorem directional_lipschitzWith (hf : QPotential (r + 2) B f) (v : Fin 3 → ℝ) :
    LipschitzWith ⟨B * ‖v‖, mul_nonneg hf.nonneg (norm_nonneg v)⟩
      (fun x => fderiv ℝ f x v) := by
  exact ((hf.of_le (by omega : 2 ≤ r + 2)).directional v).potential.lipschitzWith le_rfl

theorem taylor_linear_remainder_le (hf : QPotential r B f) (hr : 2 ≤ r)
    (x y : Fin 3 → ℝ) :
    |f (x + y) - f x - fderiv ℝ f x y| ≤ B * ‖y‖ ^ 2 := by
  let F : ℝ → ℝ := fun t => f (x + t • y)
  let D : ℝ → ℝ := fun t => fderiv ℝ f (x + t • y) y
  have hline : LipschitzWith ‖y‖₊ (fun t : ℝ => x + t • y) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm]
    have he : x + a • y - (x + b • y) = (a - b) • y := by module
    rw [he, norm_smul, Real.norm_eq_abs, Real.dist_eq, coe_nnnorm, mul_comm]
  have hD : LipschitzWith (⟨B * ‖y‖, mul_nonneg hf.nonneg (norm_nonneg y)⟩ * ‖y‖₊) D :=
    ((hf.of_le hr).directional_lipschitzWith (r := 0) y).comp hline
  have hd (t : ℝ) : HasDerivAt F (D t) t := by
    have hy : HasDerivAt (fun s : ℝ => x + s • y) y t := by
      convert! (((hasDerivAt_id t).smul_const y).const_add x) using 1
      simp only [one_smul]
    exact ((hf.smooth.of_le (by exact_mod_cast hr) : ContDiff ℝ 2 f).differentiable
      (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hy
  have h := OAI.SK.Analytic.lipschitz_derivative_taylor hd hD 0 1
  simp only [F, D, zero_add, zero_smul, one_smul, add_zero, mul_one, one_pow] at h
  change |f (x + y) - f x - fderiv ℝ f x y| ≤ B * ‖y‖ * ‖y‖ at h
  exact h.trans_eq (by ring)

end QPotential

end SKBarriers2
