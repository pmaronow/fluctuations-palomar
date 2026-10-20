module

public import SKBarriers2.Corner.PathEnergyInner5

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

private theorem terminal_gradient_product_jets {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (v w : E) :
    QBoundedJets 2 (4 * B ^ 2 * ‖v‖ * ‖w‖)
      (fun x => fderiv ℝ f x v * fderiv ℝ f x w) := by
  have h := ((hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const v).mul
    ((hf.derivativeJets.of_le (by norm_num : 2 ≤ 3)).apply_const w)
  convert h using 1; ring

private theorem terminal_hessian_jets {B : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (v w : E) :
    QBoundedJets 2 (B * ‖v‖ * ‖w‖)
      (fun x => fderiv ℝ (fderiv ℝ f) x v w) :=
  (hf.derivativeJets.derivativeJets.apply_const v).apply_const w

private theorem gradient_product_common_budget {B d : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) {v w : E} (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) :
    QBoundedJets 2 (4 * B ^ 2 * d ^ 2)
      (fun x => fderiv ℝ f x v * fderiv ℝ f x w) := by
  apply (terminal_gradient_product_jets hf v w).mono
  have hd : 0 ≤ d := (norm_nonneg v).trans hv
  calc
    _ = 4 * B ^ 2 * (‖v‖ * ‖w‖) := by ring
    _ ≤ 4 * B ^ 2 * (d * d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hv hw (norm_nonneg _) hd) (by positivity)
    _ = _ := by ring

private theorem hessian_common_budget {B d : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) {v w : E} (hv : ‖v‖ ≤ d) (hw : ‖w‖ ≤ d) :
    QBoundedJets 2 (B * d ^ 2)
      (fun x => fderiv ℝ (fderiv ℝ f) x v w) := by
  apply (terminal_hessian_jets hf v w).mono
  have hd : 0 ≤ d := (norm_nonneg v).trans hv
  calc
    _ = B * (‖v‖ * ‖w‖) := by ring
    _ ≤ B * (d * d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hv hw (norm_nonneg _) hd) hf.nonneg
    _ = _ := by ring

theorem qBoundedJets_stepQuadraticIncrement_parameter {B d : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) {p : ℝ → ℝ × E} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hm : (p k).1 ∈ Icc (0 : ℝ) 1)
    (hdm : |deriv (fun t => (p t).1) k| ≤ 1)
    (hddm : |deriv (deriv (fun t => (p t).1)) k| ≤ 1)
    (hv : ‖(p k).2‖ ≤ d) (hw : ‖deriv (fun t => (p t).2) k‖ ≤ d)
    (hb : ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ d) :
    ∀ c : ℕ, c ≤ 2 →
      QBoundedJets 2 ((2 * B + 20 * B ^ 2) * d ^ 2)
        (fun x => iteratedDeriv c (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) k) := by
  let m := (p k).1
  let v := (p k).2
  let dm := deriv (fun t => (p t).1) k
  let ddm := deriv (deriv (fun t => (p t).1)) k
  let w := deriv (fun t => (p t).2) k
  let b := deriv (deriv (fun t => (p t).2)) k
  have hB := hf.nonneg
  have hd : 0 ≤ d := (norm_nonneg _).trans hv
  have hC : 0 ≤ (2 * B + 20 * B ^ 2) * d ^ 2 := by positivity
  have hPP := gradient_product_common_budget hf hv hv
  have hPW := gradient_product_common_budget hf hv hw
  have hWW := gradient_product_common_budget hf hw hw
  have hPB := gradient_product_common_budget hf hv hb
  have hHV := hessian_common_budget hf hv hv
  have hHW := hessian_common_budget hf hw hw
  have hHvw := hessian_common_budget hf hv hw
  have hHvb := hessian_common_budget hf hv hb
  have hDirw : QBoundedJets 2 ((B + 4 * B ^ 2) * d ^ 2)
      (directionSource m v w f) := by
    have H := (hPW.const_smul m).add hHvw
    have he : directionSource m v w f = fun x =>
        m * (fderiv ℝ f x v * fderiv ℝ f x w) + fderiv ℝ (fderiv ℝ f) x v w := by
      funext x
      dsimp only [directionSource]
      ring
    rw [he]
    apply H.mono
    rw [abs_of_nonneg hm.1]
    nlinarith [mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 4 * B ^ 2 * d ^ 2)]
  have hDirb : QBoundedJets 2 ((B + 4 * B ^ 2) * d ^ 2)
      (directionSource m v b f) := by
    have H := (hPB.const_smul m).add hHvb
    have he : directionSource m v b f = fun x =>
        m * (fderiv ℝ f x v * fderiv ℝ f x b) + fderiv ℝ (fderiv ℝ f) x v b := by
      funext x
      dsimp only [directionSource]
      ring
    rw [he]
    apply H.mono
    rw [abs_of_nonneg hm.1]
    nlinarith [mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 4 * B ^ 2 * d ^ 2)]
  intro c hc
  interval_cases c
  · have H := ((hPP.const_smul m).add hHV).const_smul (1 / 2 : ℝ)
    have he : (fun x => iteratedDeriv 0 (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) k) =
        fun x => (1 / 2 : ℝ) *
          (m * (fderiv ℝ f x v * fderiv ℝ f x v) + fderiv ℝ (fderiv ℝ f) x v v) := by
      funext x
      rw [iteratedDeriv_zero, stepQuadraticIncrement_eq_hessian (hf.of_le (by norm_num))]
      dsimp only [m, v]
      ring
    rw [he]
    apply H.mono
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg hm.1]
    nlinarith [mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 4 * B ^ 2 * d ^ 2),
      mul_nonneg hB (sq_nonneg d), mul_nonneg (sq_nonneg B) (sq_nonneg d)]
  · have H := (hPP.const_smul (dm / 2)).add hDirw
    have he : (fun x => iteratedDeriv 1 (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) k) =
        fun x => dm / 2 * (fderiv ℝ f x v * fderiv ℝ f x v) + directionSource m v w f x := by
      funext x
      rw [iteratedDeriv_one]
      have h := (stepQuadraticIncrement_twoJet (hf.of_le (by norm_num)) hp x).1
      rw [h]
      simp only [stepQuadraticFirstSource, fderiv_fun_const,
        Pi.zero_apply, zero_apply, directionalJet, mul_zero, zero_add, add_zero, zero_div]
      dsimp only [m, v, dm, w]
      ring
    rw [he]
    apply H.mono
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_right hdm (by positivity : 0 ≤ 4 * B ^ 2 * d ^ 2),
      mul_nonneg hB (sq_nonneg d), mul_nonneg (sq_nonneg B) (sq_nonneg d)]
  · have H := (((hHW.add hDirb).add (hWW.const_smul m)).add
      (hPW.const_smul (2 * dm))).add (hPP.const_smul (ddm / 2))
    have he : (fun x => iteratedDeriv 2 (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) k) =
        fun x => fderiv ℝ (fderiv ℝ f) x w w + directionSource m v b f x +
          m * (fderiv ℝ f x w * fderiv ℝ f x w) +
          (2 * dm) * (fderiv ℝ f x v * fderiv ℝ f x w) +
          (ddm / 2) * (fderiv ℝ f x v * fderiv ℝ f x v) := by
      funext x
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      have h := (stepQuadraticIncrement_twoJet (hf.of_le (by norm_num)) hp x).2
      rw [h]
      simp only [stepQuadraticSecondSource, mixedDirectionSource,
        fderiv_fun_const, fderiv_zero, Pi.zero_apply, zero_apply, directionalJet,
        zero_mul, mul_zero, zero_add, add_zero, zero_div]
      dsimp only [m, v, dm, ddm, w, b]
      ring
    rw [he]
    apply H.mono
    rw [abs_of_nonneg hm.1, abs_mul, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_right hm.2 (by positivity : 0 ≤ 4 * B ^ 2 * d ^ 2),
      mul_le_mul_of_nonneg_right hdm (by positivity : 0 ≤ 4 * B ^ 2 * d ^ 2),
      mul_le_mul_of_nonneg_right hddm (by positivity : 0 ≤ 4 * B ^ 2 * d ^ 2),
      mul_nonneg (sq_nonneg B) (sq_nonneg d)]

theorem qBoundedJets_pathQuadraticSum_parameter {B d : ℝ} {f : E → ℝ}
    (hf : QPotential 4 B f) (ps : List (ℝ → ℝ × E)) {k : ℝ}
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k)
    (hjets : ∀ p ∈ ps,
      (p k).1 ∈ Icc (0 : ℝ) 1 ∧
      |deriv (fun t => (p t).1) k| ≤ 1 ∧
      |deriv (deriv (fun t => (p t).1)) k| ≤ 1 ∧
      ‖(p k).2‖ ≤ d ∧ ‖deriv (fun t => (p t).2) k‖ ≤ d ∧
      ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ d) :
    ∀ c : ℕ, c ≤ 2 →
      QBoundedJets 2 ((2 * B + 20 * B ^ 2) * (ps.length : ℝ) * d ^ 2)
        (fun x => iteratedDeriv c (fun t => pathQuadraticSum f (ps.map (fun p => p t)) x) k) := by
  intro c hc
  induction ps with
  | nil =>
    have he : (fun x : E => iteratedDeriv c
        (fun t => pathQuadraticSum f ([].map (fun p : ℝ → ℝ × E => p t)) x) k) =
        fun _ => (0 : ℝ) := by
      funext x
      interval_cases c <;> simp [pathQuadraticSum]
    rw [he]
    refine ⟨by simp, contDiff_const, ?_⟩
    intro j hj x
    simp
  | cons p ps ih =>
    have hregp := hreg p List.mem_cons_self
    have hjetp := hjets p List.mem_cons_self
    have hregt := fun q hq => hreg q (List.mem_cons_of_mem _ hq)
    have hjetst := fun q hq => hjets q (List.mem_cons_of_mem _ hq)
    have hp := qBoundedJets_stepQuadraticIncrement_parameter hf hregp
      hjetp.1 hjetp.2.1 hjetp.2.2.1 hjetp.2.2.2.1 hjetp.2.2.2.2.1 hjetp.2.2.2.2.2 c hc
    have ht := ih hregt hjetst
    have he : (fun x => iteratedDeriv c
        (fun t => pathQuadraticSum f ((p :: ps).map (fun q => q t)) x) k) =
        fun x => iteratedDeriv c (fun t => stepQuadraticIncrement (p t).1 (p t).2 f x) k +
          iteratedDeriv c (fun t => pathQuadraticSum f (ps.map (fun q => q t)) x) k := by
      funext x
      exact iteratedDeriv_fun_add
        ((contDiffAt_stepQuadraticIncrement (hf.of_le (by norm_num)) hregp x).of_le
          (by exact_mod_cast hc))
        ((contDiffAt_pathQuadraticSum (hf.of_le (by norm_num)) ps hregt x).of_le
          (by exact_mod_cast hc))
    rw [he]
    convert hp.add ht using 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

end SKBarriers2.StepCalculus
