module

public import SKBarriers2.Analysis.GaussianJets
public import OAI.Probability.SKBarriers.Scalar.VectorHierarchy
public import Mathlib.Analysis.Calculus.Deriv.ZPow

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace SKBarriers2

private theorem iteratedDeriv_log_succ (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) Real.log x =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) * x ^ (-1 - (n : ℤ)) := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]

namespace QBoundedJets

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {r : ℕ} {B C A : ℝ} {f : E → ℝ}

theorem log (hf : QBoundedJets r B f) (hpos : ∀ x, 0 < f x)
    (hC : 0 ≤ C) (hlog : ∀ x, |Real.log (f x)| ≤ C)
    (hA : 1 ≤ A) (hinv : ∀ x, (f x)⁻¹ ≤ A) :
    QBoundedJets r
      ((r.factorial : ℝ) * (C + (r.factorial : ℝ) * A ^ (r + 1)) * (1 + B) ^ r)
      (fun x => Real.log (f x)) := by
  have hB : 1 ≤ 1 + B := by linarith [hf.nonneg]
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  let K : ℝ := C + (r.factorial : ℝ) * A ^ (r + 1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have houter (i : ℕ) (hi : i ≤ r) (x : E) :
      ‖iteratedFDeriv ℝ i Real.log (f x)‖ ≤ K := by
    cases i with
    | zero =>
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (hlog x).trans (le_add_of_nonneg_right (by positivity))
    | succ n =>
      have hx : 0 < f x := hpos x
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_log_succ,
        norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_natCast, Real.norm_eq_abs]
      have hp : |(f x) ^ (-1 - (n : ℤ))| = ((f x)⁻¹) ^ (n + 1) := by
        rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega,
          zpow_neg, zpow_natCast, inv_pow, abs_of_pos (by positivity)]
      rw [hp]
      calc
        (n.factorial : ℝ) * ((f x)⁻¹) ^ (n + 1) ≤
            (r.factorial : ℝ) * A ^ (r + 1) := by
          apply mul_le_mul
          · exact_mod_cast Nat.factorial_le (by omega : n ≤ r)
          · exact (pow_le_pow_left₀ (by positivity) (hinv x) (n + 1)).trans
              (pow_le_pow_right₀ hA (by omega))
          · positivity
          · positivity
        _ ≤ K := le_add_of_nonneg_left hC
  refine ⟨by positivity, hf.smooth.log (fun x => (hpos x).ne'), ?_⟩
  intro j hj x
  calc
    ‖iteratedFDeriv ℝ j (fun x => Real.log (f x)) x‖ ≤
        (j.factorial : ℝ) * K * (1 + B) ^ j := by
      apply norm_iteratedFDeriv_comp_le' (t := Ioi 0)
        (fun y hy => by obtain ⟨z, rfl⟩ := hy; exact hpos z)
        (uniqueDiffOn_Ioi 0)
        (Real.contDiffOn_log.mono (fun y hy => ne_of_gt hy)) hf.smooth
        (by exact_mod_cast hj) x
      · intro i hi
        rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (hpos x)]
        exact houter i (hi.trans hj) x
      · intro i hi hij
        exact (hf.bound i (hij.trans hj) x).trans
          ((by linarith : B ≤ 1 + B).trans (le_self_pow₀ hB (by omega)))
    _ ≤ (r.factorial : ℝ) * K * (1 + B) ^ r := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hK
      · exact pow_le_pow_right₀ hB hj
      · positivity
      · positivity

end QBoundedJets

def exponentialJetBound (r : ℕ) (B : ℝ) : ℝ :=
  (r.factorial : ℝ) * Real.exp B * (1 + B) ^ r

def positiveStepJetBound (r : ℕ) (B a : ℝ) : ℝ :=
  a⁻¹ * ((r.factorial : ℝ) *
    (B + (r.factorial : ℝ) * (1 + Real.exp B) ^ (r + 1)) *
      (1 + exponentialJetBound r B) ^ r)

namespace QBoundedJets

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {r : ℕ} {B a m : ℝ} {f : E → ℝ}

theorem vectorStep (hf : QBoundedJets r B f) (ha : 0 < a)
    (ham : a ≤ m) (hm : m ≤ 1) (v : E) :
    QBoundedJets r (positiveStepJetBound r B a) (OAI.SK.Analytic.vectorStep m v f) := by
  have hm0 : 0 < m := ha.trans_le ham
  have hB0 : 0 ≤ B := hf.nonneg
  have hmf : QBoundedJets r B (fun x => m * f x) := by
    apply (hf.const_smul m).mono
    rw [abs_of_pos hm0]
    exact mul_le_of_le_one_left hB0 hm
  let q : E → ℝ := fun x => Real.exp (m * f x)
  have hq : QBoundedJets r (exponentialJetBound r B) q := hmf.exp
  let Z : E → ℝ := SKBarriers2.gaussianAverage v q
  have hZ : QBoundedJets r (exponentialJetBound r B) Z := hq.gaussianAverage v
  have hlower (x : E) : Real.exp (-B) ≤ Z x := by
    calc
      Real.exp (-B) = ∫ _ : ℝ, Real.exp (-B) ∂gaussianReal 0 1 := by simp
      _ ≤ Z x := by
        apply integral_mono (integrable_const _) (hq.integrable_shift v x)
        intro t
        apply Real.exp_le_exp.mpr
        exact (abs_le.mp (hmf.norm_le (x + t • v))).1
  have hupper (x : E) : Z x ≤ Real.exp B := by
    calc
      Z x ≤ ∫ _ : ℝ, Real.exp B ∂gaussianReal 0 1 := by
        apply integral_mono (hq.integrable_shift v x) (integrable_const _)
        intro t
        apply Real.exp_le_exp.mpr
        exact (abs_le.mp (hmf.norm_le (x + t • v))).2
      _ = Real.exp B := by simp
  have hpos (x : E) : 0 < Z x := (Real.exp_pos (-B)).trans_le (hlower x)
  have hlog (x : E) : |Real.log (Z x)| ≤ B := by
    apply abs_le.mpr
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (-B)) (hlower x)
    · simpa only [Real.log_exp] using Real.log_le_log (hpos x) (hupper x)
  have hinv (x : E) : (Z x)⁻¹ ≤ 1 + Real.exp B := by
    calc
      (Z x)⁻¹ ≤ (Real.exp (-B))⁻¹ := inv_anti₀ (Real.exp_pos (-B)) (hlower x)
      _ = Real.exp B := by rw [← Real.exp_neg, neg_neg]
      _ ≤ 1 + Real.exp B := by linarith
  have hL := hZ.log hpos hB0 hlog (by linarith [Real.exp_pos B]) hinv
  have hs := hL.const_smul m⁻¹
  have heq : OAI.SK.Analytic.vectorStep m v f = fun x => m⁻¹ • Real.log (Z x) := by
    funext x
    simp only [OAI.SK.Analytic.vectorStep, OAI.SK.Analytic.gaussianStep, hm0.ne', ite_false,
      OAI.SK.Analytic.positiveGaussianLogStep, Z, q, SKBarriers2.gaussianAverage, smul_eq_mul, div_eq_inv_mul]
  rw [heq]
  apply hs.mono
  rw [abs_of_pos (inv_pos.mpr hm0)]
  apply mul_le_mul_of_nonneg_right (inv_anti₀ ha ham)
  exact hL.nonneg

end QBoundedJets

theorem vectorStep_zero_mass_eq_gaussianAverage {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (v : E) (f : E → ℝ) :
    OAI.SK.Analytic.vectorStep 0 v f = gaussianAverage v f := by
  funext x
  simp only [OAI.SK.Analytic.vectorStep, OAI.SK.Analytic.gaussianStep, ite_true, gaussianAverage]

theorem QBddSmooth.vectorStep_zero_mass {r : ℕ} {B : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QBddSmooth r B f) (v : Fin 3 → ℝ) :
    QBddSmooth r B (OAI.SK.Analytic.vectorStep 0 v f) := by
  rw [vectorStep_zero_mass_eq_gaussianAverage]
  exact qBoundedJets_iff_qBddSmooth.mp ((qBoundedJets_iff_qBddSmooth.mpr hf).gaussianAverage v)

theorem QBddSmooth.vectorStep {r : ℕ} {B a m : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QBddSmooth r B f) (ha : 0 < a) (ham : a ≤ m) (hm : m ≤ 1)
    (v : Fin 3 → ℝ) :
    QBddSmooth r (positiveStepJetBound r B a) (OAI.SK.Analytic.vectorStep m v f) := by
  exact qBoundedJets_iff_qBddSmooth.mp
    ((qBoundedJets_iff_qBddSmooth.mpr hf).vectorStep ha ham hm v)

section Parameters

variable {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem vectorStep_parameter_slice (m : ℝ) (v : E) (f : E × P → ℝ) (x : E) (p : P) :
    OAI.SK.Analytic.vectorStep m (v, (0 : P)) f (x, p) =
      OAI.SK.Analytic.vectorStep m v (fun y => f (y, p)) x := by
  simp only [OAI.SK.Analytic.vectorStep, OAI.SK.Analytic.gaussianStep,
    OAI.SK.Analytic.positiveGaussianLogStep, Prod.smul_mk, Prod.mk_add_mk,
    smul_zero, add_zero]

theorem vectorStep_parameter_jets {r : ℕ} {B a m : ℝ} {f : E × P → ℝ}
    (hf : QBoundedJets (r + 2) B f) (ha : 0 < a) (ham : a ≤ m) (hm : m ≤ 1) (v : E) :
    QBoundedJets (r + 2) (positiveStepJetBound (r + 2) B a)
      (OAI.SK.Analytic.vectorStep m (v, (0 : P)) f) ∧
    QBoundedJets r (positiveStepJetBound (r + 2) B a)
      (fderiv ℝ (fderiv ℝ (OAI.SK.Analytic.vectorStep m (v, (0 : P)) f))) := by
  have hs := hf.vectorStep ha ham hm (v, (0 : P))
  exact ⟨hs, hs.derivativeJets.derivativeJets⟩

end Parameters

end SKBarriers2
