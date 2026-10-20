module

public import SKBarriers2.Analysis.QSmooth
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SKBarriers2

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure QBoundedJets (r : ℕ) (B : ℝ) (f : E → F) : Prop where
  nonneg : 0 ≤ B
  smooth : ContDiff ℝ r f
  bound : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B

namespace QBoundedJets

variable {r s : ℕ} {B C : ℝ} {f g : E → F}

theorem of_le (hf : QBoundedJets r B f) (hs : s ≤ r) : QBoundedJets s B f := by
  exact ⟨hf.nonneg, hf.smooth.of_le (by exact_mod_cast hs),
    fun j hj x => hf.bound j (hj.trans hs) x⟩

theorem mono (hf : QBoundedJets r B f) (hBC : B ≤ C) : QBoundedJets r C f := by
  exact ⟨hf.nonneg.trans hBC, hf.smooth, fun j hj x => (hf.bound j hj x).trans hBC⟩

theorem norm_le (hf : QBoundedJets r B f) (x : E) : ‖f x‖ ≤ B := by
  simpa only [norm_iteratedFDeriv_zero] using hf.bound 0 (Nat.zero_le r) x

theorem derivativeJets (hf : QBoundedJets (r + 1) B f) :
    QBoundedJets r B (fderiv ℝ f) := by
  refine ⟨hf.nonneg, hf.smooth.fderiv_right (by simp), ?_⟩
  intro j hj x
  rw [norm_iteratedFDeriv_fderiv]
  exact hf.bound (j + 1) (by omega) x

theorem translate (hf : QBoundedJets r B f) (a : E) :
    QBoundedJets r B (fun x => f (x + a)) := by
  refine ⟨hf.nonneg, hf.smooth.comp (contDiff_id.add contDiff_const), ?_⟩
  intro j hj x
  rw [iteratedFDeriv_comp_add_right]
  exact hf.bound j hj (x + a)

theorem add (hf : QBoundedJets r B f) (hg : QBoundedJets r C g) :
    QBoundedJets r (B + C) (fun x => f x + g x) := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.add hg.smooth, ?_⟩
  intro j hj x
  change ‖iteratedFDeriv ℝ j (f + g) x‖ ≤ B + C
  rw [iteratedFDeriv_add (hf.smooth.of_le (by exact_mod_cast hj))
    (hg.smooth.of_le (by exact_mod_cast hj))]
  exact (norm_add_le _ _).trans (add_le_add (hf.bound j hj x) (hg.bound j hj x))

theorem const_smul (hf : QBoundedJets r B f) (c : ℝ) :
    QBoundedJets r (|c| * B) (fun x => c • f x) := by
  refine ⟨mul_nonneg (abs_nonneg c) hf.nonneg, hf.smooth.const_smul c, ?_⟩
  intro j hj x
  rw [iteratedFDeriv_const_smul_apply'
    ((hf.smooth.of_le (by exact_mod_cast hj)).contDiffAt), norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hf.bound j hj x) (abs_nonneg c)

theorem isometryEquiv_comp {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hf : QBoundedJets r B f) (L : F ≃ₗᵢ[ℝ] G) : QBoundedJets r B (L ∘ f) := by
  refine ⟨hf.nonneg, L.toContinuousLinearEquiv.contDiff.comp hf.smooth, ?_⟩
  intro j hj x
  rw [L.norm_iteratedFDeriv_comp_left]
  exact hf.bound j hj x

theorem jet (n : ℕ) (hf : QBoundedJets (r + n) B f) :
    QBoundedJets r B (iteratedFDeriv ℝ n f) := by
  induction n generalizing F r with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (hf.of_le (by omega : r ≤ r + 0)).isometryEquiv_comp
      (continuousMultilinearCurryFin0 ℝ E F).symm
  | succ n ih =>
    have hh : QBoundedJets ((r + n) + 1) B f := by
      convert hf using 1
    have h := (ih hh.derivativeJets).isometryEquiv_comp
      (continuousMultilinearCurryRightEquiv' ℝ n E F).symm
    convert h using 1
    funext x
    exact iteratedFDeriv_succ_eq_comp_right

theorem lipschitzWith (hf : QBoundedJets (r + 1) B f) :
    LipschitzWith ⟨B, hf.nonneg⟩ f := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hf.smooth.differentiable (by norm_cast))
  intro x
  exact_mod_cast hf.derivativeJets.norm_le x

theorem comp {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : F → G} (hg : QBoundedJets r C g) (hf : QBoundedJets r B f) :
    QBoundedJets r ((r.factorial : ℝ) * C * (1 + B) ^ r) (g ∘ f) := by
  have hB : 1 ≤ 1 + B := by linarith [hf.nonneg]
  have hC0 : 0 ≤ C := hg.nonneg
  refine ⟨by positivity, hg.smooth.comp hf.smooth, ?_⟩
  intro j hj x
  calc
    ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ (j.factorial : ℝ) * C * (1 + B) ^ j := by
      apply norm_iteratedFDeriv_comp_le hg.smooth hf.smooth (by exact_mod_cast hj)
      · intro i hi
        exact hg.bound i (hi.trans hj) (f x)
      · intro i hi hir
        exact (hf.bound i (hir.trans hj) x).trans
          ((by linarith : B ≤ 1 + B).trans (le_self_pow₀ hB (by omega)))
    _ ≤ (r.factorial : ℝ) * C * (1 + B) ^ r := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity)
      · exact pow_le_pow_right₀ hB hj
      · positivity
      · positivity

theorem mul {f g : E → ℝ} (hf : QBoundedJets r B f) (hg : QBoundedJets r C g) :
    QBoundedJets r ((2 : ℝ) ^ r * B * C) (fun x => f x * g x) := by
  have hB0 : 0 ≤ B := hf.nonneg
  have hC0 : 0 ≤ C := hg.nonneg
  refine ⟨by positivity, hf.smooth.mul hg.smooth, ?_⟩
  intro j hj x
  calc
    ‖iteratedFDeriv ℝ j (fun x => f x * g x) x‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf.smooth hg.smooth x (by exact_mod_cast hj)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * C := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      gcongr
      · exact hf.bound i (hi'.trans hj) x
      · exact hg.bound (j - i) (by omega) x
    _ = (2 : ℝ) ^ j * B * C := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 : ℝ) ^ r * B * C := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hB0) hC0

theorem exp {f : E → ℝ} (hf : QBoundedJets r B f) :
    QBoundedJets r ((r.factorial : ℝ) * Real.exp B * (1 + B) ^ r)
      (fun x => Real.exp (f x)) := by
  have hB : 1 ≤ 1 + B := by linarith [hf.nonneg]
  refine ⟨by positivity, hf.smooth.exp, ?_⟩
  intro j hj x
  calc
    ‖iteratedFDeriv ℝ j (fun x => Real.exp (f x)) x‖ ≤
        (j.factorial : ℝ) * Real.exp B * (1 + B) ^ j := by
      apply norm_iteratedFDeriv_comp_le Real.contDiff_exp hf.smooth (by exact_mod_cast hj)
      · intro i _
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
          Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hf.norm_le x))
      · intro i hi hir
        exact (hf.bound i (hir.trans hj) x).trans
          ((by linarith : B ≤ 1 + B).trans (le_self_pow₀ hB (by omega)))
    _ ≤ (r.factorial : ℝ) * Real.exp B * (1 + B) ^ r := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity)
      · exact pow_le_pow_right₀ hB hj
      · positivity
      · positivity

end QBoundedJets

theorem qBoundedJets_iff_qBddSmooth {r : ℕ} {B : ℝ} {f : (Fin 3 → ℝ) → ℝ} :
    QBoundedJets r B f ↔ QBddSmooth r B f := by
  exact ⟨fun h => ⟨h.nonneg, h.smooth, h.bound⟩,
    fun h => ⟨h.nonneg, h.smooth, h.bound⟩⟩

def gaussianAverage (v : E) (f : E → F) (x : E) : F :=
  ∫ t : ℝ, f (x + t • v) ∂gaussianReal 0 1

namespace QBoundedJets

variable {r : ℕ} {B : ℝ} {f : E → F}

theorem integrable_shift (hf : QBoundedJets r B f) (v x : E) :
    Integrable (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1) := by
  apply Integrable.of_bound
    ((hf.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable) B
  exact ae_of_all _ (fun t => hf.norm_le (x + t • v))

theorem continuous_gaussianAverage (hf : QBoundedJets r B f) (v : E) :
    Continuous (gaussianAverage v f) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => B)
  · intro x
    exact (hf.integrable_shift v x).aestronglyMeasurable
  · intro x
    exact ae_of_all _ (fun t => hf.norm_le (x + t • v))
  · exact integrable_const B
  · exact ae_of_all _ (fun t => hf.smooth.continuous.comp (continuous_id.add continuous_const))

theorem hasFDerivAt_gaussianAverage (hf : QBoundedJets (r + 1) B f) (v x : E) :
    HasFDerivAt (gaussianAverage v f) (gaussianAverage v (fderiv ℝ f) x) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := univ) (bound := fun _ : ℝ => B) (F' := fun y t => fderiv ℝ f (y + t • v))
  · exact univ_mem
  · exact Eventually.of_forall (fun y => (hf.integrable_shift v y).aestronglyMeasurable)
  · exact hf.integrable_shift v x
  · exact (hf.derivativeJets.integrable_shift v x).aestronglyMeasurable
  · exact ae_of_all _ (fun t y _ => hf.derivativeJets.norm_le (y + t • v))
  · exact integrable_const B
  · apply ae_of_all
    intro t y _
    have hd : Differentiable ℝ f := hf.smooth.differentiable (by norm_cast)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      (hd (y + t • v)).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const (t • v))

theorem fderiv_gaussianAverage (hf : QBoundedJets (r + 1) B f) (v : E) :
    fderiv ℝ (gaussianAverage v f) = gaussianAverage v (fderiv ℝ f) := by
  funext x
  exact (hf.hasFDerivAt_gaussianAverage v x).fderiv

theorem gaussianAverage (hf : QBoundedJets r B f) (v : E) :
    QBoundedJets r B (SKBarriers2.gaussianAverage v f) := by
  induction r generalizing F with
  | zero =>
    refine ⟨hf.nonneg, contDiff_zero.mpr (hf.continuous_gaussianAverage v), ?_⟩
    intro j hj x
    have hj0 : j = 0 := by omega
    subst j
    rw [norm_iteratedFDeriv_zero]
    exact (norm_integral_le_of_norm_le_const (ae_of_all _
      (fun t => hf.norm_le (x + t • v)))).trans_eq (by simp)
  | succ r ih =>
    have hg : QBoundedJets r B (SKBarriers2.gaussianAverage v (fderiv ℝ f)) := ih hf.derivativeJets
    refine ⟨hf.nonneg, contDiff_succ_iff_hasFDerivAt.mpr
      ⟨_, hg.smooth, hf.hasFDerivAt_gaussianAverage v⟩, ?_⟩
    intro j hj x
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (norm_integral_le_of_norm_le_const (ae_of_all _
        (fun t => hf.norm_le (x + t • v)))).trans_eq (by simp)
    | succ j =>
      rw [← norm_iteratedFDeriv_fderiv, hf.fderiv_gaussianAverage v]
      exact hg.bound j (by omega) x

theorem iteratedFDeriv_gaussianAverage (hf : QBoundedJets r B f) (v : E)
    (j : ℕ) (hj : j ≤ r) (x : E) :
    iteratedFDeriv ℝ j (SKBarriers2.gaussianAverage v f) x =
      SKBarriers2.gaussianAverage v (iteratedFDeriv ℝ j f) x := by
  induction j generalizing F r with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm
      (fun t : ℝ => f (x + t • v))).symm
  | succ j ih =>
    have hf' : QBoundedJets (j + 1) B f := hf.of_le hj
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      hf'.fderiv_gaussianAverage v, ih hf'.derivativeJets le_rfl]
    convert!
      ((continuousMultilinearCurryRightEquiv' ℝ j E F).symm.toContinuousLinearEquiv.integral_comp_comm
        (μ := gaussianReal 0 1)
        (fun t : ℝ => iteratedFDeriv ℝ j (fderiv ℝ f) (x + t • v))).symm using 1
    exact integral_congr_ae (ae_of_all _ (fun _ => iteratedFDeriv_succ_eq_comp_right))

end QBoundedJets

end SKBarriers2
