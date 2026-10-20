module

public import SKBarriers2.Analysis.WeightedJets
public import OAI.Probability.SKBarriers.Replicas.VectorBranch

@[expose] public section

noncomputable section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialRescale (ρ : ℝ) (c : E) (f : E → ℝ) : E → ℝ :=
  fun y => f (ρ • y + c)

def scaleDirections (ρ : ℝ) (l : List (ℝ × E)) : List (ℝ × E) :=
  l.map (fun u => (u.1, ρ • u.2))

theorem spatialRescale_vectorStep (ρ m : ℝ) (c v : E) (f : E → ℝ) :
    spatialRescale ρ c (vectorStep m (ρ • v) f) =
      vectorStep m v (spatialRescale ρ c f) := by
  have he (y : E) (t : ℝ) :
      ρ • y + c + t • (ρ • v) = ρ • (y + t • v) + c := by
    simp only [smul_add, smul_smul]
    rw [mul_comm t ρ]
    abel
  funext y
  simp only [spatialRescale, vectorStep, gaussianStep, positiveGaussianLogStep]
  simp_rw [he]

theorem spatialRescale_vectorIncrementChain (ρ : ℝ) (c : E)
    (l : List (ℝ × E)) (f : E → ℝ) :
    spatialRescale ρ c (vectorIncrementChain (scaleDirections ρ l) f) =
      vectorIncrementChain l (spatialRescale ρ c f) := by
  induction l with
  | nil => rfl
  | cons u l ih =>
    change spatialRescale ρ c (vectorStep u.1 (ρ • u.2)
      (vectorIncrementChain (scaleDirections ρ l) f)) = _
    rw [spatialRescale_vectorStep, ih]
    rfl

theorem scaleDirections_inv {ρ : ℝ} (hρ : ρ ≠ 0) (l : List (ℝ × E)) :
    scaleDirections ρ (scaleDirections ρ⁻¹ l) = l := by
  simp only [scaleDirections, List.map_map, Function.comp_def, smul_smul,
    mul_inv_cancel₀ hρ, one_smul, Prod.eta]
  exact List.map_id' l

theorem spatialRescale_chain {ρ : ℝ} (hρ : ρ ≠ 0) (c : E)
    (l : List (ℝ × E)) (f : E → ℝ) :
    spatialRescale ρ c (vectorIncrementChain l f) =
      vectorIncrementChain (scaleDirections ρ⁻¹ l) (spatialRescale ρ c f) := by
  simpa only [scaleDirections_inv hρ] using
    spatialRescale_vectorIncrementChain ρ c (scaleDirections ρ⁻¹ l) f

theorem iteratedFDeriv_spatialRescale {r j : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ r f) (hj : j ≤ r) (ρ : ℝ) (c y : E) :
    iteratedFDeriv ℝ j (spatialRescale ρ c f) y =
      ρ ^ j • iteratedFDeriv ℝ j f (ρ • y + c) := by
  change iteratedFDeriv ℝ j (fun y => (fun x => f (x + c)) (ρ • y)) y = _
  have hs : ContDiff ℝ j (fun x => f (x + c)) :=
    (hf.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast hj)
  rw [iteratedFDeriv_comp_const_smul ρ hs]
  dsimp only
  rw [iteratedFDeriv_comp_add_right]

theorem norm_iteratedFDeriv_spatialRescale {r j : ℕ} {f : E → ℝ}
    (hf : ContDiff ℝ r f) (hj : j ≤ r) (ρ : ℝ) (c y : E) :
    ‖iteratedFDeriv ℝ j (spatialRescale ρ c f) y‖ =
      |ρ| ^ j * ‖iteratedFDeriv ℝ j f (ρ • y + c)‖ := by
  rw [iteratedFDeriv_spatialRescale hf hj, norm_smul, Real.norm_eq_abs, abs_pow]

theorem contDiff_of_spatialRescale {r : ℕ} {ρ : ℝ} {c : E} {f : E → ℝ}
    (hρ : ρ ≠ 0) (hf : ContDiff ℝ r (spatialRescale ρ c f)) : ContDiff ℝ r f := by
  have hi : ContDiff ℝ r (fun x : E => ρ⁻¹ • (x - c)) := by fun_prop
  have H := hf.comp hi
  convert H using 1
  funext x
  change f x = f (ρ • (ρ⁻¹ • (x - c)) + c)
  rw [smul_smul, mul_inv_cancel₀ hρ, one_smul, sub_add_cancel]

theorem WJets.spatial_unscale_bound {r p j : ℕ} {B ρ : ℝ} {c : E} {f : E → ℝ}
    (hf : WJets r B p (spatialRescale ρ c f)) (hρ : ρ ≠ 0) (hj : j ≤ r) (y : E) :
    |ρ| ^ j * ‖iteratedFDeriv ℝ j f (ρ • y + c)‖ ≤ B * (1 + ‖y‖) ^ p := by
  rw [← norm_iteratedFDeriv_spatialRescale (contDiff_of_spatialRescale hρ hf.smooth) hj]
  exact hf.bound j hj y

theorem chain_variation_scale (l : List (ℝ × E)) (f g : E → ℝ) (δ ε : ℝ) :
    vectorIncrementChain l (fun x => f x + ε * (δ * g x)) =
      vectorIncrementChain l (fun x => f x + (δ * ε) * g x) := by
  congr 1
  funext x
  ring

theorem iteratedDeriv_comp_mul_left (n : ℕ) (f : ℝ → ℝ) (δ : ℝ) :
    iteratedDeriv n (fun a => f (δ * a)) =
      fun a => δ ^ n * iteratedDeriv n f (δ * a) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext a
    rw [deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, ← iteratedDeriv_succ]
    ring

theorem iteratedDeriv_chain_variation_scale {n : ℕ} (l : List (ℝ × E))
    (f g : E → ℝ) (δ ε : ℝ) (x : E) :
    iteratedDeriv n
        (fun a => vectorIncrementChain l (fun y => f y + a * (δ * g y)) x) ε =
      δ ^ n * iteratedDeriv n
        (fun a => vectorIncrementChain l (fun y => f y + a * g y) x) (δ * ε) := by
  simp_rw [chain_variation_scale]
  exact congrFun (iteratedDeriv_comp_mul_left n
    (fun a => vectorIncrementChain l (fun y => f y + a * g y) x) δ) ε

def normalizedVariationChain (l : List (ℝ × E)) (f g : E → ℝ)
    (ρ : ℝ) (c : E) (τ : ℝ) : E → ℝ :=
  vectorIncrementChain (scaleDirections ρ⁻¹ l)
    (fun y => spatialRescale ρ c f y + τ * ((ρ ^ 3)⁻¹ * spatialRescale ρ c g y))

theorem spatialRescale_variationChain {ρ : ℝ} (hρ : ρ ≠ 0)
    (l : List (ℝ × E)) (f g : E → ℝ) (c : E) (ε : ℝ) :
    spatialRescale ρ c (vectorIncrementChain l (fun x => f x + ε * g x)) =
      normalizedVariationChain l f g ρ c (ρ ^ 3 * ε) := by
  rw [spatialRescale_chain hρ]
  unfold normalizedVariationChain
  congr 1
  funext y
  dsimp only [spatialRescale]
  field_simp

theorem iteratedDeriv_spatialRescale_variationChain {ρ : ℝ} (hρ : ρ ≠ 0)
    (l : List (ℝ × E)) (f g : E → ℝ) (c y : E) (n : ℕ) (ε : ℝ) :
    iteratedDeriv n
        (fun a => vectorIncrementChain l (fun x => f x + a * g x) (ρ • y + c)) ε =
      (ρ ^ 3) ^ n * iteratedDeriv n
        (fun a => normalizedVariationChain l f g ρ c a y) (ρ ^ 3 * ε) := by
  have he (a : ℝ) : vectorIncrementChain l (fun x => f x + a * g x) (ρ • y + c) =
      normalizedVariationChain l f g ρ c (ρ ^ 3 * a) y :=
    congrFun (spatialRescale_variationChain hρ l f g c a) y
  simp_rw [he]
  exact congrFun (iteratedDeriv_comp_mul_left n
    (fun a => normalizedVariationChain l f g ρ c a y) (ρ ^ 3)) ε

theorem iteratedDeriv_mixed_scaledChain {ρ : ℝ} (hρ : ρ ≠ 0)
    (l : ℝ → List (ℝ × E)) (f g : E → ℝ) (c y : E) (n a : ℕ) (ε k : ℝ) :
    iteratedDeriv a (fun t => iteratedDeriv n
        (fun e => vectorIncrementChain (l t) (fun x => f x + e * g x)
          (ρ • y + c)) ε) k =
      (ρ ^ 3) ^ n * iteratedDeriv a (fun t => iteratedDeriv n
        (fun e => normalizedVariationChain (l t) f g ρ c e y) (ρ ^ 3 * ε)) k := by
  simp_rw [iteratedDeriv_spatialRescale_variationChain hρ]
  exact iteratedDeriv_const_mul_field _ _

theorem iteratedDeriv_mixed_scaledChain_along {ρ : ℝ} (hρ : ρ ≠ 0)
    (l : ℝ → List (ℝ × E)) (f g : E → ℝ) (c : E) (y : ℝ → E)
    (n a : ℕ) (ε k : ℝ) :
    iteratedDeriv a (fun t => iteratedDeriv n
        (fun e => vectorIncrementChain (l t) (fun x => f x + e * g x)
          (ρ • y t + c)) ε) k =
      (ρ ^ 3) ^ n * iteratedDeriv a (fun t => iteratedDeriv n
        (fun e => normalizedVariationChain (l t) f g ρ c e (y t)) (ρ ^ 3 * ε)) k := by
  simp_rw [iteratedDeriv_spatialRescale_variationChain hρ]
  exact iteratedDeriv_const_mul_field _ _

theorem QPotential.spatialRescale {r : ℕ} {B ρ : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential r B f) (hρ : |ρ| ≤ 1) (c : Fin 3 → ℝ) :
    QPotential r B (spatialRescale ρ c f) := by
  refine ⟨hf.nonneg, hf.smooth.comp ((contDiff_id.const_smul ρ).add contDiff_const), ?_⟩
  intro j hj hjr y
  rw [norm_iteratedFDeriv_spatialRescale hf.smooth hjr]
  exact (mul_le_mul_of_nonneg_left (hf.bound j hj hjr _) (pow_nonneg (abs_nonneg _) _)).trans
    (mul_le_of_le_one_left hf.nonneg (pow_le_one₀ (abs_nonneg _) hρ))

theorem QPotential.dilate {r : ℕ} {B ρ : ℝ} {f : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential r B f) (hρ : 1 ≤ ρ) :
    QPotential r (B * ρ ^ r) (SKBarriers2.spatialRescale ρ 0 f) := by
  have hρ₀ : 0 ≤ ρ := by linarith
  refine ⟨by positivity [hf.nonneg],
    hf.smooth.comp ((contDiff_id.const_smul ρ).add contDiff_const), ?_⟩
  intro j hj hjr y
  rw [norm_iteratedFDeriv_spatialRescale hf.smooth hjr, abs_of_nonneg hρ₀]
  exact (mul_le_mul_of_nonneg_left (hf.bound j hj hjr _) (pow_nonneg hρ₀ _)).trans
    (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hρ hjr) hf.nonneg)

theorem WJets.spatialContract {r p : ℕ} {B ρ : ℝ} {f : E → ℝ}
    (hf : WJets r B p f) (hρ : |ρ| ≤ 1) :
    WJets r B p (spatialRescale ρ 0 f) := by
  refine ⟨hf.nonneg, hf.smooth.comp ((contDiff_id.const_smul ρ).add contDiff_const), ?_⟩
  intro j hj y
  rw [norm_iteratedFDeriv_spatialRescale hf.smooth hj]
  have hw : (1 + ‖ρ • y + (0 : E)‖) ^ p ≤ (1 + ‖y‖) ^ p := by
    rw [add_zero, norm_smul, Real.norm_eq_abs]
    gcongr
    exact mul_le_of_le_one_left (norm_nonneg y) hρ
  exact (mul_le_mul (pow_le_one₀ (abs_nonneg _) hρ)
    ((hf.bound j hj _).trans (mul_le_mul_of_nonneg_left hw hf.nonneg))
    (norm_nonneg _) (by positivity)).trans_eq (one_mul _)

theorem WJets.dilate {r p : ℕ} {B ρ : ℝ} {f : E → ℝ}
    (hf : WJets r B p f) (hρ : 1 ≤ ρ) :
    WJets r (B * ρ ^ (p + r)) p (spatialRescale ρ 0 f) := by
  have hρ₀ : 0 ≤ ρ := by linarith
  refine ⟨by positivity [hf.nonneg],
    hf.smooth.comp ((contDiff_id.const_smul ρ).add contDiff_const), ?_⟩
  intro j hj y
  rw [norm_iteratedFDeriv_spatialRescale hf.smooth hj, abs_of_nonneg hρ₀]
  have hw : (1 + ‖ρ • y + (0 : E)‖) ^ p ≤ ρ ^ p * (1 + ‖y‖) ^ p := by
    rw [add_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ₀, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  calc
    _ ≤ ρ ^ r * (B * (ρ ^ p * (1 + ‖y‖) ^ p)) :=
      mul_le_mul (pow_le_pow_right₀ hρ hj)
        ((hf.bound j hj _).trans (mul_le_mul_of_nonneg_left hw hf.nonneg))
        (norm_nonneg _) (pow_nonneg hρ₀ _)
    _ = _ := by rw [pow_add]; ring

namespace StepCalculus

local notation "X" => (Fin 3 → ℝ)

theorem affine_rescale {ρ : ℝ} (hρ : ρ ≠ 0) (A : X →L[ℝ] X) (b c y : X) :
    A (ρ • y + c) + b =
      ρ • (A y + ρ⁻¹ • (A c + b - c)) + c := by
  rw [map_add, map_smul, smul_add, smul_smul, mul_inv_cancel₀ hρ, one_smul]
  abel

theorem spatialRescale_tiltedAverage (ρ m : ℝ) (c v : X) (f g : X → ℝ) :
    spatialRescale ρ c (tiltedAverage m (ρ • v) f g) =
      tiltedAverage m v (spatialRescale ρ c f) (spatialRescale ρ c g) := by
  have he (y : X) (t : ℝ) :
      ρ • y + c + t • (ρ • v) = ρ • (y + t • v) + c := by
    simp only [smul_add, smul_smul]
    rw [mul_comm t ρ]
    abel
  funext y
  change (∫ t : ℝ, g (ρ • y + c + t • (ρ • v))
    ∂(gaussianReal 0 1).tilted (fun t => m * f (ρ • y + c + t • (ρ • v)))) =
      ∫ t : ℝ, g (ρ • (y + t • v) + c)
        ∂(gaussianReal 0 1).tilted (fun t => m * f (ρ • (y + t • v) + c))
  simp_rw [he]

theorem spatialRescale_affine_tiltedAverage {ρ : ℝ} (hρ : ρ ≠ 0)
    (m : ℝ) (A : X →L[ℝ] X) (b c v : X) (f g : X → ℝ) :
    spatialRescale ρ c (fun x => tiltedAverage m v f g (A x + b)) =
      fun y => tiltedAverage m (ρ⁻¹ • v) (spatialRescale ρ c f)
        (spatialRescale ρ c g) (A y + ρ⁻¹ • (A c + b - c)) := by
  have H := spatialRescale_tiltedAverage ρ m c (ρ⁻¹ • v) f g
  simp only [smul_smul, mul_inv_cancel₀ hρ, one_smul] at H
  funext y
  have Hy := congrFun H (A y + ρ⁻¹ • (A c + b - c))
  dsimp only [spatialRescale] at Hy ⊢
  rw [← affine_rescale hρ] at Hy
  exact Hy

theorem wJets_tiltedAverage_boundedNoise {r p : ℕ} {B C m K : ℝ} {f g : X → ℝ}
    (hf : QPotential (r + 1) B f) (hg : WJets r C p g)
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K) :
    WJets r (noiseAverageCoefficient r p (B * K ^ (r + 1)) *
      (C * K ^ (p + r))) p (tiltedAverage m v f g) := by
  have hK₀ : 0 < K := by linarith
  have hKi : |K⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hK₀)]
    exact (inv_le_one₀ hK₀).mpr hK
  have hv' : ‖K⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK₀)]
    exact (mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hK₀.le)).trans_eq
      (inv_mul_cancel₀ hK₀.ne')
  have H := (wJets_tiltedAverage (hf.dilate hK) (hg.dilate hK) hm (K⁻¹ • v) hv').spatialContract hKi
  have he : spatialRescale K⁻¹ 0
      (tiltedAverage m (K⁻¹ • v) (spatialRescale K 0 f) (spatialRescale K 0 g)) =
      tiltedAverage m v f g := by
    rw [← spatialRescale_tiltedAverage]
    simp only [smul_smul, mul_inv_cancel₀ hK₀.ne', one_smul]
    funext x
    simp only [spatialRescale, add_zero, smul_smul, mul_inv_cancel₀ hK₀.ne', one_smul]
  rw [he] at H
  exact H

theorem wJets_affineAverage_boundedNoise {r p : ℕ} {B C m K : ℝ} {f g : X → ℝ}
    (hf : QPotential (r + 1) B f) (hg : WJets r C p g)
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K)
    (A : X →L[ℝ] X) (b : X) :
    WJets r ((noiseAverageCoefficient r p (B * K ^ (r + 1)) *
      (C * K ^ (p + r))) * (1 + ‖A‖ + ‖b‖) ^ p * max 1 ‖A‖ ^ r) p
      (fun y => tiltedAverage m v f g (A y + b)) := by
  exact (wJets_tiltedAverage_boundedNoise hf hg hm hK v hv).comp_affine A b

theorem wJets_spatialCovariance_boundedNoise {r p q : ℕ} {B C D m K : ℝ}
    {f g a : X → ℝ} (hf : QPotential (r + 1) B f)
    (hg : WJets r C p g) (ha : WJets r D q a)
    (hm : m ∈ Icc (0 : ℝ) 1) (hK : 1 ≤ K) (v : X) (hv : ‖v‖ ≤ K) :
    WJets r
      (noiseAverageCoefficient r (p + q) (B * K ^ (r + 1)) *
          (((2 : ℝ) ^ r * C * D) * K ^ (p + q + r)) +
        (2 : ℝ) ^ r *
          (noiseAverageCoefficient r p (B * K ^ (r + 1)) * (C * K ^ (p + r))) *
          (noiseAverageCoefficient r q (B * K ^ (r + 1)) * (D * K ^ (q + r))))
      (p + q) (spatialCovariance m v f g a) := by
  exact (wJets_tiltedAverage_boundedNoise hf (hg.mul ha) hm hK v hv).sub
    ((wJets_tiltedAverage_boundedNoise hf hg hm hK v hv).mul
      (wJets_tiltedAverage_boundedNoise hf ha hm hK v hv))

end StepCalculus

end SKBarriers2
