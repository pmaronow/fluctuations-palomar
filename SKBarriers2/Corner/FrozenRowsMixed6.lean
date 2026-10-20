module

public import SKBarriers2.Analysis.ParamStep4

@[expose] public section

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
open scoped Topology

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance fixedMassLinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fixedMassLinearNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fixedMassBilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fixedMassBilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem qBoundedJets_fixedMassSecondCenteredScore_order {n : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential (n + 2) B f) (hg : QBoundedJets (n + 2) A g)
    (μ : ℝ) (v w : E) (t : ℝ) :
    QBoundedJets n ((A * ‖v‖ + |μ| * B * ‖v‖ + B * ‖w‖) * |t|)
      (fun x => secondCenteredScore μ v w f g x t) := by
  have hgp : QPotential (n + 1) A g :=
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : n + 1 ≤ n + 2))).potential
  have hG := hgp.increment (t • v)
  have hF := ((hf.of_le (by omega : n + 1 ≤ n + 2)).increment (t • v)).const_smul μ
  have hD := (((hf.derivativeJets.of_le (by omega : n ≤ n + 1)).apply_const w).translate
    (t • v)).const_smul t
  convert (hG.add hF).add hD using 1
  · rw [norm_smul, Real.norm_eq_abs]
    ring
  · rfl

theorem qBoundedJets_fixedMassSecondScoreVariance_order {n : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential (n + 2) B f) (hg : QBoundedJets (n + 2) A g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (μ : ℝ) (v w : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets n
      (potentialCovarianceCoefficient n B *
        (A * ‖v‖ + |μ| * B * ‖v‖ + B * ‖w‖) ^ 2)
      (secondScoreVariance m μ v w f g) := by
  let C := A * ‖v‖ + |μ| * B * ‖v‖ + B * ‖w‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity [hf.nonneg, hg.nonneg]
  have hR : ContDiff ℝ n (fun z : ℝ × E => secondCenteredScore μ v w f g z.2 z.1) := by
    have hline : ContDiff ℝ n (fun z : ℝ × E => z.2 + z.1 • v) :=
      contDiff_snd.add (contDiff_fst.smul contDiff_const)
    have hD : ContDiff ℝ n (fun z : ℝ × E => fderiv ℝ f (z.2 + z.1 • v) w) :=
      ((hf.smooth.fderiv_right (m := n) (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))).comp
        hline).clm_apply contDiff_const
    have hfs : ContDiff ℝ n f := hf.smooth.of_le (by exact_mod_cast (show n ≤ n + 2 by omega))
    have hgs : ContDiff ℝ n g := hg.smooth.of_le (by exact_mod_cast (show n ≤ n + 2 by omega))
    exact ((hgs.comp hline).sub (hgs.comp contDiff_snd)).add
      (contDiff_const.mul ((hfs.comp hline).sub (hfs.comp contDiff_snd)))
      |>.add (contDiff_fst.mul hD)
  have hRj (t : ℝ) : QBoundedJets n (C * |t| ^ 1)
      (fun x => secondCenteredScore μ v w f g x t) := by
    simpa only [pow_one] using qBoundedJets_fixedMassSecondCenteredScore_order hf hg μ v w t
  have hR2j (t : ℝ) : QBoundedJets n (((2 : ℝ) ^ n * C ^ 2) * |t| ^ 2)
      (fun x => secondCenteredScore μ v w f g x t ^ 2) := by
    convert (hRj t).mul (hRj t) using 1
    · ring
    · funext x
      ring
  have hR2 : ContDiff ℝ n (fun z : ℝ × E => secondCenteredScore μ v w f g z.2 z.1 ^ 2) :=
    hR.pow 2
  have hM := qBoundedJets_noiseMean_poly (hf.of_le (by omega : n + 1 ≤ n + 2)) hC 1 hR hRj hm v hv
  have hM2 := qBoundedJets_noiseMean_poly (g := fun x t => secondCenteredScore μ v w f g x t ^ 2)
    (hf.of_le (by omega : n + 1 ≤ n + 2))
    (show 0 ≤ (2 : ℝ) ^ n * C ^ 2 by positivity) 2 hR2 hR2j hm v hv
  convert hM2.sub (hM.mul hM) using 1
  · dsimp only [potentialCovarianceCoefficient]
    ring
  · funext x
    simp only [secondScoreVariance, pow_two]

theorem qBoundedJets_fixedMassMixedDirectionSource_order {n : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential (n + 2) B f) (hg : QBoundedJets (n + 2) A g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v w : E) :
    QBoundedJets n ((1 + (2 : ℝ) ^ n * B) * A * ‖v‖ * ‖w‖)
      (mixedDirectionSource m v w f g) := by
  have hH := (hg.derivativeJets.derivativeJets.apply_const v).apply_const w
  have hW := (hg.derivativeJets.of_le (by omega : n ≤ n + 1)).apply_const w
  have hV := (hf.derivativeJets.of_le (by omega : n ≤ n + 1)).apply_const v
  have H := hH.add ((hW.mul hV).const_smul m)
  apply H.mono
  rw [abs_of_nonneg hm.1]
  have h := mul_le_of_le_one_left
    (show 0 ≤ (2 : ℝ) ^ n * (A * ‖w‖) * (B * ‖v‖) by positivity [hf.nonneg, hg.nonneg]) hm.2
  nlinarith

theorem qBoundedJets_fixedMassNoiseHessian_order {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 2) B f) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v w : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets n (noiseAverageCoefficient n 2 B * B * ‖w‖ ^ 2)
      (fun x => noiseMean m v f x (fun t => t ^ 2 *
        fderiv ℝ (fderiv ℝ f) (x + t • v) w w)) := by
  have hH := (hf.derivativeJets.derivativeJets.apply_const w).apply_const w
  have hc : ContDiff ℝ n (fun z : ℝ × E => z.1 ^ 2 *
      fderiv ℝ (fderiv ℝ f) (z.2 + z.1 • v) w w) :=
    (contDiff_fst.pow 2).mul
      (hH.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const)))
  have hj (t : ℝ) : QBoundedJets n ((B * ‖w‖ ^ 2) * |t| ^ 2)
      (fun x => t ^ 2 * fderiv ℝ (fderiv ℝ f) (x + t • v) w w) := by
    convert (hH.translate (t • v)).const_smul (t ^ 2) using 1
    rw [abs_pow, sq_abs]
    ring
  convert qBoundedJets_noiseMean_poly
    (g := fun x t => t ^ 2 * fderiv ℝ (fderiv ℝ f) (x + t • v) w w)
    (hf.of_le (by omega : n + 1 ≤ n + 2))
    (show 0 ≤ B * ‖w‖ ^ 2 by positivity [hf.nonneg]) 2 hc hj hm v hv using 1
  ring

def fixedMassSecondVariationBound (n : ℕ) (B A H : ℝ) (v w b : E) : ℝ :=
  H + tiltedStabilityCoefficient n B * H * ‖v‖ ^ 2 +
    2 * (tiltedCoarseCoefficient n B * (1 + (2 : ℝ) ^ n * B)) * A * ‖v‖ * ‖w‖ +
    noiseAverageCoefficient n 2 B * B * ‖w‖ ^ 2 +
    directionSensitivityCoefficient n B * ‖v‖ * ‖b‖ +
    potentialCovarianceCoefficient n B * (A * ‖v‖ + B * ‖w‖) ^ 2

theorem qBoundedJets_fixedMassSecondVariationStep {n : ℕ} {B A H : ℝ} {f g h : E → ℝ}
    (hf : QPotential (n + 2) B f) (hg : QBoundedJets (n + 2) A g) (hh : QBoundedJets n H h)
    {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1) (v w b : E)
    (hv : ‖v‖ ≤ 1) (hsmall : B * ‖v‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets n (fixedMassSecondVariationBound n B A H v w b)
      (secondVariationStep m v f g h 0 0 w b) := by
  have hmcc : m ∈ Icc (0 : ℝ) 1 := ⟨hm.1.le, hm.2⟩
  have hcurv : m * (B * ‖v‖ ^ 2) ≤ 1 / 2 :=
    (mul_le_of_le_one_left (by positivity [hf.nonneg]) hm.2).trans hsmall
  have hT := qBoundedJets_tiltedAverage n hf (by omega) (by omega) hh hmcc v hcurv
  have hD := (qBoundedJets_tiltedAverage_coarse n hf (by omega) (by omega)
    (qBoundedJets_fixedMassMixedDirectionSource_order hf hg hmcc v w) hmcc v).const_smul 2
  have hN := qBoundedJets_fixedMassNoiseHessian_order hf hmcc v w hv
  have hB := qBoundedJets_directionSensitivity hf hmcc v b
  have hV := qBoundedJets_fixedMassSecondScoreVariance_order hf hg hmcc (0 / m) v w hv
  have hVm : QBoundedJets n
      (potentialCovarianceCoefficient n B * (A * ‖v‖ + B * ‖w‖) ^ 2)
      (fun x => m * secondScoreVariance m (0 / m) v w f g x) := by
    apply (hV.const_smul m).mono
    have Hm : |m| ≤ 1 := by rw [abs_of_pos hm.1]; exact hm.2
    simpa only [zero_div, abs_zero, zero_mul, add_zero] using
      mul_le_of_le_one_left hV.nonneg Hm
  convert (((hT.add hD).add hN).add hB).add hVm using 1
  · dsimp only [fixedMassSecondVariationBound]
    norm_num
    ring
  · funext x
    simp [secondVariationStep, smul_eq_mul]

end SKBarriers2.StepCalculus

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem qBoundedJets_second_deriv_exponential_fixedMassStep_order
    {n : ℕ} (hn : 1 ≤ n) {F : P × E → ℝ}
    (hF : ParamRegular F) (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) {B A H : ℝ}
    (hf : QPotential (n + 2) B (fun y => F (p k,y)))
    (hg : QBoundedJets (n + 2) A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hh : QBoundedJets n H (fun y =>
      fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0)))
    (hM₁ : M (deriv p k) = 0) (hM₂ : M (deriv (deriv p) k) = 0)
    (hm : Real.exp (M (p k)) ≤ 1) (hv : ‖V (p k)‖ ≤ 1)
    (hsmall : B * ‖V (p k)‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets n
      (fixedMassSecondVariationBound n B A H
        (V (p k)) (V (deriv p k)) (V (deriv (deriv p) k)))
      (fun x => deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
        (fun y => F (p t,y)) x)) k) := by
  have heq : (fun x => deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) x)) k) =
      secondVariationStep (Real.exp (M (p k))) (V (p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0)) 0 0
        (V (deriv p k)) (V (deriv (deriv p) k)) := by
    funext x
    simpa only [hM₁, hM₂, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using
      second_deriv_exponential_movingStep hF M V hp
        (hf.of_le (by omega : 3 ≤ n + 2)) (hg.of_le (by omega : 3 ≤ n + 2))
        (hh.of_le hn) x
  rw [heq]
  exact qBoundedJets_fixedMassSecondVariationStep hf hg hh ⟨Real.exp_pos _, hm⟩ _ _ _ hv hsmall

end SKBarriers2.StepCalculus

namespace SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

def fixedMassSecondVariationSource (A : ℝ) (v w b : E) : ℝ :=
  ‖v‖ ^ 2 * A ^ 2 + ‖v‖ * ‖w‖ * A + ‖v‖ * ‖b‖ + ‖w‖ ^ 2

theorem fixedMassSecondVariationBound_le_source (n : ℕ) {B : ℝ} (_hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ A H : ℝ, 0 ≤ A → 0 ≤ H → ∀ v w b : E,
      fixedMassSecondVariationBound n B A H v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * fixedMassSecondVariationSource A v w b := by
  let T := |tiltedStabilityCoefficient n B|
  let D := |tiltedCoarseCoefficient n B * (1 + (2 : ℝ) ^ n * B)|
  let N := |noiseAverageCoefficient n 2 B * B|
  let J := |directionSensitivityCoefficient n B|
  let Q := |potentialCovarianceCoefficient n B|
  have hT : 0 ≤ T := abs_nonneg _
  have hD : 0 ≤ D := abs_nonneg _
  have hN : 0 ≤ N := abs_nonneg _
  have hJ : 0 ≤ J := abs_nonneg _
  have hQ : 0 ≤ Q := abs_nonneg _
  let K := 1 + T + 2 * D + N + J + 2 * Q * (1 + B ^ 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  have ht : T ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hd : 2 * D ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hn : N + 2 * Q * B ^ 2 ≤ K := by
    apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hj : J ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hq : 2 * Q ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  refine ⟨K, hK, ?_⟩
  intro A H hA hH v w b
  have hvar : Q * (A * ‖v‖ + B * ‖w‖) ^ 2 ≤
      2 * Q * ‖v‖ ^ 2 * A ^ 2 + 2 * Q * B ^ 2 * ‖w‖ ^ 2 := by
    have HS : (A * ‖v‖ + B * ‖w‖) ^ 2 ≤
        2 * ((A * ‖v‖) ^ 2 + (B * ‖w‖) ^ 2) := by
      nlinarith [sq_nonneg (A * ‖v‖ - B * ‖w‖)]
    have H' := mul_le_mul_of_nonneg_left HS hQ
    nlinarith only [H']
  have habs : fixedMassSecondVariationBound n B A H v w b ≤
      H + T * H * ‖v‖ ^ 2 + 2 * D * A * ‖v‖ * ‖w‖ +
        N * ‖w‖ ^ 2 + J * ‖v‖ * ‖b‖ + Q * (A * ‖v‖ + B * ‖w‖) ^ 2 := by
    dsimp only [fixedMassSecondVariationBound, T, D, N, J, Q]
    gcongr <;> exact le_abs_self _
  have Ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht hH) (sq_nonneg ‖v‖)
  have Hd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hA) (norm_nonneg v)) (norm_nonneg w)
  have Hn := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖w‖)
  have Hj := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj (norm_nonneg v)) (norm_nonneg b)
  have Hq := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq (sq_nonneg ‖v‖)) (sq_nonneg A)
  dsimp only [fixedMassSecondVariationSource]
  nlinarith only [habs, hvar, Ht, Hd, Hn, Hj, Hq]

end SKBarriers2.StepCalculus
