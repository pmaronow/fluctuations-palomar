module

public import SKBarriers2.Analysis.ParamStep
public import SKBarriers2.Analysis.ParamChain
public import SKBarriers2.Analysis.ChainJets

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

theorem terminalLine_step_eq_cgf (g : E → ℝ) (v x : E) :
    (fun k : ℝ => vectorStep 1 v (fun y => k * g y) x) =
      cgf (fun t : ℝ => g (x + t • v)) (gaussianReal 0 1) := by
  funext k
  simp only [vectorStep, gaussianStep, one_ne_zero, ite_false,
    positiveGaussianLogStep, cgf, mgf, one_mul, div_one]

theorem terminalLine_second_deriv {r : ℕ} {B : ℝ} {g : E → ℝ}
    (hg : QPotential r B g) (hr : 2 ≤ r) (v x : E) :
    deriv (deriv (fun k : ℝ => vectorStep 1 v (fun y => k * g y) x)) 0 =
      variance (fun t : ℝ => g (x + t • v)) (gaussianReal 0 1) := by
  rw [terminalLine_step_eq_cgf]
  have ht := ((hg.boundedDerivs hr).compCLM (vectorTranslation v)).mem_interior_integrableExpSet_section x 0
  have H := variance_tilted_mul ht
  simpa only [zero_mul, tilted_const, iteratedDeriv_succ, iteratedDeriv_zero,
    iteratedDeriv_one, vectorTranslation, add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply] using H.symm

theorem qBoundedJets_terminalVariationVariance {n r : ℕ} {B A : ℝ}
    {f g : E → ℝ} (hf : QPotential r B f) (hr : 2 ≤ r) (hn : n + 1 ≤ r)
    (hg : QBoundedJets (n + 1) A g) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : E) (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBoundedJets n (covarianceJetCoefficient n B * A ^ 2 * ‖v‖ ^ 2)
      (spatialCovariance m v f g g) := by
  convert qBoundedJets_spatialCovariance n hf hr hn hg hg hm v hsmall using 1
  ring

def potentialCovarianceCoefficient (n : ℕ) (B : ℝ) : ℝ :=
  noiseAverageCoefficient n 2 B * (2 : ℝ) ^ n +
    (2 : ℝ) ^ n * noiseAverageCoefficient n 1 B ^ 2

private theorem potential_memLp_step {r s : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hg : QPotential s C g) (hs : 2 ≤ s)
    (m : ℝ) (v x : E) :
    MemLp (fun t : ℝ => g (x + t • v)) 2 (stepLaw m v f x) := by
  have hc := hg.smooth.continuous.comp (vectorTranslation v).continuous
  have hG := (hg.boundedDerivs hs).hasExpGrowth.compCLM (vectorTranslation v)
  have hI := (hG.mul hG).integrable_gaussianStepLaw
    ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) (hc.mul hc) m x
  rw [memLp_two_iff_integrable_sq]
  · change Integrable (fun t : ℝ => g (x + t • v) ^ 2)
      (gaussianStepLaw m (fun z : E × ℝ => f (z.1 + z.2 • v)) x)
    simpa only [pow_two, Function.comp_apply, vectorTranslation, add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.smulRight_apply] using hI
  · exact (hg.smooth.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable

theorem qBoundedJets_potentialCovariance {n : ℕ} {B C D : ℝ} {f g a : E → ℝ}
    (hf : QPotential (n + 2) B f) (hg : QPotential (n + 2) C g)
    (ha : QPotential (n + 2) D a) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets n (potentialCovarianceCoefficient n B * C * D * ‖v‖ ^ 2)
      (fun x => covariance (fun t : ℝ => g (x + t • v))
        (fun t : ℝ => a (x + t • v)) (stepLaw m v f x)) := by
  let G : E → ℝ → ℝ := fun x t => g (x + t • v) - g x
  let A : E → ℝ → ℝ := fun x t => a (x + t • v) - a x
  have hfc : QPotential (n + 1) B f := hf.of_le (by omega)
  have hGc : ContDiff ℝ n (fun z : ℝ × E => G z.2 z.1) :=
    ((hg.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))).sub
      (hg.smooth.comp contDiff_snd)).of_le (by exact_mod_cast (show n ≤ n + 2 by omega))
  have hAc : ContDiff ℝ n (fun z : ℝ × E => A z.2 z.1) :=
    ((ha.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))).sub
      (ha.smooth.comp contDiff_snd)).of_le (by exact_mod_cast (show n ≤ n + 2 by omega))
  have hGj (t : ℝ) : QBoundedJets n ((C * ‖v‖) * |t| ^ 1) (fun x => G x t) := by
    convert (hg.of_le (by omega : n + 1 ≤ n + 2)).increment (t • v) using 1
    rw [norm_smul, Real.norm_eq_abs]
    ring
  have hAj (t : ℝ) : QBoundedJets n ((D * ‖v‖) * |t| ^ 1) (fun x => A x t) := by
    convert (ha.of_le (by omega : n + 1 ≤ n + 2)).increment (t • v) using 1
    rw [norm_smul, Real.norm_eq_abs]
    ring
  have hPj (t : ℝ) : QBoundedJets n
      (((2 : ℝ) ^ n * C * D * ‖v‖ ^ 2) * |t| ^ 2)
      (fun x => G x t * A x t) := by
    convert (hGj t).mul (hAj t) using 1
    ring
  have hG := qBoundedJets_noiseMean_poly hfc (mul_nonneg hg.nonneg (norm_nonneg v))
    1 hGc hGj hm v hv
  have hA := qBoundedJets_noiseMean_poly hfc (mul_nonneg ha.nonneg (norm_nonneg v))
    1 hAc hAj hm v hv
  have hP := qBoundedJets_noiseMean_poly hfc
    (by positivity [hg.nonneg, ha.nonneg]) 2 (hGc.mul hAc) hPj hm v hv
  have hCov := hP.sub (hG.mul hA)
  have hfun : (fun x => covariance (fun t : ℝ => g (x + t • v))
      (fun t : ℝ => a (x + t • v)) (stepLaw m v f x)) =
      fun x => noiseMean m v f x (fun t => G x t * A x t) -
        noiseMean m v f x (G x) * noiseMean m v f x (A x) := by
    funext x
    let _ := stepLaw_probability hf (by omega) m v x
    have hgm : MemLp (fun t : ℝ => g (x + t • v)) 2 (stepLaw m v f x) := by
      exact potential_memLp_step hf (by omega) hg (by omega) m v x
    have ham : MemLp (fun t : ℝ => a (x + t • v)) 2 (stepLaw m v f x) := by
      exact potential_memLp_step hf (by omega) ha (by omega) m v x
    rw [← covariance_sub_const_left (hgm.integrable (by norm_num)) (g x),
      ← covariance_sub_const_right (ham.integrable (by norm_num)) (a x)]
    exact covariance_eq_sub (hgm.sub (memLp_const (g x))) (ham.sub (memLp_const (a x)))
  rw [hfun]
  convert hCov using 1
  dsimp only [potentialCovarianceCoefficient]
  ring

theorem tiltedPotentialAverage_hasFDerivAt {r s : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hg : QPotential s C g) (hs : 2 ≤ s)
    (m : ℝ) (v x : E) :
    HasFDerivAt (tiltedAverage m v f g)
      (∫ t : ℝ, fderiv ℝ g (x + t • v) + m •
        (fderiv ℝ f (x + t • v) - fderiv ℝ (vectorStep m v f) x).smulRight
          (g (x + t • v)) ∂stepLaw m v f x) x := by
  let T := vectorStep m v f
  let L : E × ℝ →L[ℝ] E := vectorTranslation v
  let H : E × ℝ → ℝ := fun z => f (L z) - T z.1
  let W : E × ℝ → ℝ := fun z => Real.exp (m * H z)
  let U : E × ℝ → E →L[ℝ] ℝ := fun z => fderiv ℝ g (L z) + m •
    (fderiv ℝ f (L z) - fderiv ℝ T z.1).smulRight (g (L z))
  have hb := hf.boundedDerivs hr
  have hgb := hg.boundedDerivs hs
  have hT : BoundedDerivs T := vectorStep_regular hb m v
  have hH : BoundedDerivs H := by
    simpa only [H, sub_eq_add_neg, neg_one_mul, ContinuousLinearMap.coe_fst'] using
      (hb.compCLM L).add ((hT.compCLM (ContinuousLinearMap.fst ℝ E ℝ)).const_mul (-1))
  have hW : Continuous W := Real.continuous_exp.comp (continuous_const.mul hH.1.continuous)
  have hWE : HasExpGrowth W := (hH.exp_growths m).1
  have hgc : Continuous (fun z : E × ℝ => g (L z)) := hg.smooth.continuous.comp L.continuous
  have hgdc : Continuous (fun z : E × ℝ => fderiv ℝ g (L z)) :=
    (hgb.1.continuous_fderiv (by norm_num)).comp L.continuous
  have hfc : Continuous (fun z : E × ℝ => fderiv ℝ f (L z) - fderiv ℝ T z.1) :=
    ((hb.1.continuous_fderiv (by norm_num)).comp L.continuous).sub
      ((hT.1.continuous_fderiv (by norm_num)).comp continuous_fst)
  have hUc : Continuous U := hgdc.add
    ((((ContinuousLinearMap.smulRightL ℝ E ℝ).continuous.comp hfc).clm_apply hgc).const_smul m)
  have hGE : HasExpGrowth (fun z : E × ℝ => g (L z)) := hgb.hasExpGrowth.compCLM L
  have hDE : HasExpGrowth (fun z : E × ℝ => fderiv ℝ g (L z)) :=
    HasExpGrowth.of_bounded hg.nonneg (fun z => hg.fderiv_le (by omega) (L z))
  have hSE : HasExpGrowth (fun z : E × ℝ => fderiv ℝ f (L z) - fderiv ℝ T z.1) := by
    apply HasExpGrowth.of_bounded (show 0 ≤ 2 * B by linarith [hf.nonneg])
    intro z
    exact (norm_sub_le _ _).trans (by
      linarith [hf.fderiv_le (by omega) (L z), norm_fderiv_step_le hf hr m v z.1])
  have hME : HasExpGrowth (fun _ : E × ℝ => m) :=
    HasExpGrowth.of_bounded (norm_nonneg m) (fun _ => le_rfl)
  have hUE : HasExpGrowth U := by
    convert hDE.add (hME.smul (hGE.smul hSE)) using 1
    funext z
    ext w
    simp only [U, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  have hdiff (y : E) (t : ℝ) : HasFDerivAt
      (fun z => W (z,t) * g (L (z,t))) (W (y,t) • U (y,t)) y := by
    have hline : HasFDerivAt (fun z : E => z + t • v) (ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).add_const (t • v)
    have hfx : HasFDerivAt (fun z : E => f (z + t • v)) (fderiv ℝ f (y + t • v)) y := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        (hb.1.differentiable (by norm_num) (y + t • v)).hasFDerivAt.comp y hline
    have hgx : HasFDerivAt (fun z : E => g (z + t • v)) (fderiv ℝ g (y + t • v)) y := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        (hgb.1.differentiable (by norm_num) (y + t • v)).hasFDerivAt.comp y hline
    convert! (((hfx.sub (hT.1.differentiable (by norm_num) y).hasFDerivAt).const_mul m).exp).mul hgx using 1
    ext w
    simp only [U, W, H, L, vectorTranslation, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, Pi.sub_apply]
    ring
  have hd := hasFDerivAt_gaussian_integral (fun z : E × ℝ => W z * g (L z))
    (fun z => W z • U z) (hW.mul hgc) (hW.smul hUc) (hWE.mul hGE) (hWE.smul hUE) hdiff x
  have heq : tiltedAverage m v f g =
      fun y => ∫ t : ℝ, W (y,t) * g (L (y,t)) ∂gaussianReal 0 1 := by
    funext y
    exact gaussianStepLaw_integral (hb.compCLM L) m y (fun t => g (y + t • v))
  rw [heq]
  convert hd using 1
  exact gaussianStepLaw_integral (hb.compCLM L) m x (fun t => U (x,t))

def massSensitivity (m : ℝ) (v : E) (f : E → ℝ) (x : E) : ℝ :=
  deriv (fun a : ℝ => vectorStep a v f x) m

theorem massSensitivity_eq {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) {m : ℝ} (hm : m ≠ 0) (v x : E) :
    massSensitivity m v f x = (tiltedAverage m v f f x - vectorStep m v f x) / m := by
  rw [massSensitivity, (hasDerivAt_mass hf hr hm v x).deriv]
  dsimp only [stepEntropy, noiseMean, tiltedAverage]
  field_simp

theorem fderiv_massSensitivity_apply {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) {m : ℝ} (hm : m ≠ 0) (v x w : E) :
    fderiv ℝ (massSensitivity m v f) x w =
      covariance (fun t : ℝ => f (x + t • v))
        (fun t : ℝ => fderiv ℝ f (x + t • v) w) (stepLaw m v f x) := by
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf hr m v x
  have hfm : MemLp (fun t : ℝ => f (x + t • v)) 2 μ :=
    potential_memLp_step hf hr hf hr m v x
  have hDw : QBddSmooth 1 (B * ‖w‖) (fun y => fderiv ℝ f y w) := (hf.of_le hr).directional w
  have hdm : MemLp (fun t : ℝ => fderiv ℝ f (x + t • v) w) 2 μ :=
    MemLp.of_bound (hDw.smooth.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable _
      (ae_of_all _ (fun t => hDw.abs_le _))
  have hiD := integrable_tilted_shift hf hr (hf.of_le hr).derivativeJets m v x
  have hiU : Integrable (fun t : ℝ => fderiv ℝ f (x + t • v) + m •
      (fderiv ℝ f (x + t • v) - fderiv ℝ (vectorStep m v f) x).smulRight
        (f (x + t • v))) μ := by
    have hGE : HasExpGrowth (fun z : E × ℝ => f ((vectorTranslation v) z)) :=
      (hf.boundedDerivs hr).hasExpGrowth.compCLM (vectorTranslation v)
    have hProd : HasExpGrowth (fun z : E × ℝ =>
        f ((vectorTranslation v) z) • (fderiv ℝ f ((vectorTranslation v) z) -
          fderiv ℝ (vectorStep m v f) x)) := by
      apply hGE.smul
      apply HasExpGrowth.of_bounded (show 0 ≤ 2 * B by linarith [hf.nonneg])
      intro z
      exact (norm_sub_le _ _).trans (by
        linarith [hf.fderiv_le (by omega) ((vectorTranslation v) z), norm_fderiv_step_le hf hr m v x])
    have hProdC : Continuous (fun z : E × ℝ =>
        f ((vectorTranslation v) z) • (fderiv ℝ f ((vectorTranslation v) z) -
          fderiv ℝ (vectorStep m v f) x)) :=
      (hf.smooth.continuous.comp (vectorTranslation v).continuous).smul
        (((hf.boundedDerivs hr).1.continuous_fderiv (by norm_num)).comp
          (vectorTranslation v).continuous |>.sub continuous_const)
    have hiP : Integrable (fun t : ℝ => f (x + t • v) •
        (fderiv ℝ f (x + t • v) - fderiv ℝ (vectorStep m v f) x)) μ := by
      let hb := (hf.boundedDerivs hr).compCLM (vectorTranslation v)
      rw [show μ = gaussianStepLaw m (f ∘ vectorTranslation v) x from rfl,
        gaussianStepLaw]
      apply (MeasureTheory.integrable_tilted_iff («E» := ((Fin 3 → ℝ) →L[ℝ] ℝ))
        (hb.exp_integrable m x) _).2
      exact (((hb.exp_growths m).1).smul hProd).integrable_gaussian_section
        ((Real.continuous_exp.comp (continuous_const.mul hb.1.continuous)).smul hProdC) x
    convert hiD.add (hiP.smul m) using 1
    funext t
    ext u
    simp only [Pi.add_apply, Pi.smul_apply, add_apply, smul_apply, sub_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  have heq : massSensitivity m v f = fun y =>
      (tiltedAverage m v f f y - vectorStep m v f y) / m :=
    funext (massSensitivity_eq hf hr hm v)
  have hd := ((tiltedPotentialAverage_hasFDerivAt hf hr hf hr m v x).sub
    ((vectorStep_regular (hf.boundedDerivs hr) m v).1.differentiable
      (by norm_num) x).hasFDerivAt).mul_const m⁻¹
  simp only [Pi.sub_apply] at hd
  rw [heq]
  simp_rw [div_eq_mul_inv]
  rw [hd.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    sub_apply]
  rw [ContinuousLinearMap.integral_apply hiU]
  simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  change m⁻¹ * ((∫ t : ℝ, fderiv ℝ f (x + t • v) w + m *
      ((fderiv ℝ f (x + t • v) w - fderiv ℝ (vectorStep m v f) x w) *
        f (x + t • v)) ∂μ) - fderiv ℝ (vectorStep m v f) x w) = _
  have hiD' : Integrable (fun t : ℝ => fderiv ℝ f (x + t • v) w) μ :=
    hdm.integrable (by norm_num)
  have hiP := hdm.integrable_mul hfm
  have hiQ := (hfm.integrable (by norm_num)).const_mul (fderiv ℝ (vectorStep m v f) x w)
  simp_rw [sub_mul]
  rw [integral_add (f := fun t : ℝ => fderiv ℝ f (x + t • v) w)
      (g := fun t : ℝ => m * (fderiv ℝ f (x + t • v) w * f (x + t • v) -
        fderiv ℝ (vectorStep m v f) x w * f (x + t • v)))
      hiD' ((hiP.sub hiQ).const_mul m), integral_const_mul,
    integral_sub (f := fun t : ℝ => fderiv ℝ f (x + t • v) w * f (x + t • v))
      (g := fun t : ℝ => fderiv ℝ (vectorStep m v f) x w * f (x + t • v)) hiP hiQ,
    integral_const_mul, fderiv_step_apply hf hr,
    covariance_eq_sub hfm hdm]
  dsimp only [noiseMean]
  have hcomm : (∫ t : ℝ, fderiv ℝ f (x + t • v) w * f (x + t • v) ∂μ) =
      ∫ t : ℝ, f (x + t • v) * fderiv ℝ f (x + t • v) w ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => mul_comm _ _)
  rw [hcomm]
  field_simp
  simp only [Pi.mul_apply]
  dsimp only [μ]
  ring

private theorem centered_potential_average {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) (v x : E) :
    noiseMean m v f x (fun t => f (x + t • v) - f x) =
      tiltedAverage m v f f x - f x := by
  let _ := stepLaw_probability hf hr m v x
  have hi := (potential_memLp_step hf hr hf hr m v x).integrable (by norm_num)
  rw [noiseMean, integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
  rfl

theorem massSensitivity_contDiff {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f) {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) : ContDiff ℝ (n + 1) (massSensitivity m v f) := by
  let G : E → ℝ → ℝ := fun x t => f (x + t • v) - f x
  have hGc : ContDiff ℝ (n + 1) (fun z : ℝ × E => G z.2 z.1) :=
    ((hf.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))).sub
      (hf.smooth.comp contDiff_snd)).of_le
        (by exact_mod_cast (show n + 1 ≤ n + 3 by omega))
  have hGj (t : ℝ) : QBoundedJets (n + 1) ((B * ‖v‖) * |t| ^ 1) (fun x => G x t) := by
    convert (hf.of_le (by omega : (n + 1) + 1 ≤ n + 3)).increment (t • v) using 1
    rw [norm_smul, Real.norm_eq_abs]
    ring
  have hM := qBoundedJets_noiseMean_poly
    (hf.of_le (by omega : (n + 1) + 1 ≤ n + 3)) (mul_nonneg hf.nonneg (norm_nonneg v))
    1 hGc hGj ⟨hm.1.le, hm.2⟩ v hv
  have hT : ContDiff ℝ (n + 1) (vectorStep m v f) :=
    (contDiff_step hf m v).of_le (by exact_mod_cast (show n + 1 ≤ n + 3 by omega))
  have heq : massSensitivity m v f = fun x =>
      (noiseMean m v f x (G x) - (vectorStep m v f x - f x)) / m := by
    funext x
    rw [massSensitivity_eq hf (by omega) hm.1.ne', centered_potential_average hf (by omega)]
    ring
  rw [heq]
  exact (hM.smooth.sub (hT.sub (hf.smooth.of_le
    (by exact_mod_cast (show n + 1 ≤ n + 3 by omega))))).div_const m

def massSensitivityJetCoefficient (n : ℕ) (B : ℝ) : ℝ :=
  max (2 * B ^ 2) (potentialCovarianceCoefficient n B * B ^ 2)

theorem qBoundedJets_massSensitivity {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f) {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) (hsmall : B * ‖v‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets (n + 1) (massSensitivityJetCoefficient n B * ‖v‖ ^ 2)
      (massSensitivity m v f) := by
  have hK : 0 ≤ massSensitivityJetCoefficient n B :=
    (show 0 ≤ 2 * B ^ 2 by positivity).trans (le_max_left _ _)
  apply QBoundedJets.of_directional (mul_nonneg hK (sq_nonneg _))
    (massSensitivity_contDiff hf hm v hv)
  · intro x
    exact (abs_deriv_mass_step_le hf (by omega) ⟨hm.1.le, hm.2⟩ v x hsmall).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · intro w hw
    have hfw : QPotential (n + 2) B (fun x => fderiv ℝ f x w) := by
      simpa only [hw, mul_one] using (hf.directional w).potential
    have hcov := qBoundedJets_potentialCovariance
      (hf.of_le (by omega : n + 2 ≤ n + 3))
      (hf.of_le (by omega : n + 2 ≤ n + 3)) hfw ⟨hm.1.le, hm.2⟩ v hv
    have heq : (fun x => fderiv ℝ (massSensitivity m v f) x w) = fun x =>
        covariance (fun t : ℝ => f (x + t • v))
          (fun t : ℝ => fderiv ℝ f (x + t • v) w) (stepLaw m v f x) :=
      funext (fun x => fderiv_massSensitivity_apply hf (by omega) hm.1.ne' v x w)
    rw [heq]
    apply hcov.mono
    calc
      potentialCovarianceCoefficient n B * B * B * ‖v‖ ^ 2 =
          (potentialCovarianceCoefficient n B * B ^ 2) * ‖v‖ ^ 2 := by ring
      _ ≤ massSensitivityJetCoefficient n B * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

def firstVariationStep (m : ℝ) (v : E) (f g : E → ℝ) (dm : ℝ) (w : E) (x : E) : ℝ :=
  tiltedAverage m v f g x + dm * massSensitivity m v f x +
    tiltedAverage m v f (directionSource m v w f) x

theorem qBoundedJets_firstVariationStep {n : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential (n + 3) B f) (hg : QBoundedJets (n + 1) A g)
    {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1) (v w : E) (dm : ℝ)
    (hv : ‖v‖ ≤ 1) (hsmall : B * ‖v‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets (n + 1)
      (A + tiltedStabilityCoefficient (n + 1) B * A * ‖v‖ ^ 2 +
        massSensitivityJetCoefficient n B * ‖v‖ ^ 2 * |dm| +
        directionSensitivityCoefficient (n + 1) B * ‖v‖ * ‖w‖)
      (firstVariationStep m v f g dm w) := by
  have hcurv : m * (B * ‖v‖ ^ 2) ≤ 1 / 2 :=
    (mul_le_of_le_one_left (mul_nonneg hf.nonneg (sq_nonneg _)) hm.2).trans hsmall
  have hT := qBoundedJets_tiltedAverage (n + 1) hf (by omega) (by omega) hg
    ⟨hm.1.le, hm.2⟩ v hcurv
  have hM := (qBoundedJets_massSensitivity hf hm v hv hsmall).const_smul dm
  have hD := qBoundedJets_directionSensitivity hf ⟨hm.1.le, hm.2⟩ v w
  convert (hT.add hM).add hD using 1
  · ring
  · rfl

theorem qBoundedJets_deriv_paramStep {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f) {m : ℝ → ℝ} {v : ℝ → E} {dm k : ℝ} {w : E}
    (hmder : HasDerivAt m dm k) (hvder : HasDerivAt v w k)
    (hm : m k ∈ Ioc (0 : ℝ) 1) (hv : ‖v k‖ ≤ 1)
    (hsmall : B * ‖v k‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets (n + 1)
      (massSensitivityJetCoefficient n B * ‖v k‖ ^ 2 * |dm| +
        directionSensitivityCoefficient (n + 1) B * ‖v k‖ * ‖w‖)
      (fun x => deriv (fun t => vectorStep (m t) (v t) f x) k) := by
  have hM := (qBoundedJets_massSensitivity hf hm (v k) hv hsmall).const_smul dm
  have hD := qBoundedJets_directionSensitivity hf ⟨hm.1.le, hm.2⟩ (v k) w
  have heq : (fun x => deriv (fun t => vectorStep (m t) (v t) f x) k) =
      fun x => dm * massSensitivity (m k) (v k) f x +
        tiltedAverage (m k) (v k) f (directionSource (m k) (v k) w f) x := by
    funext x
    exact (hasDerivAt_paramStep hf (by omega) hmder hvder hm.1.ne' x).deriv
  rw [heq]
  convert hM.add hD using 1
  ring

theorem second_mass_deriv_eq {r : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) {m : ℝ} (hm : m ≠ 0) (v x : E) :
    deriv (deriv (fun a : ℝ => vectorStep a v f x)) m =
      (variance (fun t : ℝ => f (x + t • v)) (stepLaw m v f x) -
        2 * massSensitivity m v f x) / m := by
  let Z : ℝ → ℝ := cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1)
  let hb := (hf.boundedDerivs hr).compCLM (vectorTranslation v)
  have hAn (a : ℝ) : AnalyticAt ℝ Z a :=
    analyticAt_cgf (hb.mem_interior_integrableExpSet_section x a)
  have hc : ContDiff ℝ 2 Z := contDiff_iff_contDiffAt.mpr (fun a => (hAn a).contDiffAt)
  have hZ (a : ℝ) : HasDerivAt Z (deriv Z a) a := (hAn a).differentiableAt.hasDerivAt
  have hD : HasDerivAt (deriv Z) (deriv (deriv Z) m) m :=
    (hc.differentiable_deriv_two m).hasDerivAt
  have hT (a : ℝ) (ha : a ≠ 0) : vectorStep a v f x = Z a / a := by
    simp only [vectorStep, gaussianStep, ha, ite_false, positiveGaussianLogStep, Z, cgf, mgf]
  have heq : deriv (fun a : ℝ => vectorStep a v f x) =ᶠ[𝓝 m]
      fun a => (deriv Z a * a - Z a) / a ^ 2 := by
    filter_upwards [eventually_ne_nhds hm] with a ha
    have hloc : (fun b : ℝ => vectorStep b v f x) =ᶠ[𝓝 a] fun b => Z b / b := by
      filter_upwards [eventually_ne_nhds ha] with b hb
      exact hT b hb
    rw [hloc.deriv_eq]
    simpa only [id_eq, mul_one] using ((hZ a).fun_div (hasDerivAt_id a) ha).deriv
  have hDD := (((hD.fun_mul (hasDerivAt_id m)).fun_sub (hZ m)).fun_div
    ((hasDerivAt_id m).pow 2) (pow_ne_zero 2 hm)).deriv
  simp only [Pi.pow_apply, id_eq] at hDD
  rw [heq.deriv_eq, hDD]
  have hvar := variance_tilted_mul (hb.mem_interior_integrableExpSet_section x m)
  change variance (fun t : ℝ => f (x + t • v)) (stepLaw m v f x) = iteratedDeriv 2 Z m at hvar
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hvar
  have hmean : deriv Z m = tiltedAverage m v f f x := by
    exact (integral_tilted_mul_self (hb.mem_interior_integrableExpSet_section x m)).symm
  have hz : Z m = m * vectorStep m v f x := by rw [hT m hm]; field_simp
  rw [← hvar, hmean, hz, massSensitivity_eq hf hr hm]
  simp only [mul_one]
  field_simp
  ring

theorem qBoundedJets_second_mass_deriv {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f) {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1)
    (v : E) (hv : ‖v‖ ≤ 1) (hsmall : B * ‖v‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets n
      ((massVarianceCoefficient n B + 2 * massSensitivityJetCoefficient n B) * ‖v‖ ^ 2 / m)
      (fun x => deriv (deriv (fun a : ℝ => vectorStep a v f x)) m) := by
  have hV := qBoundedJets_massVariance (n := n) hf (by omega) (by omega) ⟨hm.1.le, hm.2⟩ v hv
  have hS := ((qBoundedJets_massSensitivity hf hm v hv hsmall).of_le
    (by omega : n ≤ n + 1)).const_smul 2
  have hQ := ((hV.sub hS).const_smul m⁻¹)
  have heq : (fun x => deriv (deriv (fun a : ℝ => vectorStep a v f x)) m) =
      fun x => m⁻¹ * (variance (fun t : ℝ => f (x + t • v)) (stepLaw m v f x) -
        2 * massSensitivity m v f x) := by
    funext x
    rw [second_mass_deriv_eq hf (by omega) hm.1.ne', div_eq_mul_inv, mul_comm]
  rw [heq]
  convert hQ using 1
  rw [abs_inv, abs_of_pos hm.1]
  norm_num
  ring

theorem terminalTilt_step_eq_cgf {r s : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hg : QBddSmooth s C g) (hs : 2 ≤ s)
    {m : ℝ} (hm : m ≠ 0) (v x : E) :
    (fun k : ℝ => vectorStep m v (fun y => f y + k * g y) x) =
      fun k => vectorStep m v f x +
        cgf (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) (m * k) / m := by
  funext k
  have hb := (hf.boundedDerivs hr).compCLM (vectorTranslation v)
  have hp := ((hf.boundedDerivs hr).add ((hg.potential.boundedDerivs hs).const_mul k)).compCLM
    (vectorTranslation v)
  have he : cgf (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) (m * k) =
      m * (vectorStep m v (fun y => f y + k * g y) x - vectorStep m v f x) := by
    change Real.log (∫ t : ℝ, Real.exp ((m * k) * g (x + t • v))
      ∂(gaussianReal 0 1).tilted (fun t => m * f (x + t • v))) = _
    rw [integral_tilted_real_eq_div]
    have he' (t : ℝ) : Real.exp ((m * k) * g (x + t • v)) *
        Real.exp (m * f (x + t • v)) =
        Real.exp (m * (f (x + t • v) + k * g (x + t • v))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [he']
    rw [show (∫ t : ℝ, Real.exp (m * f (x + t • v)) ∂gaussianReal 0 1) =
        Real.exp (m * vectorStep m v f x) from (exp_gaussianStep hb m x).symm,
      show (∫ t : ℝ, Real.exp (m * (f (x + t • v) + k * g (x + t • v)))
        ∂gaussianReal 0 1) = Real.exp (m * vectorStep m v (fun y => f y + k * g y) x) from
          (exp_gaussianStep hp m x).symm,
      ← Real.exp_sub, Real.log_exp]
    ring
  rw [he]
  field_simp
  ring

private theorem terminalTest_integrableExpSet {r s : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hg : QBddSmooth s C g) (m : ℝ) (v x : E) :
    integrableExpSet (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) = univ := by
  let _ := stepLaw_probability hf hr m v x
  ext a
  simp only [mem_univ, iff_true]
  apply Integrable.of_bound
    (Real.continuous_exp.comp (continuous_const.mul
      (hg.smooth.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))))).aestronglyMeasurable (Real.exp (|a| * C))
  apply ae_of_all
  intro t
  change ‖Real.exp (a * g (x + t • v))‖ ≤ Real.exp (|a| * C)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((abs_mul _ _).trans_le
    (mul_le_mul_of_nonneg_left (hg.abs_le _) (abs_nonneg a)))

theorem terminalTilt_second_deriv {r s : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hg : QBddSmooth s C g) (hs : 2 ≤ s)
    {m : ℝ} (hm : m ≠ 0) (v x : E) :
    deriv (deriv (fun k : ℝ => vectorStep m v (fun y => f y + k * g y) x)) 0 =
      m * covariance (fun t : ℝ => g (x + t • v))
        (fun t : ℝ => g (x + t • v)) (stepLaw m v f x) := by
  let _ := stepLaw_probability hf hr m v x
  have ht (a : ℝ) : a ∈ interior (integrableExpSet
      (fun t : ℝ => g (x + t • v)) (stepLaw m v f x)) := by
    rw [terminalTest_integrableExpSet hf hr hg, interior_univ]
    exact mem_univ a
  have hc : ContDiff ℝ 2 (cgf (fun t : ℝ => g (x + t • v)) (stepLaw m v f x)) :=
    contDiff_iff_contDiffAt.mpr (fun a => (analyticAt_cgf (ht a)).contDiffAt)
  have hiter (G : ℝ → ℝ) : iteratedDeriv 2 G 0 = deriv (deriv G) 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [← hiter]
  rw [terminalTilt_step_eq_cgf hf hr hg hs hm, iteratedDeriv_const_add (by norm_num),
    iteratedDeriv_div_const, iteratedDeriv_comp_const_mul hc]
  simp only [mul_zero]
  rw [← variance_tilted_mul (ht 0)]
  simp only [zero_mul, tilted_const]
  rw [← covariance_self (memLp_of_mem_interior_integrableExpSet (ht 0) 2).aemeasurable]
  field_simp

theorem qBoundedJets_first_terminalVariation {n r s : ℕ} {B A C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hn : n + 1 ≤ r)
    (hg : QBoundedJets n A g) (hgreg : QBddSmooth s C g) (hs : 2 ≤ s)
    {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBoundedJets n (A + tiltedStabilityCoefficient n B * A * ‖v‖ ^ 2)
      (fun x => deriv (fun k : ℝ => vectorStep m v (fun y => f y + k * g y) x) 0) := by
  have heq : (fun x => deriv (fun k : ℝ => vectorStep m v (fun y => f y + k * g y) x) 0) =
      tiltedAverage m v f g := by
    funext x
    exact (hasDerivAt_terminal_tilt hf hr hgreg hs hm.1.ne' v x).deriv
  rw [heq]
  exact qBoundedJets_tiltedAverage n hf hr hn hg ⟨hm.1.le, hm.2⟩ v hsmall

theorem qBoundedJets_second_terminalVariation {n r : ℕ} {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2 ≤ r) (hn : n + 1 ≤ r)
    (hg : QBoundedJets (n + 2) A g) {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1) (v : E)
    (hsmall : m * (B * ‖v‖ ^ 2) ≤ 1 / 2) :
    QBoundedJets n (covarianceJetCoefficient n B * A ^ 2 * ‖v‖ ^ 2)
      (fun x => deriv (deriv (fun k : ℝ => vectorStep m v (fun y => f y + k * g y) x)) 0) := by
  have hcov := qBoundedJets_terminalVariationVariance hf hr hn (hg.of_le (by omega))
    ⟨hm.1.le, hm.2⟩ v hsmall
  have hscaled := (hcov.const_smul m).mono
    (mul_le_of_le_one_left hcov.nonneg (by rw [abs_of_pos hm.1]; exact hm.2))
  have heq : (fun x => deriv (deriv (fun k : ℝ =>
      vectorStep m v (fun y => f y + k * g y) x)) 0) =
      fun x => m * spatialCovariance m v f g g x := by
    funext x
    rw [terminalTilt_second_deriv hf hr (qBoundedJets_iff_qBddSmooth.mp hg) (by omega) hm.1.ne',
      spatialCovariance_eq hf hr
        (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : 1 ≤ n + 2)))
        (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : 1 ≤ n + 2)))]
  rw [heq]
  exact hscaled

private theorem gaussian_cos_sin (b : ℝ) :
    (∫ t : ℝ, Real.cos (b * t) ∂gaussianReal 0 1) = Real.exp (-(b ^ 2) / 2) ∧
    (∫ t : ℝ, Real.sin (b * t) ∂gaussianReal 0 1) = 0 := by
  have hi : Integrable (fun t : ℝ => Complex.exp ((b * t : ℝ) * Complex.I))
      (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by simp [Complex.norm_exp])
  simp only [Complex.ofReal_mul] at hi
  have H := charFun_gaussianReal (μ := 0) (v := 1) b
  rw [charFun_apply_real] at H
  have hR := (Complex.reCLM.integral_comp_comm hi).trans (congrArg Complex.re H)
  have hI := (Complex.imCLM.integral_comp_comm hi).trans (congrArg Complex.im H)
  constructor
  · simpa [Complex.exp_re, pow_two, neg_div] using hR
  · simpa [Complex.exp_im, pow_two] using hI

private theorem integrable_cos_affine (a b : ℝ) :
    Integrable (fun t : ℝ => Real.cos (a + b * t)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

private theorem integrable_sin_affine (a b : ℝ) :
    Integrable (fun t : ℝ => Real.sin (a + b * t)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _)

private theorem gaussian_trig_affine (a b : ℝ) :
    (∫ t : ℝ, Real.cos (a + b * t) ∂gaussianReal 0 1) =
      Real.cos a * Real.exp (-(b ^ 2) / 2) ∧
    (∫ t : ℝ, Real.sin (a + b * t) ∂gaussianReal 0 1) =
      Real.sin a * Real.exp (-(b ^ 2) / 2) := by
  have hc : Integrable (fun t : ℝ => Real.cos (b * t)) (gaussianReal 0 1) := by
    simpa only [zero_add] using integrable_cos_affine 0 b
  have hs : Integrable (fun t : ℝ => Real.sin (b * t)) (gaussianReal 0 1) := by
    simpa only [zero_add] using integrable_sin_affine 0 b
  constructor
  · simp_rw [Real.cos_add]
    rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul,
      integral_const_mul, (gaussian_cos_sin b).1, (gaussian_cos_sin b).2]
    ring
  · simp_rw [Real.sin_add]
    rw [integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul,
      integral_const_mul, (gaussian_cos_sin b).1, (gaussian_cos_sin b).2]
    ring

theorem gaussian_sine_variance (a : ℝ) :
    variance (fun t : ℝ => Real.sin (a + t)) (gaussianReal 0 1) =
      (1 - Real.exp (-1)) / 2 +
        (Real.exp (-1) - Real.exp (-2)) / 2 * Real.cos (2 * a) := by
  have hmem : MemLp (fun t : ℝ => Real.sin (a + t)) 2 (gaussianReal 0 1) := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _)
  rw [variance_eq_sub hmem]
  change (∫ t : ℝ, Real.sin (a + t) ^ 2 ∂gaussianReal 0 1) -
    (∫ t : ℝ, Real.sin (a + t) ∂gaussianReal 0 1) ^ 2 = _
  have hsquare : (∫ t : ℝ, Real.sin (a + t) ^ 2 ∂gaussianReal 0 1) =
      1 / 2 - Real.cos (2 * a) * Real.exp (-2) / 2 := by
    simp_rw [Real.sin_sq_eq_half_sub]
    have heq (t : ℝ) : 2 * (a + t) = 2 * a + 2 * t := by ring
    simp_rw [heq]
    rw [integral_sub (integrable_const _) ((integrable_cos_affine _ _).div_const _)]
    simp only [integral_div, integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [(gaussian_trig_affine (2 * a) 2).1]
    norm_num
  have hmean : (∫ t : ℝ, Real.sin (a + t) ∂gaussianReal 0 1) =
      Real.sin a * Real.exp (-(1 / 2)) := by
    convert (gaussian_trig_affine a 1).2 using 1 <;> norm_num
  rw [hsquare, hmean, mul_pow, ← Real.exp_nat_mul, Real.sin_sq_eq_half_sub]
  norm_num
  ring

theorem gaussian_sine_variance_deriv (A δ x : ℝ) :
    deriv (fun y : ℝ => variance
      (fun t : ℝ => A * Real.sin (y / δ + t)) (gaussianReal 0 1)) x =
      -(A ^ 2 / δ) * (Real.exp (-1) - Real.exp (-2)) * Real.sin (2 * (x / δ)) := by
  have heq : (fun y : ℝ => variance
      (fun t : ℝ => A * Real.sin (y / δ + t)) (gaussianReal 0 1)) =
      fun y : ℝ => A ^ 2 * ((1 - Real.exp (-1)) / 2 +
        (Real.exp (-1) - Real.exp (-2)) / 2 * Real.cos (2 * (y / δ))) := by
    funext y
    rw [variance_const_mul, gaussian_sine_variance]
  rw [heq]
  have hd := (((((hasDerivAt_id x).div_const δ).const_mul 2).cos).const_mul
    ((Real.exp (-1) - Real.exp (-2)) / 2)).const_add ((1 - Real.exp (-1)) / 2)
  have H := (hd.const_mul (A ^ 2)).deriv
  simp only [id_eq] at H
  rw [H]
  ring

theorem scaled_sine_scalar_jets (R : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {j : ℕ} (hj : j ≤ R) (x : ℝ) :
    |iteratedDeriv j (fun y : ℝ => δ ^ R * Real.sin (y / δ)) x| ≤ 1 := by
  have heq : (fun y : ℝ => Real.sin (y / δ)) = fun y => Real.sin (δ⁻¹ * y) := by
    funext y
    congr 1
    ring
  rw [iteratedDeriv_const_mul_field, heq,
    iteratedDeriv_comp_const_mul (show ContDiff ℝ j Real.sin from Real.contDiff_sin) δ⁻¹]
  rw [abs_mul, abs_mul, abs_pow, abs_of_pos hδ, abs_pow, abs_inv, abs_of_pos hδ]
  calc
    δ ^ R * (δ⁻¹ ^ j * |iteratedDeriv j Real.sin (δ⁻¹ * x)|) ≤ δ ^ R * δ⁻¹ ^ j := by
      have H := mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one j (δ⁻¹ * x))
        (show 0 ≤ δ⁻¹ ^ j by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left H (pow_nonneg hδ.le R)
    _ = δ ^ (R - j) := by rw [pow_sub₀ δ hδ.ne' hj, inv_pow]
    _ ≤ 1 := pow_le_one₀ hδ.le hδ1

theorem exists_terminal_variance_same_order_violation (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ A : ℝ, A ≠ 0 →
      C * δ ^ 2 * (|A| / δ) ^ 2 <
        |deriv (fun x : ℝ => variance
          (fun t : ℝ => A * Real.sin (x / δ + t)) (gaussianReal 0 1))
          (δ * (Real.pi / 4))| := by
  let c : ℝ := Real.exp (-1) - Real.exp (-2)
  have hc : 0 < c := sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))
  let δ : ℝ := min (1 / 2) (c / (2 * (C + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hc (by positivity))
  have hδsmall : δ ≤ 1 / 2 := min_le_left _ _
  have hδbound : δ * (2 * (C + 1)) ≤ c :=
    (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp (min_le_right _ _)
  have hgap : C * δ < c := by nlinarith
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro A hA
  have hphase : 2 * (δ * (Real.pi / 4) / δ) = Real.pi / 2 := by
    field_simp
    ring
  rw [gaussian_sine_variance_deriv A δ, hphase, Real.sin_pi_div_two, mul_one]
  change C * δ ^ 2 * (|A| / δ) ^ 2 < |-(A ^ 2 / δ) * c|
  have hscale : C * δ ^ 2 * (|A| / δ) ^ 2 = C * A ^ 2 := by
    rw [div_pow, sq_abs]
    field_simp
  rw [hscale, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (sq_nonneg _) hδ.le),
    abs_of_pos hc]
  have hApos : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have H := mul_lt_mul_of_pos_left hgap hApos
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ hδ).mpr
  convert H using 1
  ring

section MovingTerminal

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

private theorem parameter_curve_hasDerivAt {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : P × Y → ℝ} (hF : Differentiable ℝ F)
    {p : ℝ → P} {u : P} {k : ℝ} (hp : HasDerivAt p u k) (x : Y) :
    HasDerivAt (fun t => F (p t,x)) (fderiv ℝ F (p k,x) (u,0)) k := by
  exact (hF (p k,x)).hasFDerivAt.comp_hasDerivAt k (hp.prodMk (hasDerivAt_const k x))

theorem hasDerivAt_exponential_movingStep {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {u : P} {k : ℝ}
    (hp : HasDerivAt p u k) {B A : ℝ}
    (hf : QPotential 2 B (fun y => F (p k,y)))
    (hg : QBddSmooth 0 A (fun y => fderiv ℝ F (p k,y) (u,0))) (x : E) :
    HasDerivAt (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) x)
      (firstVariationStep (Real.exp (M (p k))) (V (p k)) (fun y => F (p k,y))
        (fun y => fderiv ℝ F (p k,y) (u,0))
        (Real.exp (M (p k)) * M u) (V u) x) k := by
  let q := p k
  let m := Real.exp (M q)
  let v := V q
  let w := V u
  let f : E → ℝ := fun y => F (q,y)
  let g : E → ℝ := fun y => fderiv ℝ F (q,y) (u,0)
  let H : P × (E × ℝ) → ℝ := fun z =>
    Real.exp (M z.1) * F (z.1, z.2.1 + z.2.2 • V z.1)
  let Z : P × E → ℝ := gaussianStep 1
    (fun z : (P × E) × ℝ => H (z.1.1,(z.1.2,z.2)))
  have hH : ParamRegular H :=
    ParamChain.regular_mul_exp_parameter (ParamChain.regular_movingInput hF V) M
  have hZ : ParamRegular Z := hH.gaussianStep 1
  have hdZ := parameter_curve_hasDerivAt (hZ.1.differentiable (by norm_num)) hp x
  have hZder := hH.parameterDerivative_gaussianStep 1 (q,x) u
  have hlaw : gaussianStepLaw 1
      (fun z : (P × E) × ℝ => H (z.1.1,(z.1.2,z.2))) (q,x) = stepLaw m v f x := by
    simp only [gaussianStepLaw, stepLaw, H, one_mul]
    rfl
  change fderiv ℝ Z (q,x) (u,0) =
    ∫ t, fderiv ℝ H (q,(x,t)) (u,0) ∂gaussianStepLaw 1
      (fun z : (P × E) × ℝ => H (z.1.1,(z.1.2,z.2))) (q,x) at hZder
  rw [hlaw] at hZder
  have hspatial (y : E) : fderiv ℝ f y w = fderiv ℝ F (q,y) (0,w) := by
    have hpair : HasFDerivAt (fun z : E => (q,z))
        ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) y :=
      (hasFDerivAt_const q y).prodMk (hasFDerivAt_id y)
    exact congrArg (fun D : E →L[ℝ] ℝ => D w)
      (((hF.1.differentiable (by norm_num) (q,y)).hasFDerivAt.comp y hpair).fderiv)
  have hpoint (t : ℝ) : fderiv ℝ H (q,(x,t)) (u,0) =
      m * (M u * f (x + t • v) + g (x + t • v) +
        t * fderiv ℝ f (x + t • v) w) := by
    have hline : HasDerivAt (fun a : ℝ => q + a • u) u 0 := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add q
    have hLeft := parameter_curve_hasDerivAt (hH.1.differentiable (by norm_num)) hline (x,t)
    have hmass := (M.hasFDerivAt.comp_hasDerivAt 0 hline).exp
    have hfield : HasDerivAt (fun a : ℝ => (q + a • u, x + t • V (q + a • u)))
        (u, t • w) 0 := by
      simpa only [Function.comp_def, Pi.smul_apply] using hline.prodMk
        (((V.hasFDerivAt.comp_hasDerivAt 0 hline).const_smul t).const_add x)
    have hInner : HasDerivAt (fun a : ℝ => F (q + a • u, x + t • V (q + a • u)))
        (fderiv ℝ F (q,x + t • v) (u,t • w)) 0 := by
      have hi := (hF.1.differentiable (by norm_num)
        (q + (0 : ℝ) • u, x + t • V (q + (0 : ℝ) • u))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hfield
      simpa only [Function.comp_def, zero_smul, add_zero] using hi
    have hBoth := hmass.fun_mul hInner
    have heq := hLeft.unique hBoth
    simp only [Function.comp_def, zero_smul, add_zero] at heq
    rw [heq, hspatial]
    have hsplit : (u,t • w) = (u,(0 : E)) + t • ((0 : P),w) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul]
    dsimp only [m, f, g, v, w]
    ring
  let _ := stepLaw_probability hf le_rfl m v x
  have hiF : Integrable (fun t : ℝ => f (x + t • v)) (stepLaw m v f x) :=
    (potential_memLp_step hf le_rfl hf le_rfl m v x).integrable (by norm_num)
  have hiG := integrable_tilted_shift hf le_rfl (qBoundedJets_iff_qBddSmooth.mpr hg) m v x
  have hDc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • v) w) :=
    ((hf.smooth.continuous_fderiv (by norm_num)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hDg : HasExpGrowth (fun t : ℝ => fderiv ℝ f (x + t • v) w) :=
    HasExpGrowth.of_bounded (mul_nonneg hf.nonneg (norm_nonneg w))
      (fun t => hf.directional_le (by norm_num) _ _)
  have hiN := integrable_noise hf le_rfl m v x
    ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).mul hDg) (continuous_id.mul hDc)
  have hZexact : fderiv ℝ Z (q,x) (u,0) = m *
      (M u * tiltedAverage m v f f x + tiltedAverage m v f g x +
        tiltedAverage m v f (directionSource m v w f) x) := by
    rw [hZder]
    simp_rw [hpoint]
    rw [integral_const_mul,
      integral_add (f := fun t : ℝ => M u * f (x + t • v) + g (x + t • v))
        (g := fun t : ℝ => t * fderiv ℝ f (x + t • v) w)
        ((hiF.const_mul _).add hiG) hiN,
      integral_add (f := fun t : ℝ => M u * f (x + t • v))
        (g := fun t : ℝ => g (x + t • v)) (hiF.const_mul _) hiG,
      integral_const_mul]
    rw [show (∫ t, t * fderiv ℝ f (x + t • v) w ∂stepLaw m v f x) =
      tiltedAverage m v f (directionSource m v w f) x from noise_directionSource hf le_rfl m v w x]
    rfl
  have hZvalue : Z (q,x) = m * vectorStep m v f x := by
    dsimp only [Z, H, m, v, f]
    simp only [vectorStep, gaussianStep, Real.exp_ne_zero, ite_false, one_ne_zero,
      positiveGaussianLogStep, one_mul, div_one]
    field_simp
  have hExp := ((M.hasFDerivAt.comp_hasDerivAt k hp).neg).exp
  simp only [Function.comp_def, Pi.neg_apply] at hExp
  have hd := hExp.fun_mul hdZ
  convert hd using 1
  · funext t
    simp only [vectorStep, gaussianStep, Real.exp_ne_zero, ite_false, one_ne_zero,
      positiveGaussianLogStep, Z, H, one_mul, Real.exp_neg, div_eq_mul_inv]
    ring
  · change firstVariationStep m v f g (m * M u) w x = _
    rw [hZexact, hZvalue]
    dsimp only [firstVariationStep]
    rw [massSensitivity_eq hf le_rfl (Real.exp_ne_zero _) v x, Real.exp_neg]
    dsimp only [q, m, f]
    field_simp
    ring

theorem qBoundedJets_deriv_exponential_movingStep {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {u : P} {k : ℝ}
    (hp : HasDerivAt p u k) {n : ℕ} {B A : ℝ}
    (hf : QPotential (n + 3) B (fun y => F (p k,y)))
    (hg : QBoundedJets (n + 1) A (fun y => fderiv ℝ F (p k,y) (u,0)))
    (hm : Real.exp (M (p k)) ≤ 1) (hv : ‖V (p k)‖ ≤ 1)
    (hsmall : B * ‖V (p k)‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets (n + 1)
      (A + tiltedStabilityCoefficient (n + 1) B * A * ‖V (p k)‖ ^ 2 +
        massSensitivityJetCoefficient n B * ‖V (p k)‖ ^ 2 * |Real.exp (M (p k)) * M u| +
        directionSensitivityCoefficient (n + 1) B * ‖V (p k)‖ * ‖V u‖)
      (fun x => deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
        (fun y => F (p t,y)) x) k) := by
  have hidentity : (fun x => deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) x) k) = fun x =>
      firstVariationStep (Real.exp (M (p k))) (V (p k)) (fun y => F (p k,y))
        (fun y => fderiv ℝ F (p k,y) (u,0)) (Real.exp (M (p k)) * M u) (V u) x := by
    funext x
    exact (hasDerivAt_exponential_movingStep hF M V hp (hf.of_le (by omega))
      (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by omega : 0 ≤ n + 1))) x).deriv
  rw [hidentity]
  exact qBoundedJets_firstVariationStep hf hg ⟨Real.exp_pos _, hm⟩ _ _ _ hv hsmall

def firstVariationMajorant (K : ℝ) (q u : P) :
    List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)) → ℝ
  | [] => 0
  | a :: ps => (1 + K * ‖a.2 q‖ ^ 2) * firstVariationMajorant K q u ps +
      K * (‖a.2 q‖ * ‖a.2 u‖ + ‖a.2 q‖ ^ 2 * |Real.exp (a.1 q) * a.1 u|)

theorem firstVariationMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (q u : P)
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) : 0 ≤ firstVariationMajorant K q u ps := by
  induction ps with
  | nil => exact le_rfl
  | cons a ps ih => dsimp only [firstVariationMajorant]; positivity

theorem qBoundedJets_first_exponentialChain
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {p : ℝ → P} {u : P} {k : ℝ}
    (hp : HasDerivAt p u k) {n : ℕ} {B K : ℝ} {f : E → ℝ}
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (n + 1) B ≤ K)
    (hMass : massSensitivityJetCoefficient n B ≤ K)
    (hDir : directionSensitivityCoefficient (n + 1) B ≤ K)
    (hpotential : ∀ front tail, ps = front ++ tail →
      QPotential (n + 3) B (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f))
    (hgeometry : ∀ a ∈ ps, Real.exp (a.1 (p k)) ≤ 1 ∧ ‖a.2 (p k)‖ ≤ 1 ∧
      B * ‖a.2 (p k)‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets (n + 1) (firstVariationMajorant K (p k) u ps)
      (fun x => deriv (fun t => vectorIncrementChain
        (ParamChain.exponentialSteps ps (p t)) f x) k) := by
  have hf : QPotential (n + 3) B f := hpotential ps [] (by rw [List.append_nil])
  induction ps with
  | nil =>
    simp only [ParamChain.exponentialSteps, List.map_nil, vectorIncrementChain, deriv_const,
      firstVariationMajorant]
    refine ⟨le_rfl, contDiff_const, ?_⟩
    intro j hj x
    simp
  | cons a ps ih =>
    have hpotTail : ∀ front tail, ps = front ++ tail →
        QPotential (n + 3) B
          (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f) := by
      intro front tail hsplit
      apply hpotential (a :: front) tail
      simpa only [List.cons_append, List.cons.injEq, true_and] using hsplit
    have hgeoTail : ∀ b ∈ ps, Real.exp (b.1 (p k)) ≤ 1 ∧ ‖b.2 (p k)‖ ≤ 1 ∧
        B * ‖b.2 (p k)‖ ^ 2 ≤ 1 / 2 :=
      fun b hb => hgeometry b (List.mem_cons_of_mem a hb)
    have hinner := ih hpotTail hgeoTail
    let F : P × E → ℝ := ParamChain.exponentialChain ps (fun z => f z.2)
    have hF : ParamRegular F := ParamChain.regular_exponentialChain ps
      (ParamChain.regular_fixedTerminal hf (by omega) P)
    have hGidentity : (fun y => fderiv ℝ F (p k,y) (u,0)) =
        fun y => deriv (fun t => vectorIncrementChain
          (ParamChain.exponentialSteps ps (p t)) f y) k := by
      funext y
      exact (parameter_curve_hasDerivAt (hF.1.differentiable (by norm_num)) hp y).deriv.symm
    have hG : QBoundedJets (n + 1) (firstVariationMajorant K (p k) u ps)
        (fun y => fderiv ℝ F (p k,y) (u,0)) := by rw [hGidentity]; exact hinner
    have hgeo := hgeometry a (List.mem_cons_self ..)
    have hstep := qBoundedJets_deriv_exponential_movingStep hF a.1 a.2 hp
      (hpotential [a] ps rfl) hG hgeo.1 hgeo.2.1 hgeo.2.2
    apply hstep.mono
    dsimp only [firstVariationMajorant]
    calc
      _ ≤ firstVariationMajorant K (p k) u ps +
          K * firstVariationMajorant K (p k) u ps * ‖a.2 (p k)‖ ^ 2 +
          K * ‖a.2 (p k)‖ ^ 2 * |Real.exp (a.1 (p k)) * a.1 u| +
          K * ‖a.2 (p k)‖ * ‖a.2 u‖ := by
        gcongr
        exact firstVariationMajorant_nonneg hK _ _ _
      _ = _ := by ring

theorem qBoundedJets_first_exponentialChain_of_energy
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {p : ℝ → P} {u : P} {k : ℝ}
    (hp : HasDerivAt p u k) {n : ℕ} {B K : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f) (hK : 0 ≤ K)
    (hTilt : tiltedStabilityCoefficient (n + 1) (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient n (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient (n + 1) (B + 1) ≤ K)
    (hgeometry : ∀ a ∈ ps, Real.exp (a.1 (p k)) ≤ 1 ∧ ‖a.2 (p k)‖ ≤ 1 ∧
      (B + 1) * ‖a.2 (p k)‖ ^ 2 ≤ 1 / 2)
    (hbudget : (stepStabilityCoefficient (n + 3) (B + 1) + 1) *
      chainEnergy (ParamChain.exponentialSteps ps (p k)) ≤ 1)
    (hcurv : (B + 1) * chainEnergy (ParamChain.exponentialSteps ps (p k)) ≤ 1 / 2) :
    QBoundedJets (n + 1) (firstVariationMajorant K (p k) u ps)
      (fun x => deriv (fun t => vectorIncrementChain
        (ParamChain.exponentialSteps ps (p t)) f x) k) := by
  apply qBoundedJets_first_exponentialChain ps hp hK hTilt hMass hDir _ hgeometry
  intro front tail hsplit
  have hpath : ParamChain.exponentialSteps ps (p k) =
      ParamChain.exponentialSteps front (p k) ++ ParamChain.exponentialSteps tail (p k) := by
    rw [hsplit]
    exact List.map_append
  apply qPotential_chain_tail (ParamChain.exponentialSteps front (p k))
    (ParamChain.exponentialSteps tail (p k)) hf (by omega)
  · intro b hb
    rw [← hpath] at hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ⟨(Real.exp_pos _).le, (hgeometry a ha).1⟩
  · rw [← hpath]
    exact hbudget
  · rw [← hpath]
    exact hcurv

theorem qBoundedJets_first_curveChain_of_energy
    (ps : List (ℝ → ℝ × E)) {k : ℝ} {n : ℕ} {B K : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f)
    (hreg : ∀ a ∈ ps, ContDiffAt ℝ 2 a k) (hpos : ∀ a ∈ ps, 0 < (a k).1)
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (n + 1) (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient n (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient (n + 1) (B + 1) ≤ K)
    (hgeometry : ∀ a ∈ ps, (a k).1 ≤ 1 ∧ ‖(a k).2‖ ≤ 1 ∧
      (B + 1) * ‖(a k).2‖ ^ 2 ≤ 1 / 2)
    (hbudget : (stepStabilityCoefficient (n + 3) (B + 1) + 1) *
      chainEnergy (ps.map (fun a => a k)) ≤ 1)
    (hcurv : (B + 1) * chainEnergy (ps.map (fun a => a k)) ≤ 1 / 2) :
    QBoundedJets (n + 1)
      (firstVariationMajorant K (ParamChain.logParameters ps k)
        (deriv (ParamChain.logParameters ps) k) (ParamChain.coordinateSteps ps.length))
      (fun x => deriv (fun t => vectorIncrementChain (ps.map (fun a => a t)) f x) k) := by
  have hp := (ParamChain.logParameters_contDiffAt ps hreg hpos).differentiableAt
    (by norm_num : (2 : WithTop ℕ∞) ≠ 0) |>.hasDerivAt
  have hpath := ParamChain.coordinateSteps_apply ps k hpos
  have hgeom : ∀ a ∈ ParamChain.coordinateSteps ps.length,
      Real.exp (a.1 (ParamChain.logParameters ps k)) ≤ 1 ∧
      ‖a.2 (ParamChain.logParameters ps k)‖ ≤ 1 ∧
      (B + 1) * ‖a.2 (ParamChain.logParameters ps k)‖ ^ 2 ≤ 1 / 2 := by
    intro a ha
    have hmem : (Real.exp (a.1 (ParamChain.logParameters ps k)),
        a.2 (ParamChain.logParameters ps k)) ∈
        ParamChain.exponentialSteps (ParamChain.coordinateSteps ps.length) (ParamChain.logParameters ps k) :=
      List.mem_map.mpr ⟨a, ha, rfl⟩
    rw [hpath] at hmem
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hmem
    have H := hgeometry b hb
    rw [heq] at H
    exact H
  have hactual := qBoundedJets_first_exponentialChain_of_energy
    (ParamChain.coordinateSteps ps.length) hp hf hK hTilt hMass hDir hgeom
    (by rw [hpath]; exact hbudget) (by rw [hpath]; exact hcurv)
  have hevent : ∀ᶠ t in 𝓝 k, ∀ a ∈ ps, 0 < (a t).1 := by
    have hget : ∀ᶠ t in 𝓝 k, ∀ i : Fin ps.length, 0 < (ps.get i t).1 := by
      apply Filter.eventually_all.mpr
      intro i
      exact (hreg _ (List.get_mem ps i)).fst.continuousAt.eventually
        (Ioi_mem_nhds (hpos _ (List.get_mem ps i)))
    filter_upwards [hget] with t ht a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact ht i
  have heq : (fun x => deriv (fun t => vectorIncrementChain (ps.map (fun a => a t)) f x) k) =
      fun x => deriv (fun t => vectorIncrementChain
        (ParamChain.exponentialSteps (ParamChain.coordinateSteps ps.length)
          (ParamChain.logParameters ps t)) f x) k := by
    funext x
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hevent] with t ht
    rw [ParamChain.coordinateSteps_apply ps t ht]
  rw [heq]
  exact hactual

end MovingTerminal

end SKBarriers2.StepCalculus
