module

public import SKBarriers2.Analysis.ParamStep3

@[expose] public section

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
open scoped Topology

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def secondCenteredScore (μ : ℝ) (v w : E) (f g : E → ℝ) (x : E) (t : ℝ) : ℝ :=
  g (x + t • v) - g x + μ * (f (x + t • v) - f x) +
    t * fderiv ℝ f (x + t • v) w

def secondScoreVariance (m μ : ℝ) (v w : E) (f g : E → ℝ) (x : E) : ℝ :=
  noiseMean m v f x (fun t => secondCenteredScore μ v w f g x t ^ 2) -
    noiseMean m v f x (secondCenteredScore μ v w f g x) ^ 2

theorem qBoundedJets_secondCenteredScore {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g)
    (μ : ℝ) (v w : E) (t : ℝ) :
    QBoundedJets 1 ((A * ‖v‖ + |μ| * B * ‖v‖ + B * ‖w‖) * |t|)
      (fun x => secondCenteredScore μ v w f g x t) := by
  have hgp : QPotential 2 A g :=
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 2 ≤ 3))).potential
  have hG := hgp.increment (t • v)
  have hF := ((hf.of_le (by norm_num : 2 ≤ 3)).increment (t • v)).const_smul μ
  have hD := (((hf.derivativeJets.of_le (by norm_num : 1 ≤ 2)).apply_const w).translate
    (t • v)).const_smul t
  convert (hG.add hF).add hD using 1
  · rw [norm_smul, Real.norm_eq_abs]
    ring
  · rfl

theorem qBoundedJets_secondScoreVariance {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (μ : ℝ) (v w : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets 1
      (potentialCovarianceCoefficient 1 B *
        (A * ‖v‖ + |μ| * B * ‖v‖ + B * ‖w‖) ^ 2)
      (secondScoreVariance m μ v w f g) := by
  let C := A * ‖v‖ + |μ| * B * ‖v‖ + B * ‖w‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity [hf.nonneg, hg.nonneg]
  have hR : ContDiff ℝ 1 (fun z : ℝ × E => secondCenteredScore μ v w f g z.2 z.1) := by
    have hline : ContDiff ℝ 1 (fun z : ℝ × E => z.2 + z.1 • v) :=
      contDiff_snd.add (contDiff_fst.smul contDiff_const)
    have hD : ContDiff ℝ 1 (fun z : ℝ × E => fderiv ℝ f (z.2 + z.1 • v) w) :=
      ((hf.smooth.fderiv_right (m := 1) (by norm_num)).comp
        hline).clm_apply contDiff_const
    exact (((hg.smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).comp hline).sub
      ((hg.smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).comp contDiff_snd)).add
        (contDiff_const.mul (((hf.smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).comp
          hline).sub ((hf.smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).comp contDiff_snd)))
      |>.add (contDiff_fst.mul hD)
  have hRj (t : ℝ) : QBoundedJets 1 (C * |t| ^ 1)
      (fun x => secondCenteredScore μ v w f g x t) := by
    simpa only [pow_one] using qBoundedJets_secondCenteredScore hf hg μ v w t
  have hR2j (t : ℝ) : QBoundedJets 1 ((2 * C ^ 2) * |t| ^ 2)
      (fun x => secondCenteredScore μ v w f g x t ^ 2) := by
    convert (hRj t).mul (hRj t) using 1
    · ring_nf
    · funext x
      ring
  have hR2 : ContDiff ℝ 1 (fun z : ℝ × E => secondCenteredScore μ v w f g z.2 z.1 ^ 2) :=
    hR.pow 2
  have hM := qBoundedJets_noiseMean_poly (hf.of_le (by norm_num : 2 ≤ 3)) hC 1 hR hRj hm v hv
  have hM2 := qBoundedJets_noiseMean_poly (g := fun x t => secondCenteredScore μ v w f g x t ^ 2)
    (hf.of_le (by norm_num : 2 ≤ 3))
    (show 0 ≤ 2 * C ^ 2 by positivity) 2 hR2 hR2j hm v hv
  convert hM2.sub (hM.mul hM) using 1
  · dsimp only [potentialCovarianceCoefficient]
    norm_num
    ring
  · funext x
    simp only [secondScoreVariance, pow_two]

def mixedDirectionSource (m : ℝ) (v w : E) (f g : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ (fderiv ℝ g) x v w + m * (fderiv ℝ g x w * fderiv ℝ f x v)

theorem qBoundedJets_mixedDirectionSource {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v w : E) :
    QBoundedJets 1 ((1 + 2 * B) * A * ‖v‖ * ‖w‖)
      (mixedDirectionSource m v w f g) := by
  have hH := (hg.derivativeJets.derivativeJets.apply_const v).apply_const w
  have hW := (hg.derivativeJets.of_le (by norm_num : 1 ≤ 2)).apply_const w
  have hV := (hf.derivativeJets.of_le (by norm_num : 1 ≤ 2)).apply_const v
  have H := hH.add ((hW.mul hV).const_smul m)
  apply H.mono
  rw [abs_of_nonneg hm.1]
  have h := mul_le_of_le_one_left
    (show 0 ≤ (2 : ℝ) ^ 1 * (A * ‖w‖) * (B * ‖v‖) by positivity [hf.nonneg, hg.nonneg]) hm.2
  norm_num at h ⊢
  nlinarith

theorem qBoundedJets_noiseHessian {B : ℝ} {f : E → ℝ}
    (hf : QPotential 3 B f) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (v w : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets 1 (noiseAverageCoefficient 1 2 B * B * ‖w‖ ^ 2)
      (fun x => noiseMean m v f x (fun t => t ^ 2 *
        fderiv ℝ (fderiv ℝ f) (x + t • v) w w)) := by
  have hH := (hf.derivativeJets.derivativeJets.apply_const w).apply_const w
  have hc : ContDiff ℝ 1 (fun z : ℝ × E => z.1 ^ 2 *
      fderiv ℝ (fderiv ℝ f) (z.2 + z.1 • v) w w) :=
    (contDiff_fst.pow 2).mul
      (hH.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const)))
  have hj (t : ℝ) : QBoundedJets 1 ((B * ‖w‖ ^ 2) * |t| ^ 2)
      (fun x => t ^ 2 * fderiv ℝ (fderiv ℝ f) (x + t • v) w w) := by
    convert (hH.translate (t • v)).const_smul (t ^ 2) using 1
    rw [abs_pow, sq_abs]
    ring
  convert qBoundedJets_noiseMean_poly
    (g := fun x t => t ^ 2 * fderiv ℝ (fderiv ℝ f) (x + t • v) w w)
    (hf.of_le (by norm_num : 2 ≤ 3))
    (show 0 ≤ B * ‖w‖ ^ 2 by positivity [hf.nonneg]) 2 hc hj hm v hv using 1
  ring

end SKBarriers2.StepCalculus

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem noise_mixedDirectionSource {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g) (m : ℝ) (v w x : E) :
    noiseMean m v f x (fun t => t * fderiv ℝ g (x + t • v) w) =
      tiltedAverage m v f (mixedDirectionSource m v w f g) x := by
  have hD := hg.derivativeJets.apply_const w
  have hH := (hg.derivativeJets.derivativeJets.apply_const v).apply_const w
  have hV := hf.derivativeJets.apply_const v
  have hd (t : ℝ) : HasDerivAt (fun a : ℝ => fderiv ℝ g (x + a • v) w)
      (fderiv ℝ (fderiv ℝ g) (x + t • v) v w) t := by
    have hline : HasDerivAt (fun a : ℝ => x + a • v) v t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
    have H := (((hg.smooth.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline).clm_apply
        (hasDerivAt_const t w)
    simpa only [Function.comp_def, map_zero, add_zero] using H
  have hc : Continuous (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (x + t • v) v w) :=
    hH.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hG : HasExpGrowth (fun t : ℝ => fderiv ℝ g (x + t • v) w) :=
    HasExpGrowth.of_bounded hD.nonneg (fun t => hD.norm_le _)
  have hG' : HasExpGrowth (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (x + t • v) v w) :=
    HasExpGrowth.of_bounded hH.nonneg (fun t => hH.norm_le _)
  have hiH := integrable_tilted_shift hf (by norm_num) hH m v x
  have hiP := integrable_tilted_shift hf (by norm_num) (hD.mul hV) m v x
  rw [tilted_integration_by_parts hf (by norm_num) m v x hd hc hG hG']
  unfold tiltedAverage mixedDirectionSource noiseMean
  rw [← integral_const_mul, ← integral_add hiH (hiP.const_mul m)]

theorem memLp_noise_of_growth {B : ℝ} {f : E → ℝ} (hf : QPotential 3 B f)
    (m : ℝ) (v x : E) {G : ℝ → ℝ} (hc : Continuous G) (hG : HasExpGrowth G) :
    MemLp G 2 (stepLaw m v f x) := by
  rw [memLp_two_iff_integrable_sq]
  · simpa only [pow_two] using integrable_noise hf (by norm_num) m v x
      (hG.mul hG) (hc.mul hc)
  · exact hc.aestronglyMeasurable

theorem memLp_secondScore {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g)
    (m η : ℝ) (v w x : E) :
    MemLp (fun t => g (x + t • v) + η * f (x + t • v) +
      t * fderiv ℝ f (x + t • v) w) 2 (stepLaw m v f x) := by
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hG : MemLp (fun t => g (x + t • v)) 2 (stepLaw m v f x) :=
    MemLp.of_bound (hg.smooth.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable A
      (ae_of_all _ (fun t => hg.norm_le _))
  have hF : MemLp (fun t => f (x + t • v)) 2 (stepLaw m v f x) :=
    memLp_tilted_mul (((hf.boundedDerivs (by norm_num)).compCLM (vectorTranslation v)).mem_interior_integrableExpSet_section x m) 2
  have hD := hf.derivativeJets.apply_const w
  have hcD : Continuous (fun t : ℝ => fderiv ℝ f (x + t • v) w) :=
    hD.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hgD : HasExpGrowth (fun t : ℝ => fderiv ℝ f (x + t • v) w) :=
    HasExpGrowth.of_bounded hD.nonneg (fun t => hD.norm_le _)
  have hN := memLp_noise_of_growth hf m v x (continuous_id.mul hcD)
    ((HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)).mul hgD)
  exact (hG.add (hF.const_mul η)).add hN

theorem secondScoreVariance_eq_variance {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g)
    (m η : ℝ) (v w x : E) :
    secondScoreVariance m η v w f g x =
      variance (fun t => g (x + t • v) + η * f (x + t • v) +
        t * fderiv ℝ f (x + t • v) w) (stepLaw m v f x) := by
  let _ := stepLaw_probability hf (by norm_num) m v x
  let S : ℝ → ℝ := fun t => g (x + t • v) + η * f (x + t • v) +
    t * fderiv ℝ f (x + t • v) w
  let c := g x + η * f x
  have hS : MemLp S 2 (stepLaw m v f x) := memLp_secondScore hf hg m η v w x
  have hR : secondCenteredScore η v w f g x = S - fun _ => c := by
    funext t
    dsimp only [secondCenteredScore, S, c, Pi.sub_apply]
    ring
  have hV := variance_eq_sub (hS.sub (memLp_const c))
  have hCentered : secondScoreVariance m η v w f g x =
      variance (S - fun _ => c) (stepLaw m v f x) := by
    simpa only [secondScoreVariance, noiseMean, hR, Pi.pow_apply] using hV.symm
  exact hCentered.trans (variance_sub_const hS.aestronglyMeasurable c)

end SKBarriers2.StepCalculus

namespace SKBarriers2.ParamChain

section CurveCalculus

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance : NormedAddCommGroup (P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × X →L[ℝ] ℝ) := inferInstance

theorem second_parameter_curve {F : P × X → ℝ} (hF : ContDiff ℝ 2 F)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (x : X) :
    deriv (deriv (fun t => F (p t,x))) k =
      fderiv ℝ (fderiv ℝ F) (p k,x) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,x) (deriv (deriv p) k,0) := by
  have hd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have heq : deriv (fun t => F (p t,x)) =ᶠ[𝓝 k]
      fun t => fderiv ℝ F (p t,x) (deriv p t,0) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact ((hF.differentiable (by norm_num) (p t,x)).hasFDerivAt.comp_hasDerivAt t
      ((ht.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const t x))).deriv
  have hD := ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (p k,x)).hasFDerivAt.comp_hasDerivAt k (hd.prodMk (hasDerivAt_const k x))
  have hBoth := hD.clm_apply (hdd.prodMk (hasDerivAt_const k (0 : X)))
  rw [heq.deriv_eq]
  exact hBoth.deriv

theorem second_exp_neg_mul {a z : ℝ → ℝ} {k : ℝ}
    (ha : ContDiffAt ℝ 2 a k) (hz : ContDiffAt ℝ 2 z k) :
    deriv (deriv (fun t => Real.exp (-a t) * z t)) k =
      Real.exp (-a k) * (deriv (deriv z) k - 2 * deriv a k * deriv z k +
        (deriv a k ^ 2 - deriv (deriv a) k) * z k) := by
  have ha1 := (ha.differentiableAt (by norm_num)).hasDerivAt
  have hz1 := (hz.differentiableAt (by norm_num)).hasDerivAt
  have ha2 := ((ha.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hz2 := ((hz.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have heq : deriv (fun t => Real.exp (-a t) * z t) =ᶠ[𝓝 k]
      fun t => Real.exp (-a t) * (deriv z t - deriv a t * z t) := by
    filter_upwards [ha.eventually (by norm_num), hz.eventually (by norm_num)] with t hat hzt
    have H := ((((hat.differentiableAt (by norm_num)).hasDerivAt.neg).exp).fun_mul
      (hzt.differentiableAt (by norm_num)).hasDerivAt).deriv
    simp only [Pi.neg_apply] at H
    rw [H]
    ring
  have H := ((ha1.neg.exp).fun_mul (hz2.fun_sub (ha2.fun_mul hz1))).deriv
  simp only [Pi.neg_apply] at H
  rw [heq.deriv_eq, H]
  ring

end CurveCalculus

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

section AffineJets

variable {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

local instance : NormedAddCommGroup (Y →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Y →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (Y →L[ℝ] Y →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Y →L[ℝ] Y →L[ℝ] ℝ) := inferInstance

theorem first_affine_apply {F : Y → ℝ} (hF : ContDiff ℝ 2 F)
    (L : Z →L[ℝ] Y) (b : Y) (q u : Z) :
    fderiv ℝ (fun p => F (L p + b)) q u = fderiv ℝ F (L q + b) (L u) := by
  have h := ((hF.differentiable (by norm_num) (L q + b)).hasFDerivAt.comp q
    (L.hasFDerivAt.add_const b)).fderiv
  exact congrArg (fun D : Z →L[ℝ] ℝ => D u) h

theorem second_affine_apply {F : Y → ℝ} (hF : ContDiff ℝ 2 F)
    (L : Z →L[ℝ] Y) (b : Y) (q u w : Z) :
    fderiv ℝ (fderiv ℝ (fun p => F (L p + b))) q u w =
      fderiv ℝ (fderiv ℝ F) (L q + b) (L u) (L w) := by
  let A : (Y →L[ℝ] ℝ) →L[ℝ] Z →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ Z Y ℝ).flip L
  have heq : fderiv ℝ (fun p => F (L p + b)) = fun p => A (fderiv ℝ F (L p + b)) := by
    funext p
    exact ((hF.differentiable (by norm_num) (L p + b)).hasFDerivAt.comp p
      (L.hasFDerivAt.add_const b)).fderiv
  have hd := A.hasFDerivAt.comp q
    (((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
      (L q + b)).hasFDerivAt.comp q (L.hasFDerivAt.add_const b))
  change HasFDerivAt (fun p => A (fderiv ℝ F (L p + b)))
    (A.comp ((fderiv ℝ (fderiv ℝ F) (L q + b)).comp L)) q at hd
  rw [heq, hd.fderiv]
  rfl

theorem first_exp_linear_mul {F : Y → ℝ} (hF : ContDiff ℝ 2 F)
    (M : Y →L[ℝ] ℝ) (q u : Y) :
    fderiv ℝ (fun p => Real.exp (M p) * F p) q u =
      Real.exp (M q) * (M u * F q + fderiv ℝ F q u) := by
  rw [((M.hasFDerivAt.exp).fun_mul (hF.differentiable (by norm_num) q).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem second_exp_linear_mul {F : Y → ℝ} (hF : ContDiff ℝ 2 F)
    (M : Y →L[ℝ] ℝ) (q u : Y) :
    fderiv ℝ (fderiv ℝ (fun p => Real.exp (M p) * F p)) q u u =
      Real.exp (M q) * ((M u) ^ 2 * F q + 2 * M u * fderiv ℝ F q u +
        fderiv ℝ (fderiv ℝ F) q u u) := by
  let G : Y → ℝ := fun p => Real.exp (M p) * F p
  have hG : ContDiff ℝ 2 G := (M.contDiff.exp).mul hF
  have hline : HasDerivAt (fun t : ℝ => q + t • u) u 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add q
  have hLeft := (((hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    q).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)).clm_apply (hasDerivAt_const 0 u)
  have hfirst (p : Y) : fderiv ℝ G p u =
      Real.exp (M p) * (M u * F p + fderiv ℝ F p u) := first_exp_linear_mul hF M p u
  simp only [Function.comp_def] at hLeft
  simp_rw [hfirst] at hLeft
  have hE := (M.hasFDerivAt.comp_hasDerivAt 0 hline).exp
  have hU := (hF.differentiable (by norm_num) q).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hD := (((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    q).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)).clm_apply (hasDerivAt_const 0 u)
  have hRight := hE.fun_mul ((hU.const_mul (M u)).fun_add hD)
  have H := hLeft.unique hRight
  simp only [Function.comp_def, zero_smul, add_zero, map_zero] at H
  rw [H]
  ring

end AffineJets

end SKBarriers2.ParamChain

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def secondVariationStep (m : ℝ) (v : E) (f g h : E → ℝ)
    (dm ddm : ℝ) (w b : E) (x : E) : ℝ :=
  tiltedAverage m v f h x +
    2 * tiltedAverage m v f (mixedDirectionSource m v w f g) x +
    noiseMean m v f x (fun t => t ^ 2 * fderiv ℝ (fderiv ℝ f) (x + t • v) w w) +
    tiltedAverage m v f (directionSource m v b f) x +
    m * secondScoreVariance m (dm / m) v w f g x +
    (ddm - 2 * dm ^ 2 / m) * massSensitivity m v f x

def secondVariationBound (B A H m dm ddm : ℝ) (v w b : E) : ℝ :=
  H + tiltedStabilityCoefficient 1 B * H * ‖v‖ ^ 2 +
    2 * (tiltedCoarseCoefficient 1 B * (1 + 2 * B)) * A * ‖v‖ * ‖w‖ +
    noiseAverageCoefficient 1 2 B * B * ‖w‖ ^ 2 +
    directionSensitivityCoefficient 1 B * ‖v‖ * ‖b‖ +
    potentialCovarianceCoefficient 1 B *
      (A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖) ^ 2 +
    massSensitivityJetCoefficient 0 B * ‖v‖ ^ 2 * |ddm - 2 * dm ^ 2 / m|

theorem qBoundedJets_secondVariationStep {B A H : ℝ} {f g h : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g) (hh : QBoundedJets 1 H h)
    {m : ℝ} (hm : m ∈ Ioc (0 : ℝ) 1) (v w b : E) (dm ddm : ℝ)
    (hv : ‖v‖ ≤ 1) (hsmall : B * ‖v‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets 1 (secondVariationBound B A H m dm ddm v w b)
      (secondVariationStep m v f g h dm ddm w b) := by
  have hmcc : m ∈ Icc (0 : ℝ) 1 := ⟨hm.1.le, hm.2⟩
  have hcurv : m * (B * ‖v‖ ^ 2) ≤ 1 / 2 :=
    (mul_le_of_le_one_left (by positivity [hf.nonneg]) hm.2).trans hsmall
  have hT := qBoundedJets_tiltedAverage 1 hf (by norm_num) (by norm_num) hh hmcc v hcurv
  have hD := (qBoundedJets_tiltedAverage_coarse 1 hf (by norm_num) (by norm_num)
    (qBoundedJets_mixedDirectionSource hf hg hmcc v w) hmcc v).const_smul 2
  have hN := qBoundedJets_noiseHessian hf hmcc v w hv
  have hB := qBoundedJets_directionSensitivity hf hmcc v b
  have hV := qBoundedJets_secondScoreVariance hf hg hmcc (dm / m) v w hv
  have hVm : QBoundedJets 1
      (potentialCovarianceCoefficient 1 B *
        (A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖) ^ 2)
      (fun x => m * secondScoreVariance m (dm / m) v w f g x) :=
    (hV.const_smul m).mono (mul_le_of_le_one_left hV.nonneg (by
      rw [abs_of_pos hm.1]
      exact hm.2))
  have hM := (qBoundedJets_massSensitivity (n := 0) hf hm v hv hsmall).const_smul
    (ddm - 2 * dm ^ 2 / m)
  convert ((((hT.add hD).add hN).add hB).add hVm).add hM using 1
  · dsimp only [secondVariationBound]
    norm_num
    ring
  · rfl

end SKBarriers2.StepCalculus

namespace SKBarriers2.ParamChain

section NormalizedLogStep

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem deriv_linear_parameter {p : ℝ → P} {k : ℝ} (hp : DifferentiableAt ℝ p k)
    (M : P →L[ℝ] ℝ) : deriv (fun t => M (p t)) k = M (deriv p k) :=
  (M.hasFDerivAt.comp_hasDerivAt k hp.hasDerivAt).deriv

theorem second_linear_parameter {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k)
    (M : P →L[ℝ] ℝ) : deriv (deriv (fun t => M (p t))) k = M (deriv (deriv p) k) := by
  have heq : deriv (fun t => M (p t)) =ᶠ[𝓝 k] fun t => M (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact deriv_linear_parameter (ht.differentiableAt (by norm_num)) M
  rw [heq.deriv_eq]
  exact (M.hasFDerivAt.comp_hasDerivAt k
    (((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt)).deriv

theorem second_normalized_logStep {H : P × (X × ℝ) → ℝ} (hH : ParamRegular H)
    (M : P →L[ℝ] ℝ) {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (x : X) :
    let G : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
    let Z := gaussianStep 1 G
    let q := p k
    let u := deriv p k
    let a := deriv (deriv p) k
    let μ := gaussianStepLaw 1 G (q,x)
    deriv (deriv (fun t => Real.exp (-M (p t)) * Z (p t,x))) k =
      Real.exp (-M q) *
        ((∫ t, fderiv ℝ (fderiv ℝ H) (q,(x,t)) (u,0) (u,0) +
            (fderiv ℝ H (q,(x,t)) (u,0)) ^ 2 ∂μ) -
          (∫ t, fderiv ℝ H (q,(x,t)) (u,0) ∂μ) ^ 2 +
          (∫ t, fderiv ℝ H (q,(x,t)) (a,0) ∂μ) -
          2 * M u * (∫ t, fderiv ℝ H (q,(x,t)) (u,0) ∂μ) +
          ((M u) ^ 2 - M a) * Z (q,x)) := by
  let G : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
  let Z := gaussianStep 1 G
  have hZ : ParamRegular Z := hH.gaussianStep 1
  have hzc : ContDiffAt ℝ 2 (fun t => Z (p t,x)) k :=
    hZ.1.contDiffAt.comp k (hp.prodMk contDiffAt_const)
  have hac : ContDiffAt ℝ 2 (fun t => M (p t)) k := M.contDiff.contDiffAt.comp k hp
  have hfirst : deriv (fun t => Z (p t,x)) k =
      fderiv ℝ Z (p k,x) (deriv p k,0) := by
    simpa only [Function.comp_def] using
      ((hZ.1.differentiable (by norm_num) (p k,x)).hasFDerivAt.comp_hasDerivAt k
        ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k x))).deriv
  change deriv (deriv (fun t => Real.exp (-M (p t)) * Z (p t,x))) k = _
  rw [second_exp_neg_mul hac hzc, deriv_linear_parameter (hp.differentiableAt (by norm_num)),
    second_linear_parameter hp, second_parameter_curve hZ.1 hp x, hfirst,
    second_parameter_gaussianStep hH]
  rw [hH.parameterDerivative_gaussianStep 1 (p k,x) (deriv p k),
    hH.parameterDerivative_gaussianStep 1 (p k,x) (deriv (deriv p) k)]
  rfl

end NormalizedLogStep

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

section MovingInputJets

local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def movingLogInput (F : P × E → ℝ) (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) :
    P × (E × ℝ) → ℝ :=
  fun z => Real.exp (M z.1) * F (z.1, z.2.1 + z.2.2 • V z.1)

theorem regular_movingLogInput {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) : ParamRegular (movingLogInput F M V) :=
  regular_mul_exp_parameter (regular_movingInput hF V) M

theorem movingLogInput_parameter_jets {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) (q u : P) (x : E) (t : ℝ) :
    fderiv ℝ (movingLogInput F M V) (q,(x,t)) (u,0) =
      Real.exp (M q) * (M u * F (q,x + t • V q) +
        fderiv ℝ F (q,x + t • V q) (u,t • V u)) ∧
    fderiv ℝ (fderiv ℝ (movingLogInput F M V)) (q,(x,t)) (u,0) (u,0) =
      Real.exp (M q) * ((M u) ^ 2 * F (q,x + t • V q) +
        2 * M u * fderiv ℝ F (q,x + t • V q) (u,t • V u) +
        fderiv ℝ (fderiv ℝ F) (q,x + t • V q) (u,t • V u) (u,t • V u)) := by
  let H := movingLogInput F M V
  have hH : ParamRegular H := regular_movingLogInput hF M V
  let I : P →L[ℝ] P × (E × ℝ) := ContinuousLinearMap.inl ℝ P (E × ℝ)
  let L : P →L[ℝ] P × E := (ContinuousLinearMap.id ℝ P).prod (t • V)
  let b : P × E := (0,x)
  let U : P → ℝ := fun p => F (L p + b)
  have hU : ContDiff ℝ 2 U := hF.1.comp (L.contDiff.add contDiff_const)
  have hpair (p : P) : I p + (0,(x,t)) = (p,(x,t)) := by
    ext <;> simp [I]
  have hfield (p : P) : L p + b = (p,x + t • V p) := by
    apply Prod.ext
    · simp [L, b]
    · change t • V p + x = x + t • V p
      exact add_comm _ _
  have hslice : (fun p => H (I p + (0,(x,t)))) = fun p => Real.exp (M p) * U p := by
    funext p
    rw [hpair]
    dsimp only [H, movingLogInput, U]
    rw [hfield]
  have h1 := first_affine_apply hH.1 I (0,(x,t)) q u
  have h2 := second_affine_apply hH.1 I (0,(x,t)) q u u
  rw [hslice, first_exp_linear_mul hU M] at h1
  rw [hslice, second_exp_linear_mul hU M] at h2
  have hU1 := first_affine_apply hF.1 L b q u
  have hU2 := second_affine_apply hF.1 L b q u u
  change fderiv ℝ U q u = _ at hU1
  change fderiv ℝ (fderiv ℝ U) q u u = _ at hU2
  rw [hU1, hfield] at h1
  rw [hU1, hU2, hfield] at h2
  have hUq : U q = F (q,x + t • V q) := congrArg F (hfield q)
  rw [hUq] at h1 h2
  rw [hpair] at h1 h2
  exact ⟨h1.symm, h2.symm⟩

end MovingInputJets

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

section SpatialSlices

local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : NormedAddCommGroup (P × E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × E →L[ℝ] ℝ) := inferInstance

theorem spatial_slice_jets {F : P × E → ℝ} (hF : ParamRegular F)
    (q u : P) (y w : E) :
    fderiv ℝ (fun z => F (q,z)) y w = fderiv ℝ F (q,y) (0,w) ∧
    fderiv ℝ (fderiv ℝ (fun z => F (q,z))) y w w =
      fderiv ℝ (fderiv ℝ F) (q,y) (0,w) (0,w) ∧
    fderiv ℝ (fun z => fderiv ℝ F (q,z) (u,0)) y w =
      fderiv ℝ (fderiv ℝ F) (q,y) (0,w) (u,0) := by
  let L : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  have heq (z : E) : L z + (q,0) = (q,z) := by ext <;> simp [L]
  have h1 := first_affine_apply hF.1 L (q,0) y w
  have h2 := second_affine_apply hF.1 L (q,0) y w w
  simp_rw [heq] at h1 h2
  have hp : HasFDerivAt (fun z : E => (q,z)) L y :=
    (hasFDerivAt_const q y).prodMk (hasFDerivAt_id y)
  have hd := (((hF.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    (q,y)).hasFDerivAt.comp y hp).clm_apply (hasFDerivAt_const (u,(0 : E)) y)
  have h3 := congrArg (fun D : E →L[ℝ] ℝ => D w) hd.fderiv
  change fderiv ℝ (fun z => fderiv ℝ F (q,z) (u,0)) y w =
    fderiv ℝ F (q,y) 0 + fderiv ℝ (fderiv ℝ F) (q,y) (0,w) (u,0) at h3
  exact ⟨h1, h2, by simpa only [map_zero, zero_add] using h3⟩

theorem mixed_parameter_spatial_jet {F : P × E → ℝ} (hF : ParamRegular F)
    (q u : P) (y w : E) (t : ℝ) :
    fderiv ℝ (fderiv ℝ F) (q,y) (u,t • w) (u,t • w) =
      fderiv ℝ (fderiv ℝ F) (q,y) (u,0) (u,0) +
        2 * t * fderiv ℝ (fun z => fderiv ℝ F (q,z) (u,0)) y w +
        t ^ 2 * fderiv ℝ (fderiv ℝ (fun z => F (q,z))) y w w := by
  have hsplit : (u,t • w) = (u,(0 : E)) + t • ((0 : P),w) := by ext <;> simp
  have hs := (hF.1.contDiffAt.isSymmSndFDerivAt (by norm_num) :
    IsSymmSndFDerivAt ℝ F (q,y)) (u,0) (0,w)
  obtain ⟨_, h2, h3⟩ := spatial_slice_jets hF q u y w
  rw [hsplit]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [hs, ← h2, ← h3]
  ring

end SpatialSlices

end SKBarriers2.ParamChain

namespace SKBarriers2.StepCalculus

theorem normalized_second_moments {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {m η ν T : ℝ} (hm : m ≠ 0) {A B C S K f : ℝ → ℝ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ)
    (hS : MemLp S 2 μ) (hK : Integrable K μ) (hf : Integrable f μ)
    (hfirst : ∀ t, A t = m * S t)
    (hsecond : ∀ t, B t + C t - 2 * η * A t = m * K t + m * (ν - η ^ 2) * f t) :
    m⁻¹ * ((∫ t, B t + A t ^ 2 ∂μ) - (∫ t, A t ∂μ) ^ 2 +
      (∫ t, C t ∂μ) - 2 * η * (∫ t, A t ∂μ) + (η ^ 2 - ν) * (m * T)) =
      (∫ t, K t ∂μ) + m * variance S μ + (ν - η ^ 2) * ((∫ t, f t ∂μ) - T) := by
  have hS2 : Integrable (fun t => S t ^ 2) μ := hS.integrable_sq
  have hA2 : Integrable (fun t => A t ^ 2) μ := by
    simpa only [hfirst, mul_pow] using hS2.const_mul (m ^ 2)
  have hmean : (∫ t, A t ∂μ) = m * (∫ t, S t ∂μ) := by
    simp_rw [hfirst]
    rw [integral_const_mul]
  have hmean2 : (∫ t, A t ^ 2 ∂μ) = m ^ 2 * (∫ t, S t ^ 2 ∂μ) := by
    simp_rw [hfirst, mul_pow]
    rw [integral_const_mul]
  have hcombined := congrArg (fun G : ℝ → ℝ => ∫ t, G t ∂μ) (funext hsecond)
  rw [integral_sub (f := fun t => B t + C t) (g := fun t => 2 * η * A t)
      (hB.add hC) (hA.const_mul (2 * η)), integral_add hB hC,
    integral_const_mul, integral_add (f := fun t => m * K t)
      (g := fun t => m * (ν - η ^ 2) * f t) (hK.const_mul m) (hf.const_mul (m * (ν - η ^ 2))),
    integral_const_mul, integral_const_mul] at hcombined
  calc
    _ = m⁻¹ * (((∫ t, B t ∂μ) + (∫ t, C t ∂μ) - 2 * η * (∫ t, A t ∂μ)) +
        m ^ 2 * ((∫ t, S t ^ 2 ∂μ) - (∫ t, S t ∂μ) ^ 2) + (η ^ 2 - ν) * (m * T)) := by
      rw [integral_add (f := B) (g := fun t => A t ^ 2) hB hA2, hmean, hmean2]
      ring
    _ = _ := by
      rw [hcombined, variance_eq_sub hS]
      simp only [Pi.pow_apply]
      field_simp [hm]
      ring

end SKBarriers2.StepCalculus

namespace SKBarriers2.ParamChain

section CenteredMovingSource

local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem movingLogInput_second_source {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) (q u a : P) (x : E) (t : ℝ) :
    fderiv ℝ (fderiv ℝ (movingLogInput F M V)) (q,(x,t)) (u,0) (u,0) +
      fderiv ℝ (movingLogInput F M V) (q,(x,t)) (a,0) -
      2 * M u * fderiv ℝ (movingLogInput F M V) (q,(x,t)) (u,0) =
    Real.exp (M q) *
      ((fderiv ℝ (fderiv ℝ F) (q,x + t • V q) (u,0) (u,0) +
          fderiv ℝ F (q,x + t • V q) (a,0)) +
        2 * t * fderiv ℝ (fun z => fderiv ℝ F (q,z) (u,0)) (x + t • V q) (V u) +
        t ^ 2 * fderiv ℝ (fderiv ℝ (fun z => F (q,z))) (x + t • V q) (V u) (V u) +
        t * fderiv ℝ (fun z => F (q,z)) (x + t • V q) (V a) +
        (M a - (M u) ^ 2) * F (q,x + t • V q)) := by
  obtain ⟨h1, h2⟩ := movingLogInput_parameter_jets hF M V q u x t
  have ha := (movingLogInput_parameter_jets hF M V q a x t).1
  have hD (b : P) : fderiv ℝ F (q,x + t • V q) (b,t • V b) =
      fderiv ℝ F (q,x + t • V q) (b,0) +
        t * fderiv ℝ (fun z => F (q,z)) (x + t • V q) (V b) := by
    have hsplit : (b,t • V b) = (b,(0 : E)) + t • ((0 : P),V b) := by ext <;> simp
    rw [hsplit, map_add, map_smul,
      ← (spatial_slice_jets hF q b (x + t • V q) (V b)).1]
    rfl
  rw [h2, ha, h1, hD u, hD a,
    mixed_parameter_spatial_jet hF q u (x + t • V q) (V u) t]
  ring

end CenteredMovingSource

end SKBarriers2.ParamChain

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem integrable_noise_test_powers {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 1 C g) (m : ℝ) (v x : E) :
    Integrable (fun t => t * g (x + t • v)) (stepLaw m v f x) ∧
      Integrable (fun t => t ^ 2 * g (x + t • v)) (stepLaw m v f x) := by
  have hc : Continuous (fun t : ℝ => g (x + t • v)) :=
    hg.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hG : HasExpGrowth (fun t : ℝ => g (x + t • v)) :=
    HasExpGrowth.of_bounded hg.nonneg (fun t => hg.norm_le _)
  have hI : HasExpGrowth (fun t : ℝ => t) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  refine ⟨integrable_noise hf (by norm_num) m v x (hI.mul hG) (continuous_id.mul hc), ?_⟩
  simpa only [pow_two] using integrable_noise hf (by norm_num) m v x
    ((hI.mul hI).mul hG) ((continuous_id.mul continuous_id).mul hc)

end SKBarriers2.StepCalculus

namespace SKBarriers2.ParamChain

section FirstSource

local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem movingLogInput_first_source {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) (q u : P) (x : E) (t : ℝ) :
    fderiv ℝ (movingLogInput F M V) (q,(x,t)) (u,0) =
      Real.exp (M q) * (fderiv ℝ F (q,x + t • V q) (u,0) +
        M u * F (q,x + t • V q) +
        t * fderiv ℝ (fun z => F (q,z)) (x + t • V q) (V u)) := by
  rw [(movingLogInput_parameter_jets hF M V q u x t).1]
  have hsplit : (u,t • V u) = (u,(0 : E)) + t • ((0 : P),V u) := by ext <;> simp
  rw [hsplit, map_add, map_smul,
    ← (spatial_slice_jets hF q u (x + t • V q) (V u)).1]
  change _ = Real.exp (M q) * (_ + _ + _)
  ring

end FirstSource

end SKBarriers2.ParamChain

namespace SKBarriers2.ParamChain

section JetIntegrability

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance : NormedAddCommGroup (P × (X × ℝ) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × (X × ℝ) →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (P × (X × ℝ) →L[ℝ] P × (X × ℝ) →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × (X × ℝ) →L[ℝ] P × (X × ℝ) →L[ℝ] ℝ) := inferInstance

theorem integrable_parameter_jets {H : P × (X × ℝ) → ℝ} (hH : ParamRegular H)
    (q u : P) (x : X) :
    let μ := gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (q,x)
    Integrable (fun t => fderiv ℝ H (q,(x,t)) (u,0)) μ ∧
      Integrable (fun t => fderiv ℝ (fderiv ℝ H) (q,(x,t)) (u,0) (u,0)) μ := by
  have h1 : ParamExpGrowth (fun z : P × (X × ℝ) => fderiv ℝ H z (u,0)) :=
    hH.2.2.1.clm (ContinuousLinearMap.apply ℝ ℝ (u,0))
  have h2 : ParamExpGrowth (fun z : P × (X × ℝ) => fderiv ℝ (fderiv ℝ H) z (u,0) (u,0)) :=
    (hH.2.2.2.clm (ContinuousLinearMap.apply ℝ (P × (X × ℝ) →L[ℝ] ℝ) (u,0))).clm
      (ContinuousLinearMap.apply ℝ ℝ (u,0))
  have hc1 : Continuous (fun z : P × (X × ℝ) => fderiv ℝ H z (u,0)) :=
    (hH.1.fderiv_right (m := 1) (by norm_num)).continuous.clm_apply continuous_const
  have hc2 : Continuous (fun z : P × (X × ℝ) => fderiv ℝ (fderiv ℝ H) z (u,0) (u,0)) :=
    ((hH.1.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous.clm_apply
      continuous_const).clm_apply continuous_const
  exact ⟨h1.integrable_paramStepLaw hH hc1 1 (q,x), h2.integrable_paramStepLaw hH hc2 1 (q,x)⟩

end JetIntegrability

end SKBarriers2.ParamChain

namespace SKBarriers2.StepCalculus

section ActualSecondVariation

local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem second_deriv_exponential_movingStep {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B A H : ℝ}
    (hf : QPotential 3 B (fun y => F (p k,y)))
    (hg : QBoundedJets 3 A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hh : QBoundedJets 1 H (fun y =>
      fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0))) (x : E) :
    deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) x)) k =
      secondVariationStep (Real.exp (M (p k))) (V (p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0))
        (Real.exp (M (p k)) * M (deriv p k))
        (Real.exp (M (p k)) * ((M (deriv p k)) ^ 2 + M (deriv (deriv p) k)))
        (V (deriv p k)) (V (deriv (deriv p) k)) x := by
  let q := p k
  let u := deriv p k
  let a := deriv (deriv p) k
  let m := Real.exp (M q)
  let η := M u
  let ν := M a
  let v := V q
  let w := V u
  let b := V a
  let f : E → ℝ := fun y => F (q,y)
  let g : E → ℝ := fun y => fderiv ℝ F (q,y) (u,0)
  let h : E → ℝ := fun y => fderiv ℝ (fderiv ℝ F) (q,y) (u,0) (u,0) +
    fderiv ℝ F (q,y) (a,0)
  let I := ParamChain.movingLogInput F M V
  have hI : ParamRegular I := ParamChain.regular_movingLogInput hF M V
  let G : (P × E) × ℝ → ℝ := fun z => I (z.1.1,(z.1.2,z.2))
  let Z := gaussianStep 1 G
  let μ := stepLaw m v f x
  let _ := stepLaw_probability hf (by norm_num) m v x
  have hm : m ≠ 0 := Real.exp_ne_zero _
  have hlaw : gaussianStepLaw 1 G (q,x) = μ := by
    simp only [gaussianStepLaw, μ, stepLaw, G, I, ParamChain.movingLogInput, one_mul]
    rfl
  let A₁ : ℝ → ℝ := fun t => fderiv ℝ I (q,(x,t)) (u,0)
  let A₂ : ℝ → ℝ := fun t => fderiv ℝ (fderiv ℝ I) (q,(x,t)) (u,0) (u,0)
  let Aₐ : ℝ → ℝ := fun t => fderiv ℝ I (q,(x,t)) (a,0)
  let S : ℝ → ℝ := fun t => g (x + t • v) + η * f (x + t • v) +
    t * fderiv ℝ f (x + t • v) w
  let H₀ : ℝ → ℝ := fun t => h (x + t • v)
  let G₀ : ℝ → ℝ := fun t => t * fderiv ℝ g (x + t • v) w
  let Q₀ : ℝ → ℝ := fun t => t ^ 2 * fderiv ℝ (fderiv ℝ f) (x + t • v) w w
  let B₀ : ℝ → ℝ := fun t => t * fderiv ℝ f (x + t • v) b
  let K : ℝ → ℝ := fun t => H₀ t + 2 * G₀ t + Q₀ t + B₀ t
  have hiu := ParamChain.integrable_parameter_jets hI q u x
  have hia := (ParamChain.integrable_parameter_jets hI q a x).1
  rw [hlaw] at hiu hia
  have hS : MemLp S 2 μ := memLp_secondScore hf hg m η v w x
  have hfm : MemLp (fun t => f (x + t • v)) 2 μ :=
    memLp_tilted_mul (((hf.boundedDerivs (by norm_num)).compCLM (vectorTranslation v)).mem_interior_integrableExpSet_section x m) 2
  have hiH : Integrable H₀ μ := integrable_tilted_shift hf (by norm_num) hh m v x
  have hgd := (hg.derivativeJets.apply_const w).of_le (by norm_num : 1 ≤ 2)
  have hfd := (hf.derivativeJets.apply_const b).of_le (by norm_num : 1 ≤ 2)
  have hfww := (hf.derivativeJets.derivativeJets.apply_const w).apply_const w
  have hiG : Integrable G₀ μ := (integrable_noise_test_powers hf hgd m v x).1
  have hiQ : Integrable Q₀ μ := (integrable_noise_test_powers hf hfww m v x).2
  have hiB : Integrable B₀ μ := (integrable_noise_test_powers hf hfd m v x).1
  have hiK : Integrable K μ := ((hiH.add (hiG.const_mul 2)).add hiQ).add hiB
  have hfirst (t : ℝ) : A₁ t = m * S t :=
    ParamChain.movingLogInput_first_source hF M V q u x t
  have hsecond (t : ℝ) : A₂ t + Aₐ t - 2 * η * A₁ t =
      m * K t + m * (ν - η ^ 2) * f (x + t • v) := by
    have HC := ParamChain.movingLogInput_second_source hF M V q u a x t
    convert HC using 1
    dsimp only [K, H₀, G₀, Q₀, B₀, h, g, f, m, η, ν, v, w, b]
    ring
  have hKm : (∫ t, K t ∂μ) =
      tiltedAverage m v f h x + 2 * tiltedAverage m v f (mixedDirectionSource m v w f g) x +
        noiseMean m v f x (fun t => t ^ 2 * fderiv ℝ (fderiv ℝ f) (x + t • v) w w) +
        tiltedAverage m v f (directionSource m v b f) x := by
    change (∫ t, H₀ t + 2 * G₀ t + Q₀ t + B₀ t ∂μ) = _
    rw [integral_add (f := fun t => H₀ t + 2 * G₀ t + Q₀ t) (g := B₀)
        ((hiH.add (hiG.const_mul 2)).add hiQ) hiB,
      integral_add (f := fun t => H₀ t + 2 * G₀ t) (g := Q₀)
        (hiH.add (hiG.const_mul 2)) hiQ,
      integral_add (f := H₀) (g := fun t => 2 * G₀ t) hiH (hiG.const_mul 2), integral_const_mul]
    rw [show (∫ t, G₀ t ∂μ) = tiltedAverage m v f (mixedDirectionSource m v w f g) x from
        noise_mixedDirectionSource hf hg m v w x,
      show (∫ t, B₀ t ∂μ) = tiltedAverage m v f (directionSource m v b f) x from
        noise_directionSource hf (by norm_num) m v b x]
    rfl
  have hAlg := normalized_second_moments (T := vectorStep m v f x) hm hiu.1 hiu.2 hia hS hiK
    (hfm.integrable (by norm_num)) hfirst hsecond
  have hZvalue : Z (q,x) = m * vectorStep m v f x := by
    dsimp only [Z, G, I, ParamChain.movingLogInput, m, v, f]
    simp only [vectorStep, gaussianStep, Real.exp_ne_zero, ite_false, one_ne_zero,
      positiveGaussianLogStep, one_mul, div_one]
    field_simp
  have hActual : (fun t => vectorStep (Real.exp (M (p t))) (V (p t)) (fun y => F (p t,y)) x) =
      fun t => Real.exp (-M (p t)) * Z (p t,x) := by
    funext t
    dsimp only [Z, G, I, ParamChain.movingLogInput]
    simp only [vectorStep, gaussianStep, Real.exp_ne_zero, ite_false, one_ne_zero,
      positiveGaussianLogStep, one_mul, Real.exp_neg, div_eq_mul_inv]
    ring
  have hNorm := ParamChain.second_normalized_logStep hI M hp x
  change deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
    (fun y => F (p t,y)) x)) k = secondVariationStep m v f g h (m * η) (m * (η ^ 2 + ν)) w b x
  rw [hActual, hNorm, hlaw]
  change Real.exp (-M q) * ((∫ t, A₂ t + A₁ t ^ 2 ∂μ) - (∫ t, A₁ t ∂μ) ^ 2 +
    (∫ t, Aₐ t ∂μ) - 2 * η * (∫ t, A₁ t ∂μ) + (η ^ 2 - ν) * Z (q,x)) = _
  rw [hZvalue, Real.exp_neg]
  change m⁻¹ * ((∫ t, A₂ t + A₁ t ^ 2 ∂μ) - (∫ t, A₁ t ∂μ) ^ 2 +
    (∫ t, Aₐ t ∂μ) - 2 * η * (∫ t, A₁ t ∂μ) + (η ^ 2 - ν) * (m * vectorStep m v f x)) = _
  rw [hAlg, hKm, ← secondScoreVariance_eq_variance hf hg m η v w x]
  unfold secondVariationStep
  have hratio : m * η / m = η := by field_simp [hm]
  rw [hratio, massSensitivity_eq hf (by norm_num) hm]
  change _ + _ + (ν - η ^ 2) * (tiltedAverage m v f f x - vectorStep m v f x) = _
  field_simp [hm]
  ring

theorem qBoundedJets_second_deriv_exponential_movingStep {F : P × E → ℝ}
    (hF : ParamRegular F) (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) {B A H : ℝ}
    (hf : QPotential 3 B (fun y => F (p k,y)))
    (hg : QBoundedJets 3 A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hh : QBoundedJets 1 H (fun y =>
      fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0)))
    (hm : Real.exp (M (p k)) ≤ 1) (hv : ‖V (p k)‖ ≤ 1)
    (hsmall : B * ‖V (p k)‖ ^ 2 ≤ 1 / 2) :
    QBoundedJets 1
      (secondVariationBound B A H (Real.exp (M (p k)))
        (Real.exp (M (p k)) * M (deriv p k))
        (Real.exp (M (p k)) * ((M (deriv p k)) ^ 2 + M (deriv (deriv p) k)))
        (V (p k)) (V (deriv p k)) (V (deriv (deriv p) k)))
      (fun x => deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
        (fun y => F (p t,y)) x)) k) := by
  have heq : (fun x => deriv (deriv (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
      (fun y => F (p t,y)) x)) k) =
      secondVariationStep (Real.exp (M (p k))) (V (p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0))
        (Real.exp (M (p k)) * M (deriv p k))
        (Real.exp (M (p k)) * ((M (deriv p k)) ^ 2 + M (deriv (deriv p) k)))
        (V (deriv p k)) (V (deriv (deriv p) k)) :=
    funext (second_deriv_exponential_movingStep hF M V hp hf hg hh)
  rw [heq]
  exact qBoundedJets_secondVariationStep hf hg hh ⟨Real.exp_pos _, hm⟩ _ _ _ _ _ hv hsmall

end ActualSecondVariation

end SKBarriers2.StepCalculus

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def secondVariationSource (A dm ddm : ℝ) (v w b : E) : ℝ :=
  ‖v‖ ^ 2 * A ^ 2 + ‖v‖ * ‖w‖ * A + ‖v‖ ^ 2 * |dm| * A +
    ‖v‖ * ‖b‖ + ‖w‖ ^ 2 + ‖v‖ ^ 2 * |ddm| + ‖v‖ ^ 2 * |dm| ^ 2

theorem secondVariationBound_le_source {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E,
      secondVariationBound B A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b := by
  let T := |tiltedStabilityCoefficient 1 B|
  let D := |tiltedCoarseCoefficient 1 B * (1 + 2 * B)|
  let N := |noiseAverageCoefficient 1 2 B * B|
  let J := |directionSensitivityCoefficient 1 B|
  let Q := |potentialCovarianceCoefficient 1 B|
  let M := |massSensitivityJetCoefficient 0 B|
  have hT : 0 ≤ T := abs_nonneg _
  have hD : 0 ≤ D := abs_nonneg _
  have hN : 0 ≤ N := abs_nonneg _
  have hJ : 0 ≤ J := abs_nonneg _
  have hQ : 0 ≤ Q := abs_nonneg _
  have hM : 0 ≤ M := abs_nonneg _
  let K := 1 + T + 2 * D + N + J + 3 * Q * (1 + B ^ 2 * R ^ 2 + B ^ 2) + M * (1 + 2 * R)
  have hK : 0 < K := by dsimp only [K]; positivity
  have ht : T ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hd : 2 * D ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hn : N + 3 * Q * B ^ 2 ≤ K := by
    apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hj : J ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hq : 3 * Q ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hm0 : M ≤ K := by apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  have hmq : 3 * Q * B ^ 2 * R ^ 2 + 2 * M * R ≤ K := by
    apply sub_nonneg.mp; dsimp only [K]; ring_nf; positivity
  refine ⟨K, hK, ?_⟩
  intro A H m dm ddm hA hH hm hinv v w b
  have hratio : |dm / m| ≤ |dm| * R := by
    rw [abs_div, abs_of_pos hm, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (abs_nonneg dm)
  have hscore : A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖ ≤
      A * ‖v‖ + |dm| * R * B * ‖v‖ + B * ‖w‖ := by
    gcongr
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖)
    (by positivity : 0 ≤ A * ‖v‖ + |dm| * R * B * ‖v‖ + B * ‖w‖)).mpr hscore
  have hthree : (A * ‖v‖ + |dm| * R * B * ‖v‖ + B * ‖w‖) ^ 2 ≤
      3 * ((A * ‖v‖) ^ 2 + (|dm| * R * B * ‖v‖) ^ 2 + (B * ‖w‖) ^ 2) := by
    nlinarith [sq_nonneg (A * ‖v‖ - |dm| * R * B * ‖v‖),
      sq_nonneg (A * ‖v‖ - B * ‖w‖), sq_nonneg (|dm| * R * B * ‖v‖ - B * ‖w‖)]
  have hvar : Q * (A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖) ^ 2 ≤
      3 * Q * ‖v‖ ^ 2 * A ^ 2 + 3 * Q * B ^ 2 * R ^ 2 * ‖v‖ ^ 2 * dm ^ 2 +
        3 * Q * B ^ 2 * ‖w‖ ^ 2 := by
    have H' := mul_le_mul_of_nonneg_left (hsq.trans hthree) hQ
    simp only [mul_pow, sq_abs] at H'
    nlinarith only [H']
  have hmassAbs : |ddm - 2 * dm ^ 2 / m| ≤ |ddm| + 2 * dm ^ 2 * R := by
    apply (abs_sub _ _).trans
    apply add_le_add (le_refl |ddm|)
    rw [abs_div, abs_of_pos hm, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg dm), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  have hmass := mul_le_mul_of_nonneg_left hmassAbs
    (show 0 ≤ M * ‖v‖ ^ 2 by positivity)
  have hraw : secondVariationBound B A H m dm ddm v w b ≤
      H + T * H * ‖v‖ ^ 2 + 2 * D * A * ‖v‖ * ‖w‖ + N * ‖w‖ ^ 2 +
        J * ‖v‖ * ‖b‖ + Q * (A * ‖v‖ + |dm / m| * B * ‖v‖ + B * ‖w‖) ^ 2 +
        M * ‖v‖ ^ 2 * |ddm - 2 * dm ^ 2 / m| := by
    dsimp only [secondVariationBound, T, D, N, J, Q, M]
    gcongr <;> exact le_abs_self _
  calc
    secondVariationBound B A H m dm ddm v w b ≤
        H + T * H * ‖v‖ ^ 2 + (2 * D) * (A * ‖v‖ * ‖w‖) +
          (N + 3 * Q * B ^ 2) * ‖w‖ ^ 2 + J * (‖v‖ * ‖b‖) +
          (3 * Q) * (‖v‖ ^ 2 * A ^ 2) + M * (‖v‖ ^ 2 * |ddm|) +
          (3 * Q * B ^ 2 * R ^ 2 + 2 * M * R) * (‖v‖ ^ 2 * dm ^ 2) := by
      nlinarith only [hraw, hvar, hmass]
    _ ≤ H + K * H * ‖v‖ ^ 2 + K * (A * ‖v‖ * ‖w‖) + K * ‖w‖ ^ 2 +
        K * (‖v‖ * ‖b‖) + K * (‖v‖ ^ 2 * A ^ 2) + K * (‖v‖ ^ 2 * |ddm|) +
        K * (‖v‖ ^ 2 * dm ^ 2) := by
      gcongr
    _ ≤ (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b := by
      dsimp only [secondVariationSource]
      rw [sq_abs]
      have hextra : 0 ≤ K * ‖v‖ ^ 2 * |dm| * A := by positivity
      nlinarith only [hextra]

section SecondChain

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def exponentialSecondMajorant (K : ℝ) (q u a : P) :
    List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)) → ℝ
  | [] => 0
  | c :: ps => (1 + K * ‖c.2 q‖ ^ 2) * exponentialSecondMajorant K q u a ps +
      K * secondVariationSource (firstVariationMajorant K q u ps)
        (Real.exp (c.1 q) * c.1 u)
        (Real.exp (c.1 q) * ((c.1 u) ^ 2 + c.1 a)) (c.2 q) (c.2 u) (c.2 a)

theorem exponentialSecondMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (q u a : P)
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    0 ≤ exponentialSecondMajorant K q u a ps := by
  induction ps with
  | nil => exact le_rfl
  | cons c ps ih =>
    have ha := firstVariationMajorant_nonneg hK q u ps
    dsimp only [exponentialSecondMajorant, secondVariationSource]
    positivity

theorem qBoundedJets_second_exponentialChain
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B R K : ℝ} {f : E → ℝ}
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient 3 B ≤ K)
    (hMass : massSensitivityJetCoefficient 2 B ≤ K)
    (hDir : directionSensitivityCoefficient 3 B ≤ K)
    (hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E, secondVariationBound B A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b)
    (hpotential : ∀ front tail, ps = front ++ tail →
      QPotential 5 B (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f))
    (hgeometry : ∀ c ∈ ps, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      B * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (c.1 (p k)))⁻¹ ≤ R) :
    QBoundedJets 1
      (exponentialSecondMajorant K (p k) (deriv p k) (deriv (deriv p) k) ps)
      (fun x => deriv (deriv (fun t => vectorIncrementChain
        (ParamChain.exponentialSteps ps (p t)) f x)) k) := by
  have hf : QPotential 5 B f := hpotential ps [] (by rw [List.append_nil])
  have hp1 := (hp.differentiableAt (by norm_num)).hasDerivAt
  induction ps with
  | nil =>
    simp only [ParamChain.exponentialSteps, List.map_nil, vectorIncrementChain, deriv_const',
      exponentialSecondMajorant]
    refine ⟨le_rfl, contDiff_const, ?_⟩
    intro j hj x
    simp
  | cons c ps ih =>
    have hpotTail : ∀ front tail, ps = front ++ tail →
        QPotential 5 B (vectorIncrementChain (ParamChain.exponentialSteps tail (p k)) f) := by
      intro front tail hsplit
      apply hpotential (c :: front) tail
      simpa only [List.cons_append, List.cons.injEq, true_and] using hsplit
    have hgeoTail : ∀ d ∈ ps, Real.exp (d.1 (p k)) ≤ 1 ∧ ‖d.2 (p k)‖ ≤ 1 ∧
        B * ‖d.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (d.1 (p k)))⁻¹ ≤ R :=
      fun d hd => hgeometry d (List.mem_cons_of_mem c hd)
    have hinner := ih hpotTail hgeoTail
    have hfirst := qBoundedJets_first_exponentialChain (n := 2) ps hp1 hK hTilt hMass hDir
      hpotTail (fun d hd => ⟨(hgeoTail d hd).1, (hgeoTail d hd).2.1, (hgeoTail d hd).2.2.1⟩)
    let F : P × E → ℝ := ParamChain.exponentialChain ps (fun z => f z.2)
    have hF : ParamRegular F := ParamChain.regular_exponentialChain ps
      (ParamChain.regular_fixedTerminal hf (by norm_num) P)
    have hGid : (fun y => fderiv ℝ F (p k,y) (deriv p k,0)) =
        fun y => deriv (fun t => vectorIncrementChain (ParamChain.exponentialSteps ps (p t)) f y) k := by
      funext y
      exact (((hF.1.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
        (hp1.prodMk (hasDerivAt_const k y))).deriv).symm
    have hHid : (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0)) =
        fun y => deriv (deriv (fun t => vectorIncrementChain
          (ParamChain.exponentialSteps ps (p t)) f y)) k := by
      funext y
      exact (ParamChain.second_parameter_curve hF.1 hp y).symm
    have hG : QBoundedJets 3 (firstVariationMajorant K (p k) (deriv p k) ps)
        (fun y => fderiv ℝ F (p k,y) (deriv p k,0)) := by rw [hGid]; exact hfirst
    have hH : QBoundedJets 1 (exponentialSecondMajorant K (p k) (deriv p k) (deriv (deriv p) k) ps)
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0)) := by rw [hHid]; exact hinner
    have hgeo := hgeometry c (List.mem_cons_self ..)
    have hstep := qBoundedJets_second_deriv_exponential_movingStep hF c.1 c.2 hp
      ((hpotential [c] ps rfl).of_le (by norm_num : 3 ≤ 5)) hG hH
      hgeo.1 hgeo.2.1 hgeo.2.2.1
    apply hstep.mono
    exact hsource _ _ _ _ _ hG.nonneg hH.nonneg (Real.exp_pos _) hgeo.2.2.2 _ _ _

end SecondChain

end SKBarriers2.StepCalculus
