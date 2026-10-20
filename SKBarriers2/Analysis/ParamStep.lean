module

public import SKBarriers2.Analysis.StepStability
public import SKBarriers2.Analysis.HigherStepCalculus
public import OAI.Probability.SKBarriers.Calculus.ParameterStepDerivative
public import OAI.Probability.SKBarriers.Scalar.DslopeLipschitz
public import OAI.Probability.SKBarriers.Calculus.ParameterBilinear
public import OAI.Probability.SKBarriers.Calculus.ParameterProduct
public import OAI.Probability.SKBarriers.Calculus.ParameterRecursion
public import OAI.Probability.SKBarriers.Gaussian.GaussianMassStability

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open OAI.SK.Analytic

namespace SKBarriers2.QBoundedJets

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem integral {n : ℕ} {F : ℝ → X → Y} {b : ℝ → ℝ} (μ : Measure ℝ)
    (hF : ContDiff ℝ n (Function.uncurry F))
    (hjets : ∀ t, QBoundedJets n (b t) (F t)) (hb : Integrable b μ) :
    QBoundedJets n (∫ t, b t ∂μ) (fun x => ∫ t, F t x ∂μ) := by
  have hnonneg : 0 ≤ ∫ t, b t ∂μ := integral_nonneg (fun t => (hjets t).nonneg)
  have hInt (x : X) : Integrable (fun t => F t x) μ := by
    apply hb.mono' (hF.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    exact ae_of_all _ (fun t => (hjets t).norm_le x)
  have h0 (x : X) : ‖∫ t, F t x ∂μ‖ ≤ ∫ t, b t ∂μ :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) hb
        (ae_of_all _ (fun t => (hjets t).norm_le x)))
  induction n generalizing Y with
  | zero =>
    refine ⟨hnonneg, contDiff_zero.mpr ?_, ?_⟩
    · apply continuous_of_dominated (bound := b)
      · intro x
        exact (hInt x).aestronglyMeasurable
      · intro x
        exact ae_of_all _ (fun t => (hjets t).norm_le x)
      · exact hb
      · exact ae_of_all _ (fun t => (hjets t).smooth.continuous)
    · intro j hj x
      have hj0 : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero] using h0 x
  | succ n ih =>
    let D : ℝ → X → X →L[ℝ] Y := fun t x => fderiv ℝ (F t) x
    have hD : ContDiff ℝ n (Function.uncurry D) := by
      have hFam : ContDiff ℝ (n + 1) (fun p : (ℝ × X) × X => F p.1.1 p.2) :=
        hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact hFam.fderiv contDiff_snd (by simp)
    have hdjets (t : ℝ) : QBoundedJets n (b t) (D t) := (hjets t).derivativeJets
    have hDInt (x : X) : Integrable (fun t => D t x) μ :=
      hb.mono' (hD.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
        (ae_of_all _ (fun t => (hdjets t).norm_le x))
    have hD0 (x : X) : ‖∫ t, D t x ∂μ‖ ≤ ∫ t, b t ∂μ :=
      (norm_integral_le_integral_norm _).trans
        (integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) hb
          (ae_of_all _ (fun t => (hdjets t).norm_le x)))
    have hAvg := ih hD hdjets hDInt hD0
    have hder (x : X) : HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, D t x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ) (bound := b)
        (F' := fun y t => D t y)
      · exact univ_mem
      · exact Eventually.of_forall (fun y => (hInt y).aestronglyMeasurable)
      · exact hInt x
      · exact (hD.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      · exact ae_of_all _ (fun t y _ => (hdjets t).norm_le y)
      · exact hb
      · exact ae_of_all _ (fun t y _ => ((hjets t).smooth.differentiable (by simp) y).hasFDerivAt)
    refine ⟨hnonneg, contDiff_succ_iff_hasFDerivAt.mpr ⟨_, hAvg.smooth, hder⟩, ?_⟩
    intro j hj x
    cases j with
    | zero => simpa only [norm_iteratedFDeriv_zero] using h0 x
    | succ j =>
      rw [← norm_iteratedFDeriv_fderiv,
        show fderiv ℝ (fun y => ∫ t, F t y ∂μ) = fun y => ∫ t, D t y ∂μ from
          funext (fun y => (hder y).fderiv)]
      exact hAvg.bound j (by omega) x

end SKBarriers2.QBoundedJets

namespace SKBarriers2.QPotential

local notation "E" => (Fin 3 → ℝ)

theorem positiveJet {s j : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (s + j) B f) (hj : 1 ≤ j) :
    QBoundedJets s B (iteratedFDeriv ℝ j f) := by
  cases j with
  | zero => omega
  | succ j =>
    have hf' : QPotential ((s + j) + 1) B f := by simpa only [Nat.add_assoc] using hf
    have H := (hf'.derivativeJets.jet j).isometryEquiv_comp
      (continuousMultilinearCurryRightEquiv' ℝ j E ℝ).symm
    convert H using 1
    funext x
    exact iteratedFDeriv_succ_eq_comp_right

theorem increment {n : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 1) B f) (d : E) :
    QBoundedJets n (B * ‖d‖) (fun x => f (x + d) - f x) := by
  refine ⟨mul_nonneg hf.nonneg (norm_nonneg d),
    (hf.smooth.comp (contDiff_id.add contDiff_const)).sub hf.smooth |>.of_le (by norm_cast; omega), ?_⟩
  intro j hj x
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have H := (hf.lipschitzWith (by omega)).norm_sub_le (x + d) x
    change ‖f (x + d) - f x‖ ≤ B * ‖x + d - x‖ at H
    simpa only [add_sub_cancel_left] using H
  | succ j =>
    have hfd : ContDiff ℝ (j + 1) f := hf.smooth.of_le (by exact_mod_cast (hj.trans (Nat.le_succ n)))
    have hft : ContDiff ℝ (j + 1) (fun x : E => f (x + d)) :=
      hfd.comp (contDiff_id.add contDiff_const)
    change ‖iteratedFDeriv ℝ (j + 1) ((fun y : E => f (y + d)) - f) x‖ ≤ _
    rw [iteratedFDeriv_sub hft hfd]
    change ‖iteratedFDeriv ℝ (j + 1) (fun y => f (y + d)) x - iteratedFDeriv ℝ (j + 1) f x‖ ≤ _
    rw [iteratedFDeriv_comp_add_right]
    have hJ : QBoundedJets 1 B (iteratedFDeriv ℝ (j + 1) f) :=
      (hf.of_le (by omega : 1 + (j + 1) ≤ n + 1)).positiveJet (by omega)
    have H := hJ.lipschitzWith.norm_sub_le (x + d) x
    change ‖iteratedFDeriv ℝ (j + 1) f (x + d) - iteratedFDeriv ℝ (j + 1) f x‖ ≤
      B * ‖x + d - x‖ at H
    simpa only [add_sub_cancel_left] using H

end SKBarriers2.QPotential

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)
variable {r n : ℕ} {B : ℝ} {f : E → ℝ}

local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def directionSource (m : ℝ) (v w : E) (f : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x v w + m * (fderiv ℝ f x v * fderiv ℝ f x w)

theorem qBoundedJets_directionSource (hf : QPotential (n + 2) B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v w : E) :
    QBoundedJets n ((B + (2 : ℝ) ^ n * B ^ 2) * ‖v‖ * ‖w‖)
      (directionSource m v w f) := by
  have hfirst := hf.derivativeJets
  have hsecond := hfirst.derivativeJets
  have hH := (hsecond.apply_const v).apply_const w
  have hV := (hfirst.of_le (by omega : n ≤ n + 1)).apply_const v
  have hW := (hfirst.of_le (by omega : n ≤ n + 1)).apply_const w
  have hP := (hV.mul hW).const_smul m
  have h := hH.add hP
  apply h.mono
  rw [abs_of_nonneg hm.1]
  calc
    _ ≤ B * ‖v‖ * ‖w‖ + (2 : ℝ) ^ n * (B * ‖v‖) * (B * ‖w‖) := by
      exact add_le_add_right (mul_le_of_le_one_left
        (show 0 ≤ (2 : ℝ) ^ n * (B * ‖v‖) * (B * ‖w‖) by positivity [hf.nonneg]) hm.2) _
    _ = _ := by ring

theorem noise_directionSource (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v w x : E) :
    noiseMean m v f x (fun t => t * fderiv ℝ f (x + t • v) w) =
      tiltedAverage m v f (directionSource m v w f) x := by
  have hD := (hf.of_le hr).directional w
  have hd (t : ℝ) : HasDerivAt (fun a : ℝ => fderiv ℝ f (x + a • v) w)
      (fderiv ℝ (fderiv ℝ f) (x + t • v) v w) t := by
    have hline : HasDerivAt (fun a : ℝ => x + a • v) v t := by
      convert! (((hasDerivAt_id t).smul_const v).const_add x) using 1
      simp only [one_smul]
    exact (((hf.boundedDerivs hr).1.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline |>.clm_apply (hasDerivAt_const t w)
      |>.congr_deriv (by simp only [map_zero, add_zero])
  have hcont : Continuous (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • v) v w) :=
    ((((hf.boundedDerivs hr).1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      (by norm_num)).comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const |>.clm_apply continuous_const
  have hG : HasExpGrowth (fun t : ℝ => fderiv ℝ f (x + t • v) w) :=
    HasExpGrowth.of_bounded (by positivity [hf.nonneg]) (fun t => hf.directional_le (by omega) _ _)
  have hG' : HasExpGrowth (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • v) v w) :=
    HasExpGrowth.of_bounded (by positivity [hf.nonneg]) (fun t => hf.second_directional_le hr _ _ _)
  rw [tilted_integration_by_parts hf hr m v x hd hcont hG hG']
  have hH := qBoundedJets_directionSource (hf.of_le hr) (m := 0) (by constructor <;> norm_num) v w
  have hI : Integrable (fun t : ℝ => fderiv ℝ (fderiv ℝ f) (x + t • v) v w) (stepLaw m v f x) := by
    simpa only [directionSource, zero_mul, add_zero] using integrable_tilted_shift hf hr hH m v x
  have hP := ((qBoundedJets_iff_qBddSmooth.mpr hD).of_le (by omega : 0 ≤ 1)).mul
    ((qBoundedJets_iff_qBddSmooth.mpr ((hf.of_le hr).directional v)).of_le (by omega : 0 ≤ 1))
  have hIP := integrable_tilted_shift hf hr hP m v x
  unfold tiltedAverage directionSource noiseMean
  rw [← integral_const_mul, ← integral_add hI (hIP.const_mul m)]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

def directionSensitivityCoefficient (n : ℕ) (B : ℝ) : ℝ :=
  tiltedCoarseCoefficient n B * (B + (2 : ℝ) ^ n * B ^ 2)

theorem qBoundedJets_directionSensitivity (hf : QPotential (n + 2) B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v w : E) :
    QBoundedJets n (directionSensitivityCoefficient n B * ‖v‖ * ‖w‖)
      (tiltedAverage m v f (directionSource m v w f)) := by
  have h := qBoundedJets_tiltedAverage_coarse n hf (by omega) (by omega)
    (qBoundedJets_directionSource hf hm v w) hm v
  convert h using 1
  dsimp only [directionSensitivityCoefficient]
  ring

theorem differentiable_mass_step (hf : QPotential r B f) (hr : 2 ≤ r) (v x : E) :
    Differentiable ℝ (fun m : ℝ => vectorStep m v f x) := by
  intro m
  by_cases hm : m = 0
  · subst m
    exact (gaussianStep_hasDerivAt_mass_zero
      ((hf.boundedDerivs hr).compCLM (vectorTranslation v)) x).differentiableAt
  · exact (hasDerivAt_mass hf hr hm v x).differentiableAt

theorem abs_deriv_mass_step_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v x : E)
    (hsmall : B * ‖v‖ ^ 2 ≤ 1 / 2) :
    |deriv (fun a : ℝ => vectorStep a v f x) m| ≤ 2 * B ^ 2 * ‖v‖ ^ 2 := by
  let hb := (hf.boundedDerivs hr).compCLM (vectorTranslation v)
  have hAn (a : ℝ) : AnalyticAt ℝ
      (cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1)) a :=
    analyticAt_cgf (hb.mem_interior_integrableExpSet_section x a)
  have hVar (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      |iteratedDeriv 2 (cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1)) a| ≤
        2 * B ^ 2 * ‖v‖ ^ 2 := by
    have hvareq := variance_tilted_mul (hb.mem_interior_integrableExpSet_section x a)
    change variance (fun t : ℝ => f (x + t • v)) (stepLaw a v f x) =
      iteratedDeriv 2 (cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1)) a at hvareq
    rw [← hvareq, abs_of_nonneg (variance_nonneg _ _)]
    have hcurv : a * (B * ‖v‖ ^ 2) ≤ 1 / 2 :=
      (mul_le_of_le_one_left (by positivity [hf.nonneg]) ha.2).trans hsmall
    have H := spatial_variance_le hf hr ha.1 v x (by linarith)
      (hf.lipschitzWith (by omega))
    change variance (fun t : ℝ => f (x + t • v)) (stepLaw a v f x) ≤
      B ^ 2 * ‖v‖ ^ 2 / (1 - a * (B * ‖v‖ ^ 2)) at H
    have hden : 0 < 1 - a * (B * ‖v‖ ^ 2) := by linarith
    exact H.trans ((div_le_iff₀ hden).mpr (by
      nlinarith [mul_nonneg (sq_nonneg (B * ‖v‖)) (show 0 ≤ 1 / 2 - a * (B * ‖v‖ ^ 2) by linarith)]))
  have H := dslope_deriv_bound hAn (by positivity) hVar hm
  have heq : (fun a : ℝ => vectorStep a v f x) =
      dslope (cgf (fun t : ℝ => f (x + t • v)) (gaussianReal 0 1)) 0 :=
    gaussianStep_mass_eq_dslope hb x
  rw [heq]
  exact H.2

def gaussianExpMoment (b : ℝ) : ℝ := ∫ t : ℝ, Real.exp (b * |t|) ∂gaussianReal 0 1

theorem gaussianExpMoment_pos (b : ℝ) : 0 < gaussianExpMoment b :=
  integral_exp_pos (integrable_exp_mul_abs_gaussian b)

def anchorJetCoefficient (n : ℕ) (B : ℝ) : ℝ := (n.factorial : ℝ) * (1 + B) ^ n

def anchorPartitionJetBound (n : ℕ) (B : ℝ) : ℝ :=
  anchorJetCoefficient n B * gaussianExpMoment (B + n)

def anchorPartition (m : ℝ) (v : E) (f : E → ℝ) (x : E) : ℝ :=
  ∫ t : ℝ, Real.exp (m * (f (x + t • v) - f x)) ∂gaussianReal 0 1

private theorem abs_le_exp_abs (t : ℝ) : |t| ≤ Real.exp |t| := by
  linarith [Real.add_one_le_exp |t|]

private theorem exp_increment_jets (hf : QPotential (n + 1) B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1) (t : ℝ) :
    QBoundedJets n (anchorJetCoefficient n B * Real.exp ((B + n) * |t|))
      (fun x => Real.exp (m * (f (x + t • v) - f x))) := by
  have hB : 0 ≤ B := hf.nonneg
  have hinc := (hf.increment (t • v)).const_smul m
  have hi : QBoundedJets n (B * |t|) (fun x => m * (f (x + t • v) - f x)) := by
    apply hinc.mono
    rw [abs_of_nonneg hm.1, norm_smul, Real.norm_eq_abs]
    calc
      m * (B * (|t| * ‖v‖)) ≤ B * (|t| * ‖v‖) := mul_le_of_le_one_left (by positivity) hm.2
      _ ≤ B * |t| := by nlinarith [mul_nonneg hB (abs_nonneg t)]
  apply hi.exp.mono
  have hpow : (1 + B * |t|) ^ n ≤ (1 + B) ^ n * Real.exp ((n : ℝ) * |t|) := by
    have hbase : 1 + B * |t| ≤ (1 + B) * Real.exp |t| := by
      have he : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
      nlinarith [mul_le_mul_of_nonneg_left (abs_le_exp_abs t) hB]
    have H := pow_le_pow_left₀ (by positivity) hbase n
    rw [mul_pow, ← Real.exp_nat_mul] at H
    exact H
  calc
    (n.factorial : ℝ) * Real.exp (B * |t|) * (1 + B * |t|) ^ n ≤
        (n.factorial : ℝ) * Real.exp (B * |t|) * ((1 + B) ^ n * Real.exp ((n : ℝ) * |t|)) := by
      gcongr
    _ = _ := by
      dsimp only [anchorJetCoefficient]
      rw [add_mul, Real.exp_add]
      ring

theorem qBoundedJets_anchorPartition (hf : QPotential (n + 1) B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets n (anchorPartitionJetBound n B) (anchorPartition m v f) := by
  have hFam : ContDiff ℝ n (fun z : ℝ × E =>
      Real.exp (m * (f (z.2 + z.1 • v) - f z.2))) :=
    ((contDiff_const.mul ((hf.smooth.comp (contDiff_snd.add
      (contDiff_fst.smul contDiff_const))).sub (hf.smooth.comp contDiff_snd))).exp).of_le
        (by exact_mod_cast Nat.le_succ n)
  have h := QBoundedJets.integral (gaussianReal 0 1) hFam
    (exp_increment_jets hf hm v hv)
    ((integrable_exp_mul_abs_gaussian (B + n)).const_mul (anchorJetCoefficient n B))
  change QBoundedJets n (anchorJetCoefficient n B * gaussianExpMoment (B + n))
    (fun x => ∫ t : ℝ, Real.exp (m * (f (x + t • v) - f x)) ∂gaussianReal 0 1)
  simpa only [gaussianExpMoment, integral_const_mul] using h

theorem anchorPartition_lower (hf : QPotential r B f) (hr : 1 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1) (x : E) :
    gaussianExpMoment (-B) ≤ anchorPartition m v f x := by
  have hB : 0 ≤ B := hf.nonneg
  have hinc (t : ℝ) : |f (x + t • v) - f x| ≤ B * |t| := by
    have H := (hf.lipschitzWith hr).norm_sub_le (x + t • v) x
    change |f (x + t • v) - f x| ≤ B * ‖x + t • v - x‖ at H
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at H
    exact H.trans (by nlinarith [mul_nonneg hB (abs_nonneg t)])
  have hupper (t : ℝ) : |m * (f (x + t • v) - f x)| ≤ B * |t| := by
    rw [abs_mul, abs_of_nonneg hm.1]
    exact ((mul_le_of_le_one_left (abs_nonneg _) hm.2).trans (hinc t))
  have hI : Integrable (fun t : ℝ => Real.exp (m * (f (x + t • v) - f x)))
      (gaussianReal 0 1) := by
    apply (integrable_exp_mul_abs_gaussian B).mono'
      (Real.continuous_exp.comp (continuous_const.mul
        ((hf.smooth.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
          continuous_const))).aestronglyMeasurable
    exact ae_of_all _ (fun t => by
      change ‖Real.exp (m * (f (x + t • v) - f x))‖ ≤ Real.exp (B * |t|)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hupper t)))
  exact integral_mono (integrable_exp_mul_abs_gaussian (-B)) hI (fun t =>
    Real.exp_le_exp.mpr (by have H := (abs_le.mp (hupper t)).1; linarith))

def anchorLogJetBound (n : ℕ) (B : ℝ) : ℝ :=
  (n.factorial : ℝ) *
    (|Real.log (gaussianExpMoment (-B))| + |Real.log (anchorPartitionJetBound n B)| +
      (n.factorial : ℝ) * (1 + (gaussianExpMoment (-B))⁻¹) ^ (n + 1)) *
        (1 + anchorPartitionJetBound n B) ^ n

def anchorInverseJetBound (n : ℕ) (B : ℝ) : ℝ := exponentialJetBound n (anchorLogJetBound n B)

theorem qBoundedJets_inv_anchorPartition (hf : QPotential (n + 1) B f)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets n (anchorInverseJetBound n B) (fun x => (anchorPartition m v f x)⁻¹) := by
  have hZ := qBoundedJets_anchorPartition hf hm v hv
  have hD := gaussianExpMoment_pos (-B)
  have hpos (x : E) : 0 < anchorPartition m v f x :=
    hD.trans_le (anchorPartition_lower hf (by omega) hm v hv x)
  have hupper (x : E) : anchorPartition m v f x ≤ anchorPartitionJetBound n B :=
    (le_abs_self _).trans (hZ.norm_le x)
  have hlogs (x : E) : |Real.log (anchorPartition m v f x)| ≤
      |Real.log (gaussianExpMoment (-B))| + |Real.log (anchorPartitionJetBound n B)| := by
    have hlow := Real.log_le_log hD (anchorPartition_lower hf (by omega) hm v hv x)
    have hhigh := Real.log_le_log (hpos x) (hupper x)
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log (gaussianExpMoment (-B))),
        abs_nonneg (Real.log (anchorPartitionJetBound n B))]
    · linarith [le_abs_self (Real.log (anchorPartitionJetBound n B)),
        abs_nonneg (Real.log (gaussianExpMoment (-B)))]
  have hinv (x : E) : (anchorPartition m v f x)⁻¹ ≤ 1 + (gaussianExpMoment (-B))⁻¹ :=
    (inv_anti₀ hD (anchorPartition_lower hf (by omega) hm v hv x)).trans (by linarith)
  have hL : QBoundedJets n (anchorLogJetBound n B) (fun x => Real.log (anchorPartition m v f x)) :=
    hZ.log hpos (by positivity) hlogs (le_add_of_nonneg_right (inv_nonneg.mpr hD.le)) hinv
  have hN := (hL.const_smul (-1)).exp
  have heq : (fun x => (anchorPartition m v f x)⁻¹) =
      fun x => Real.exp ((-1 : ℝ) • Real.log (anchorPartition m v f x)) := by
    funext x
    rw [neg_one_smul, Real.exp_neg, Real.exp_log (hpos x)]
  rw [heq]
  simpa only [abs_neg, abs_one, one_mul, anchorInverseJetBound, exponentialJetBound] using hN

def noiseAverageCoefficient (n p : ℕ) (B : ℝ) : ℝ :=
  (2 : ℝ) ^ n * anchorInverseJetBound n B *
    ((2 : ℝ) ^ n * anchorJetCoefficient n B * gaussianExpMoment (B + n + p))

theorem noiseMean_anchor (m : ℝ) (v : E) (f : E → ℝ) (x : E) (g : ℝ → ℝ) :
    noiseMean m v f x g = (∫ t : ℝ, g t * Real.exp (m * (f (x + t • v) - f x))
      ∂gaussianReal 0 1) / anchorPartition m v f x := by
  have hlaw : stepLaw m v f x = (gaussianReal 0 1).tilted
      (fun t : ℝ => m * (f (x + t • v) - f x)) := by
    calc
      _ = (gaussianReal 0 1).tilted
          (fun t : ℝ => m * (f (x + t • v) - f x) + m * f x) := by
        apply tilted_congr
        exact ae_of_all _ (fun t => by change m * f (x + t • v) = _; ring)
      _ = _ := tilted_add_constant _ _ _
  rw [noiseMean, hlaw, integral_tilted_real_eq_div]
  rfl

theorem qBoundedJets_noiseMean_poly (hf : QPotential (n + 1) B f)
    {C : ℝ} (hC : 0 ≤ C) (p : ℕ) {g : E → ℝ → ℝ}
    (hg : ContDiff ℝ n (fun z : ℝ × E => g z.2 z.1))
    (hgj : ∀ t, QBoundedJets n (C * |t| ^ p) (fun x => g x t))
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets n (noiseAverageCoefficient n p B * C)
      (fun x => noiseMean m v f x (g x)) := by
  have hB : 0 ≤ B := hf.nonneg
  let A := anchorJetCoefficient n B
  have hA : 0 ≤ A := by dsimp only [A, anchorJetCoefficient]; positivity
  let b : ℝ → ℝ := fun t => (2 : ℝ) ^ n * C * A * Real.exp ((B + n + p) * |t|)
  have hNum (t : ℝ) : QBoundedJets n (b t)
      (fun x => g x t * Real.exp (m * (f (x + t • v) - f x))) := by
    apply ((hgj t).mul (exp_increment_jets hf hm v hv t)).mono
    have hp : |t| ^ p ≤ Real.exp ((p : ℝ) * |t|) := by
      have H := pow_le_pow_left₀ (abs_nonneg t) (abs_le_exp_abs t) p
      rwa [← Real.exp_nat_mul] at H
    calc
      (2 : ℝ) ^ n * (C * |t| ^ p) * (A * Real.exp ((B + n) * |t|)) ≤
          (2 : ℝ) ^ n * (C * Real.exp ((p : ℝ) * |t|)) * (A * Real.exp ((B + n) * |t|)) := by
        gcongr
      _ = b t := by
        dsimp only [b]
        simp only [add_mul, Real.exp_add]
        ring
  have hExp : ContDiff ℝ n (fun z : ℝ × E =>
      Real.exp (m * (f (z.2 + z.1 • v) - f z.2))) :=
    ((contDiff_const.mul ((hf.smooth.comp (contDiff_snd.add
      (contDiff_fst.smul contDiff_const))).sub (hf.smooth.comp contDiff_snd))).exp).of_le
        (by exact_mod_cast Nat.le_succ n)
  have hN := QBoundedJets.integral (gaussianReal 0 1) (hg.mul hExp) hNum
    ((integrable_exp_mul_abs_gaussian (B + n + p)).const_mul ((2 : ℝ) ^ n * C * A))
  have hP := hN.mul (qBoundedJets_inv_anchorPartition hf hm v hv)
  have hfun : (fun x => noiseMean m v f x (g x)) = fun x =>
      (∫ t : ℝ, g x t * Real.exp (m * (f (x + t • v) - f x)) ∂gaussianReal 0 1) *
        (anchorPartition m v f x)⁻¹ := by
    funext x
    rw [noiseMean_anchor, div_eq_mul_inv]
  rw [hfun]
  convert hP using 1
  dsimp only [b, noiseAverageCoefficient, gaussianExpMoment, A]
  rw [integral_const_mul]
  ring

def massVarianceCoefficient (n : ℕ) (B : ℝ) : ℝ :=
  noiseAverageCoefficient n 2 B * ((2 : ℝ) ^ n * B ^ 2) +
    (2 : ℝ) ^ n * (noiseAverageCoefficient n 1 B * B) ^ 2

theorem qBoundedJets_massVariance (hf : QPotential r B f) (hr : 2 ≤ r) (hn : n + 1 ≤ r)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : E) (hv : ‖v‖ ≤ 1) :
    QBoundedJets n (massVarianceCoefficient n B * ‖v‖ ^ 2)
      (fun x => variance (fun t : ℝ => f (x + t • v)) (stepLaw m v f x)) := by
  let a : E → ℝ → ℝ := fun x t => f (x + t • v) - f x
  have hf' : QPotential (n + 1) B f := hf.of_le hn
  have hB : 0 ≤ B := hf.nonneg
  have ha : ContDiff ℝ n (fun z : ℝ × E => a z.2 z.1) :=
    ((hf'.smooth.comp (contDiff_snd.add (contDiff_fst.smul contDiff_const))).sub
      (hf'.smooth.comp contDiff_snd)).of_le (by exact_mod_cast Nat.le_succ n)
  have haj (t : ℝ) : QBoundedJets n ((B * ‖v‖) * |t| ^ 1) (fun x => a x t) := by
    convert hf'.increment (t • v) using 1
    rw [norm_smul, Real.norm_eq_abs]
    ring
  have ha2j (t : ℝ) : QBoundedJets n
      (((2 : ℝ) ^ n * B ^ 2 * ‖v‖ ^ 2) * |t| ^ 2) (fun x => a x t * a x t) := by
    convert (haj t).mul (haj t) using 1
    ring
  have hM := qBoundedJets_noiseMean_poly hf' (by positivity) 1 ha haj hm v hv
  have hM2 := qBoundedJets_noiseMean_poly hf' (by positivity) 2 (ha.mul ha) ha2j hm v hv
  have hV := hM2.sub (hM.mul hM)
  have hfun : (fun x => variance (fun t : ℝ => f (x + t • v)) (stepLaw m v f x)) =
      fun x => noiseMean m v f x (fun t => a x t * a x t) -
        noiseMean m v f x (a x) * noiseMean m v f x (a x) := by
    funext x
    let _ := stepLaw_probability hf hr m v x
    have hmem : MemLp (fun t : ℝ => f (x + t • v)) 2 (stepLaw m v f x) :=
      memLp_tilted_mul (((hf.boundedDerivs hr).compCLM (vectorTranslation v)).mem_interior_integrableExpSet_section x m) 2
    have haMem := hmem.sub (memLp_const (f x))
    rw [← variance_sub_const hmem.aestronglyMeasurable (f x)]
    convert! variance_eq_sub haMem using 1
    simp only [a, noiseMean, Pi.sub_apply, pow_two, Pi.mul_apply]
  rw [hfun]
  convert hV using 1
  dsimp only [massVarianceCoefficient]
  ring

section ParameterRegularity

variable {P Y : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local instance : NormedAddCommGroup (P × Y →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (P × Y →L[ℝ] E) := inferInstance
local instance : NormedAddCommGroup (P × Y →L[ℝ] P × Y →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (P × Y →L[ℝ] P × Y →L[ℝ] E) := inferInstance

private theorem paramRegular_comp_potential (hf : QPotential r B f) (hr : 2 ≤ r)
    {g : P × Y → E} (hg : ContDiff ℝ 2 g)
    (hgl : ParamLinearGrowth (fun z => ‖g z‖))
    (hg₁ : ParamExpGrowth (fderiv ℝ g))
    (hg₂ : ParamExpGrowth (fderiv ℝ (fderiv ℝ g))) : ParamRegular (fun z => f (g z)) := by
  have hB : 0 ≤ B := hf.nonneg
  have hfl : ParamLinearGrowth (fun z => f (g z)) := by
    intro R
    obtain ⟨C, hC, hgb⟩ := hgl R
    refine ⟨|f 0| + B * C, by positivity, ?_⟩
    intro p e hp
    have hlip := (hf.lipschitzWith (by omega)).norm_sub_le (g (p,e)) 0
    change |f (g (p,e)) - f 0| ≤ B * ‖g (p,e) - 0‖ at hlip
    rw [sub_zero] at hlip
    have hb := hgb p e hp
    rw [abs_of_nonneg (norm_nonneg _)] at hb
    calc
      |f (g (p,e))| ≤ |f (g (p,e)) - f 0| + |f 0| := by
        simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add (f (g (p,e))) (f 0)
      _ ≤ B * (C * (1 + ‖e‖)) + |f 0| := add_le_add
        (hlip.trans (mul_le_mul_of_nonneg_left hb hB)) le_rfl
      _ ≤ (|f 0| + B * C) * (1 + ‖e‖) := by nlinarith [mul_nonneg (abs_nonneg (f 0)) (norm_nonneg e)]
  let C : P × Y → ℝ := fun z => |f (g z)| + B
  let D : P × Y → ℝ := fun z => 1 + ‖fderiv ℝ g z‖ + ‖fderiv ℝ (fderiv ℝ g) z‖
  have hC : ParamExpGrowth C := hfl.expGrowth.norm.add (ParamExpGrowth.of_bounded hB (fun _ => by simp [Real.norm_eq_abs, abs_of_nonneg hB]))
  have hD : ParamExpGrowth D := ((ParamExpGrowth.of_bounded zero_le_one (fun _ => by norm_num)).add hg₁.norm).add hg₂.norm
  have henv := hC.mul (hD.mul hD)
  have hjbound (j : ℕ) (hj : j ≤ 2) (z : P × Y) :
      ‖iteratedFDeriv ℝ j (fun w => f (g w)) z‖ ≤ 2 * (C z * (D z * D z)) := by
    have hC0 : 0 ≤ C z := by dsimp only [C]; positivity
    have hD1 : 1 ≤ D z := by dsimp only [D]; linarith [norm_nonneg (fderiv ℝ g z), norm_nonneg (fderiv ℝ (fderiv ℝ g) z)]
    have hDj : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i g z‖ ≤ D z ^ i := by
      intro i hi hij
      have hi2 : i ≤ 2 := hij.trans hj
      interval_cases i
      · rw [pow_one, norm_iteratedFDeriv_one]
        dsimp only [D]
        linarith [norm_nonneg (fderiv ℝ (fderiv ℝ g) z)]
      · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
        exact (show ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ D z by dsimp only [D]; linarith [norm_nonneg (fderiv ℝ g z)]).trans
          (le_self_pow₀ hD1 (by norm_num))
    have houter (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i f (g z)‖ ≤ C z := by
      cases i with
      | zero => simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using le_add_of_nonneg_right hB
      | succ i =>
          exact (hf.bound (i + 1) (by omega) (by omega) (g z)).trans
            (le_add_of_nonneg_left (abs_nonneg _))
    have h := norm_iteratedFDeriv_comp_le (hf.smooth.of_le (by exact_mod_cast hr)) hg
      (by exact_mod_cast hj) z (C := C z) (D := D z) houter hDj
    calc
      _ ≤ (j.factorial : ℝ) * C z * D z ^ j := h
      _ ≤ 2 * C z * D z ^ 2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hC0
        · exact pow_le_pow_right₀ hD1 hj
        · positivity
        · positivity
      _ = _ := by ring
  refine ⟨(hf.smooth.of_le (by exact_mod_cast hr)).comp hg, hfl, ?_, ?_⟩
  · apply henv.of_norm_le (K := 2) (by norm_num)
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [C, D]; positivity)]
    simpa only [norm_iteratedFDeriv_one] using hjbound 1 (by norm_num) z
  · apply henv.of_norm_le (K := 2) (by norm_num)
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [C, D]; positivity)]
    simpa only [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, norm_iteratedFDeriv_zero] using hjbound 2 le_rfl z

theorem paramRegular_affineBilinear (hf : QPotential r B f) (hr : 2 ≤ r)
    (A : Y →L[ℝ] E) (L : P →L[ℝ] Y →L[ℝ] E) :
    ParamRegular (fun z : P × Y => f (A z.2 + L z.1 z.2)) := by
  let S : P × Y →L[ℝ] E := A.comp (ContinuousLinearMap.snd ℝ P Y)
  let g : P × Y → E := fun z => A z.2 + L z.1 z.2
  have hgs : ContDiff ℝ 2 g := (A.contDiff.comp contDiff_snd).add L.isBoundedBilinearMap.contDiff
  have hd : fderiv ℝ g = fun z => S + L.deriv₂ z := by
    funext z
    exact (S.hasFDerivAt.add (L.isBoundedBilinearMap.hasFDerivAt z)).fderiv
  have hdd : fderiv ℝ (fderiv ℝ g) = fun _ => L.deriv₂ := by
    rw [hd]
    funext z
    exact (L.deriv₂.hasFDerivAt.const_add S).fderiv
  apply paramRegular_comp_potential hf hr hgs
  · intro R
    refine ⟨‖A‖ + ‖L‖ * max R 0, by positivity, ?_⟩
    intro p e hp
    rw [abs_of_nonneg (norm_nonneg _)]
    calc
      ‖g (p,e)‖ ≤ ‖A e‖ + ‖L p e‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖e‖ + (‖L‖ * ‖p‖) * ‖e‖ := add_le_add (A.le_opNorm e)
        (((L p).le_opNorm e).trans (mul_le_mul_of_nonneg_right (L.le_opNorm p) (norm_nonneg e)))
      _ ≤ (‖A‖ + ‖L‖ * max R 0) * (1 + ‖e‖) := by
        have hpr : ‖p‖ ≤ max R 0 := hp.trans (le_max_left _ _)
        calc
          _ ≤ ‖A‖ * ‖e‖ + (‖L‖ * max R 0) * ‖e‖ :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpr (norm_nonneg L)) (norm_nonneg e))
          _ = (‖A‖ + ‖L‖ * max R 0) * ‖e‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · rw [hd]
    exact (ParamExpGrowth.of_bounded (norm_nonneg S) (fun _ => le_rfl)).add
      (ParamExpGrowth.continuousLinearMap L.deriv₂)
  · rw [hdd]
    exact ParamExpGrowth.of_bounded (f := fun _ : P × Y => L.deriv₂)
      (norm_nonneg L.deriv₂) (fun _ => le_rfl)

end ParameterRegularity

section MassParameterRegularity

variable {P Y : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local instance : NormedAddCommGroup (P × Y →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × Y →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (P × Y →L[ℝ] P × Y →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × Y →L[ℝ] P × Y →L[ℝ] ℝ) := inferInstance

private theorem paramRegular_parameterCLM (M : P →L[ℝ] ℝ) :
    ParamRegular (fun z : P × Y => M z.1) := by
  let K : P × Y →L[ℝ] ℝ := M.comp (ContinuousLinearMap.fst ℝ P Y)
  have hd : fderiv ℝ (fun z : P × Y => M z.1) = fun _ => K :=
    funext (fun z => K.fderiv)
  refine ⟨K.contDiff, ?_, ?_, ?_⟩
  · intro R
    refine ⟨‖M‖ * max R 0, by positivity, ?_⟩
    intro p e hp
    calc
      |M p| ≤ ‖M‖ * ‖p‖ := M.le_opNorm p
      _ ≤ ‖M‖ * max R 0 := mul_le_mul_of_nonneg_left (hp.trans (le_max_left _ _)) (norm_nonneg M)
      _ ≤ (‖M‖ * max R 0) * (1 + ‖e‖) :=
        le_mul_of_one_le_right (by positivity) (by linarith [norm_nonneg e])
  · rw [hd]
    exact ParamExpGrowth.of_bounded (norm_nonneg K) (fun _ => le_rfl)
  · rw [hd]
    have hzero : fderiv ℝ (fun _ : P × Y => K) = fun _ => (0 : P × Y →L[ℝ] P × Y →L[ℝ] ℝ) :=
      funext (fun z => fderiv_const_apply K)
    rw [hzero]
    exact ParamExpGrowth.of_bounded (f := fun _ : P × Y => (0 : P × Y →L[ℝ] P × Y →L[ℝ] ℝ))
      (C := 0) le_rfl (fun _ => le_of_eq ContinuousLinearMap.opNorm_zero)

private theorem paramRegular_mul_parameterCLM {g : P × Y → ℝ}
    (hg : ParamRegular g) (M : P →L[ℝ] ℝ) :
    ParamRegular (fun z : P × Y => M z.1 * g z) := by
  have hprod := (paramRegular_parameterCLM (Y := Y) M).toSmooth.mul hg.toSmooth
  refine ⟨hprod.1, ?_, hprod.2.2⟩
  intro R
  obtain ⟨C, hC, hgb⟩ := hg.2.1 R
  refine ⟨(‖M‖ * max R 0) * C, by positivity, ?_⟩
  intro p e hp
  rw [abs_mul]
  have hMp : |M p| ≤ ‖M‖ * max R 0 :=
    (M.le_opNorm p).trans (mul_le_mul_of_nonneg_left (hp.trans (le_max_left _ _)) (norm_nonneg M))
  exact (mul_le_mul hMp (hgb p e hp) (abs_nonneg _) (by positivity)).trans_eq (by ring)

end MassParameterRegularity

theorem paramRegular_directionInput (hf : QPotential r B f) (hr : 2 ≤ r) :
    ParamRegular (fun z : E × (E × ℝ) => f (z.2.1 + z.2.2 • z.1)) := by
  let L : E →L[ℝ] (E × ℝ) →L[ℝ] E :=
    ((ContinuousLinearMap.compL ℝ (E × ℝ) ℝ E).flip (ContinuousLinearMap.snd ℝ E ℝ)).comp
      (ContinuousLinearMap.lsmul ℝ ℝ).flip
  exact paramRegular_affineBilinear hf hr (ContinuousLinearMap.fst ℝ E ℝ) L

theorem contDiff_direction_step (hf : QPotential r B f) (hr : 2 ≤ r) (m : ℝ) :
    ContDiff ℝ 2 (fun z : E × E => vectorStep m z.1 f z.2) :=
  (paramRegular_directionInput hf hr).gaussianStep m |>.1

theorem fderiv_direction_step_apply (hf : QPotential r B f) (hr : 2 ≤ r)
    (m : ℝ) (v w x : E) :
    fderiv ℝ (fun u : E => vectorStep m u f x) v w =
      tiltedAverage m v f (directionSource m v w f) x := by
  let H : E × (E × ℝ) → ℝ := fun z => f (z.2.1 + z.2.2 • z.1)
  have hreg := paramRegular_directionInput hf hr
  have hstep := (contDiff_direction_step hf hr m).differentiable (by norm_num)
  have hpair : HasFDerivAt (fun u : E => (u,x))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) v :=
    (hasFDerivAt_id v).prodMk (hasFDerivAt_const x v)
  have hpart := ((hstep (v,x)).hasFDerivAt.comp v
    hpair).fderiv
  change fderiv ℝ (fun u : E => vectorStep m u f x) v = _ at hpart
  rw [hpart]
  change fderiv ℝ (fun z : E × E => vectorStep m z.1 f z.2) (v,x) (w,0) = _
  have hparam := hreg.parameterDerivative_gaussianStep m (v,x) w
  change fderiv ℝ (fun z : E × E => vectorStep m z.1 f z.2) (v,x) (w,0) =
    noiseMean m v f x (fun t => fderiv ℝ H (v,(x,t)) (w,0)) at hparam
  rw [hparam]
  have hterminal (t : ℝ) : fderiv ℝ H (v,(x,t)) (w,0) =
      t * fderiv ℝ f (x + t • v) w := by
    have hfst : HasFDerivAt (fun z : E × (E × ℝ) => z.1)
        (ContinuousLinearMap.fst ℝ E (E × ℝ)) (v,(x,t)) := hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun z : E × (E × ℝ) => z.2)
        (ContinuousLinearMap.snd ℝ E (E × ℝ)) (v,(x,t)) := hasFDerivAt_snd
    have hG := hsnd.fst.add (hsnd.snd.smul hfst)
    have hd := (((hf.boundedDerivs hr).1.differentiable (by norm_num) (x + t • v)).hasFDerivAt.comp
      (v,(x,t)) hG).fderiv
    change fderiv ℝ H (v,(x,t)) = _ at hd
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', Prod.fst_zero, Prod.snd_zero,
      zero_add, zero_smul, add_zero, map_smul, smul_eq_mul]
  change (∫ t : ℝ, fderiv ℝ H (v,(x,t)) (w,0) ∂stepLaw m v f x) = _
  simp_rw [hterminal]
  exact noise_directionSource hf hr m v w x

theorem hasDerivAt_direction_curve (hf : QPotential r B f) (hr : 2 ≤ r)
    {v : ℝ → E} {k : ℝ} {w : E} (hv : HasDerivAt v w k) (m : ℝ) (x : E) :
    HasDerivAt (fun a : ℝ => vectorStep m (v a) f x)
      (tiltedAverage m (v k) f (directionSource m (v k) w f) x) k := by
  have hD : DifferentiableAt ℝ (fun u : E => vectorStep m u f x) (v k) :=
    ((contDiff_direction_step hf hr m).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by norm_num) (v k)
  have H := hD.hasFDerivAt.comp_hasDerivAt k hv
  rwa [fderiv_direction_step_apply hf hr m] at H

theorem qbddSmooth_deriv_direction_curve (hf : QPotential (n + 2) B f)
    {v : ℝ → E} {k : ℝ} {w : E} (hv : HasDerivAt v w k)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    QBddSmooth n (directionSensitivityCoefficient n B * ‖v k‖ * ‖w‖)
      (fun x => deriv (fun a : ℝ => vectorStep m (v a) f x) k) := by
  have heq : (fun x => deriv (fun a : ℝ => vectorStep m (v a) f x) k) =
      tiltedAverage m (v k) f (directionSource m (v k) w f) := by
    funext x
    exact (hasDerivAt_direction_curve hf (by omega) hv m x).deriv
  rw [heq]
  exact qBoundedJets_iff_qBddSmooth.mp (qBoundedJets_directionSensitivity hf hm (v k) w)

theorem contDiffAt_mass_direction_step (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ≠ 0) (v x : E) :
    ContDiffAt ℝ 2 (fun p : ℝ × E => vectorStep p.1 p.2 f x) (m,v) := by
  let L₀ : E →L[ℝ] (E × ℝ) →L[ℝ] E :=
    ((ContinuousLinearMap.compL ℝ (E × ℝ) ℝ E).flip (ContinuousLinearMap.snd ℝ E ℝ)).comp
      (ContinuousLinearMap.lsmul ℝ ℝ).flip
  let L : (ℝ × E) →L[ℝ] (E × ℝ) →L[ℝ] E := L₀.comp (ContinuousLinearMap.snd ℝ ℝ E)
  let H : (ℝ × E) × (E × ℝ) → ℝ := fun z => z.1.1 * f (z.2.1 + z.2.2 • z.1.2)
  have hreg : ParamRegular H := paramRegular_mul_parameterCLM
    (paramRegular_affineBilinear hf hr (ContinuousLinearMap.fst ℝ E ℝ) L)
      (ContinuousLinearMap.fst ℝ ℝ E)
  let Z : (ℝ × E) → ℝ := fun p => gaussianStep 1
    (fun z : ((ℝ × E) × E) × ℝ => H (z.1.1,(z.1.2,z.2))) (p,x)
  have hZ : ContDiff ℝ 2 Z := (hreg.gaussianStep 1).1.comp (contDiff_id.prodMk contDiff_const)
  have hQ : ContDiffAt ℝ 2 (fun p : ℝ × E => Z p / p.1) (m,v) := by
    have hp : ContDiffAt ℝ 2 (fun p : ℝ × E => p.1) (m,v) := contDiff_fst.contDiffAt
    convert! hZ.contDiffAt.mul (hp.inv (show (m,v).1 ≠ 0 from hm)) using 1
  have heq : (fun p : ℝ × E => vectorStep p.1 p.2 f x) =ᶠ[𝓝 (m,v)]
      (fun p : ℝ × E => Z p / p.1) := by
    have hne : ∀ᶠ p : ℝ × E in 𝓝 (m,v), p.1 ≠ 0 :=
      continuous_fst.continuousAt.eventually (eventually_ne_nhds hm)
    filter_upwards [hne] with p hp
    simp only [vectorStep, gaussianStep, hp, ite_false, one_ne_zero, positiveGaussianLogStep,
      Z, H, one_mul, div_one]
  exact hQ.congr_of_eventuallyEq heq

theorem differentiableAt_mass_direction_step (hf : QPotential r B f) (hr : 2 ≤ r)
    {m : ℝ} (hm : m ≠ 0) (v x : E) :
    DifferentiableAt ℝ (fun p : ℝ × E => vectorStep p.1 p.2 f x) (m,v) :=
  (contDiffAt_mass_direction_step hf hr hm v x).differentiableAt (by norm_num)

theorem contDiffAt_paramStep (hf : QPotential r B f) (hr : 2 ≤ r)
    {mass : ℝ → ℝ} {v : ℝ → E} {k : ℝ}
    (hm : ContDiffAt ℝ 2 mass k) (hv : ContDiffAt ℝ 2 v k) (hm0 : mass k ≠ 0) (x : E) :
    ContDiffAt ℝ 2 (fun a : ℝ => vectorStep (mass a) (v a) f x) k := by
  convert! (contDiffAt_mass_direction_step hf hr hm0 (v k) x).comp k (hm.prodMk hv) using 1

theorem hasDerivAt_paramStep (hf : QPotential r B f) (hr : 2 ≤ r)
    {mass : ℝ → ℝ} {v : ℝ → E} {k dm : ℝ} {w : E}
    (hm : HasDerivAt mass dm k) (hv : HasDerivAt v w k) (hm0 : mass k ≠ 0) (x : E) :
    HasDerivAt (fun a : ℝ => vectorStep (mass a) (v a) f x)
      (dm * deriv (fun a : ℝ => vectorStep a (v k) f x) (mass k) +
        tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x) k := by
  let T : ℝ × E → ℝ := fun p => vectorStep p.1 p.2 f x
  let D := fderiv ℝ T (mass k, v k)
  have hd := differentiableAt_mass_direction_step hf hr hm0 (v k) x
  have hmassCurve : HasDerivAt (fun a : ℝ => (a, v k)) (1,0) (mass k) :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  have hM : D (1,0) = deriv (fun a : ℝ => vectorStep a (v k) f x) (mass k) := by
    exact (hd.hasFDerivAt.comp_hasDerivAt (mass k) hmassCurve).deriv.symm
  have hpair : HasFDerivAt (fun u : E => (mass k,u))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) (v k) :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have hP := (hd.hasFDerivAt.comp (v k) hpair).fderiv
  change fderiv ℝ (fun u : E => vectorStep (mass k) u f x) (v k) = _ at hP
  have hV : D (0,w) = tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x := by
    rw [← fderiv_direction_step_apply hf hr (mass k) (v k) w x, hP]
    rfl
  have hsum : D (dm,w) = dm * D (1,0) + D (0,w) := by
    have hp : (dm,w) = dm • (1, (0 : E)) + (0,w) := by ext <;> simp
    rw [hp, map_add, map_smul, smul_eq_mul]
  have H := hd.hasFDerivAt.comp_hasDerivAt k (hm.prodMk hv)
  change HasDerivAt (fun a : ℝ => vectorStep (mass a) (v a) f x) (D (dm,w)) k at H
  rwa [hsum, hM, hV] at H

theorem abs_deriv_paramStep_le (hf : QPotential r B f) (hr : 2 ≤ r)
    {mass : ℝ → ℝ} {v : ℝ → E} {k dm : ℝ} {w : E}
    (hm : HasDerivAt mass dm k) (hv : HasDerivAt v w k)
    (hmrange : mass k ∈ Ioc (0 : ℝ) 1) (x : E)
    (hsmall : B * ‖v k‖ ^ 2 ≤ 1 / 2) :
    |deriv (fun a : ℝ => vectorStep (mass a) (v a) f x) k| ≤
      2 * B ^ 2 * ‖v k‖ ^ 2 * |dm| + (B + B ^ 2) * ‖v k‖ * ‖w‖ := by
  have hm01 : mass k ∈ Icc (0 : ℝ) 1 := ⟨hmrange.1.le, hmrange.2⟩
  rw [(hasDerivAt_paramStep hf hr hm hv hmrange.1.ne' x).deriv]
  have hmass := abs_deriv_mass_step_le hf hr hm01 (v k) x hsmall
  have hdir := (qBoundedJets_directionSensitivity (hf.of_le hr) hm01 (v k) w).norm_le x
  change |tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x| ≤ _ at hdir
  have hcoef : directionSensitivityCoefficient 0 B = B + B ^ 2 := by
    simp only [directionSensitivityCoefficient, tiltedCoarseCoefficient, pow_zero, one_mul]
  rw [hcoef] at hdir
  calc
    _ ≤ |dm * deriv (fun a : ℝ => vectorStep a (v k) f x) (mass k)| +
        |tiltedAverage (mass k) (v k) f (directionSource (mass k) (v k) w f) x| := abs_add_le _ _
    _ ≤ |dm| * (2 * B ^ 2 * ‖v k‖ ^ 2) + (B + B ^ 2) * ‖v k‖ * ‖w‖ := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hmass (abs_nonneg dm)) hdir
    _ = _ := by ring

end SKBarriers2.StepCalculus
