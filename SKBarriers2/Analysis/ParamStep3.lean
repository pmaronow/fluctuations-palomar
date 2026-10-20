module

public import SKBarriers2.Analysis.ParamStep2

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def curveFirstMajorant (K k : ℝ) : List (ℝ → ℝ × E) → ℝ
  | [] => 0
  | p :: ps => (1 + K * ‖(p k).2‖ ^ 2) * curveFirstMajorant K k ps +
      K * (‖(p k).2‖ * ‖deriv (fun t => (p t).2) k‖ +
        ‖(p k).2‖ ^ 2 * |deriv (fun t => (p t).1) k|)

theorem curveFirstMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (k : ℝ)
    (ps : List (ℝ → ℝ × E)) : 0 ≤ curveFirstMajorant K k ps := by
  induction ps with
  | nil => exact le_rfl
  | cons p ps ih => dsimp only [curveFirstMajorant]; positivity

theorem curveFirstMajorant_tail_le {K : ℝ} (hK : 0 ≤ K) (k : ℝ)
    (front tail : List (ℝ → ℝ × E)) :
    curveFirstMajorant K k tail ≤ curveFirstMajorant K k (front ++ tail) := by
  induction front with
  | nil => exact le_rfl
  | cons p front ih =>
    have ha := curveFirstMajorant_nonneg hK k (front ++ tail)
    have hs : 0 ≤ K * (‖(p k).2‖ * ‖deriv (fun t => (p t).2) k‖ +
        ‖(p k).2‖ ^ 2 * |deriv (fun t => (p t).1) k|) := by positivity
    simp only [List.cons_append, curveFirstMajorant]
    nlinarith [mul_nonneg (mul_nonneg hK (sq_nonneg ‖(p k).2‖)) ha]

private def jetFirstMajorant (K : ℝ) : List (E × E × ℝ) → ℝ
  | [] => 0
  | p :: ps => (1 + K * ‖p.1‖ ^ 2) * jetFirstMajorant K ps +
      K * (‖p.1‖ * ‖p.2.1‖ + ‖p.1‖ ^ 2 * |p.2.2|)

private theorem curveFirstMajorant_eq_jets (K k : ℝ) (ps : List (ℝ → ℝ × E)) :
    curveFirstMajorant K k ps = jetFirstMajorant K (ps.map fun p =>
      ((p k).2, deriv (fun t => (p t).2) k, deriv (fun t => (p t).1) k)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [curveFirstMajorant, List.map_cons, jetFirstMajorant, ih]

private theorem firstVariationMajorant_eq_jets
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (K : ℝ) (q u : P) (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    firstVariationMajorant K q u ps = jetFirstMajorant K (ps.map fun a =>
      (a.2 q, a.2 u, Real.exp (a.1 q) * a.1 u)) := by
  induction ps with
  | nil => rfl
  | cons a ps ih => simp only [firstVariationMajorant, List.map_cons, jetFirstMajorant, ih]

theorem firstVariationMajorant_logParameters (K : ℝ) (ps : List (ℝ → ℝ × E))
    {k : ℝ} (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k)
    (hpos : ∀ p ∈ ps, 0 < (p k).1) :
    firstVariationMajorant K (ParamChain.logParameters ps k)
      (deriv (ParamChain.logParameters ps) k) (ParamChain.coordinateSteps ps.length) =
        curveFirstMajorant K k ps := by
  rw [firstVariationMajorant_eq_jets, curveFirstMajorant_eq_jets]
  congr 1
  rw [ParamChain.coordinateSteps, List.map_ofFn]
  have hcoords := (ParamChain.logParameters_contDiffAt ps hreg hpos).differentiableAt
    (by norm_num : (2 : WithTop ℕ∞) ≠ 0) |>.hasDerivAt
  have heq : (fun i : Fin ps.length =>
      ((((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.proj i))
          (ParamChain.logParameters ps k)),
        (((ContinuousLinearMap.snd ℝ ℝ E).comp (ContinuousLinearMap.proj i))
          (deriv (ParamChain.logParameters ps) k)),
        Real.exp (((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.proj i))
          (ParamChain.logParameters ps k)) *
          (((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.proj i))
            (deriv (ParamChain.logParameters ps) k)))) =
      fun i => ((ps.get i k).2, deriv (fun t => (ps.get i t).2) k,
        deriv (fun t => (ps.get i t).1) k) := by
    funext i
    have hi := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt k hcoords
    have hm := (hreg _ (List.get_mem ps i)).fst.differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0) |>.hasDerivAt
    have hv := (hreg _ (List.get_mem ps i)).snd.differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0) |>.hasDerivAt
    have hlog := ((ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt k hi).unique
      (hm.log (hpos _ (List.get_mem ps i)).ne')
    have hdir := ((ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt k hi).unique hv
    change (deriv (ParamChain.logParameters ps) k i).1 =
      deriv (fun t => (ps.get i t).1) k / (ps.get i k).1 at hlog
    change (deriv (ParamChain.logParameters ps) k i).2 =
      deriv (fun t => (ps.get i t).2) k at hdir
    change ((ps.get i k).2, (deriv (ParamChain.logParameters ps) k i).2,
      Real.exp (Real.log ((ps.get i k).1)) * (deriv (ParamChain.logParameters ps) k i).1) = _
    rw [hdir, hlog, Real.exp_log (hpos _ (List.get_mem ps i))]
    congr 2
    exact mul_div_cancel₀ _ (hpos _ (List.get_mem ps i)).ne'
  simp only [Function.comp_def]
  rw [heq]
  simpa only [List.ofFn_get, Function.comp_def] using
    (List.map_ofFn (f := ps.get) (g := fun p =>
      ((p k).2, deriv (fun t => (p t).2) k, deriv (fun t => (p t).1) k))).symm

theorem qBoundedJets_first_curveChain
    (ps : List (ℝ → ℝ × E)) {k : ℝ} {n : ℕ} {B K : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f)
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1)
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (n + 1) (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient n (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient (n + 1) (B + 1) ≤ K)
    (hgeometry : ∀ p ∈ ps, (p k).1 ≤ 1 ∧ ‖(p k).2‖ ≤ 1 ∧
      (B + 1) * ‖(p k).2‖ ^ 2 ≤ 1 / 2)
    (hbudget : (stepStabilityCoefficient (n + 3) (B + 1) + 1) *
      chainEnergy (ps.map (fun p => p k)) ≤ 1)
    (hcurv : (B + 1) * chainEnergy (ps.map (fun p => p k)) ≤ 1 / 2) :
    QBoundedJets (n + 1) (curveFirstMajorant K k ps)
      (fun x => deriv (fun t => vectorIncrementChain (ps.map (fun p => p t)) f x) k) := by
  have H := qBoundedJets_first_curveChain_of_energy ps hf hreg hpos hK
    hTilt hMass hDir hgeometry hbudget hcurv
  rw [firstVariationMajorant_logParameters K ps hreg hpos] at H
  exact H

theorem qBoundedJets_first_curveChain_tail
    (ps : List (ℝ → ℝ × E)) {k : ℝ} {n : ℕ} {B K : ℝ} {f : E → ℝ}
    (hf : QPotential (n + 3) B f)
    (hreg : ∀ p ∈ ps, ContDiffAt ℝ 2 p k) (hpos : ∀ p ∈ ps, 0 < (p k).1)
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (n + 1) (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient n (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient (n + 1) (B + 1) ≤ K)
    (hgeometry : ∀ p ∈ ps, (p k).1 ≤ 1 ∧ ‖(p k).2‖ ≤ 1 ∧
      (B + 1) * ‖(p k).2‖ ^ 2 ≤ 1 / 2)
    (hbudget : (stepStabilityCoefficient (n + 3) (B + 1) + 1) *
      chainEnergy (ps.map (fun p => p k)) ≤ 1)
    (hcurv : (B + 1) * chainEnergy (ps.map (fun p => p k)) ≤ 1 / 2)
    (front tail : List (ℝ → ℝ × E)) (hsplit : ps = front ++ tail) :
    QBoundedJets (n + 1) (curveFirstMajorant K k tail)
      (fun x => deriv (fun t => vectorIncrementChain (tail.map (fun p => p t)) f x) k) := by
  have hsub : ∀ p ∈ tail, p ∈ ps :=
    fun p hp => hsplit.symm ▸ List.mem_append_right front hp
  have he : chainEnergy (tail.map (fun p => p k)) ≤
      chainEnergy (ps.map (fun p => p k)) := by
    rw [hsplit, List.map_append, chainEnergy_append]
    exact le_add_of_nonneg_left (chainEnergy_nonneg _)
  have hB := hf.nonneg
  have hS := stepStabilityCoefficient_nonneg (n + 3) (show 0 ≤ B + 1 by positivity)
  exact qBoundedJets_first_curveChain tail hf
    (fun p hp => hreg p (hsub p hp)) (fun p hp => hpos p (hsub p hp))
    hK hTilt hMass hDir (fun p hp => hgeometry p (hsub p hp))
    ((mul_le_mul_of_nonneg_left he (by positivity)).trans hbudget)
    ((mul_le_mul_of_nonneg_left he (by positivity)).trans hcurv)

end SKBarriers2.StepCalculus

namespace SKBarriers2.ParamChain

section SecondStep

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

local instance : NormedAddCommGroup (P × X →L[ℝ] P × X →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (P × X →L[ℝ] P × X →L[ℝ] ℝ) := inferInstance
local instance : ContinuousENorm (P × X →L[ℝ] P × X →L[ℝ] ℝ) :=
  @SeminormedAddGroup.toContinuousENorm (P × X →L[ℝ] P × X →L[ℝ] ℝ) inferInstance

private theorem second_compCLM_apply {Y Z : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {H : Y → ℝ} (hH : ContDiff ℝ 2 H)
    (L : Z →L[ℝ] Y) (z a b : Z) :
    fderiv ℝ (fderiv ℝ (fun y => H (L y))) z a b =
      fderiv ℝ (fderiv ℝ H) (L z) (L a) (L b) := by
  let A : (Y →L[ℝ] ℝ) →L[ℝ] Z →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ Z Y ℝ).flip L
  have heq : fderiv ℝ (fun y => H (L y)) = fun y => A (fderiv ℝ H (L y)) := by
    funext y
    exact ((hH.differentiable (by norm_num) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  have hd := A.hasFDerivAt.comp z
    (((hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
      (L z)).hasFDerivAt.comp z L.hasFDerivAt)
  change HasFDerivAt (fun y => A (fderiv ℝ H (L y)))
    (A.comp ((fderiv ℝ (fderiv ℝ H) (L z)).comp L)) z at hd
  rw [heq, hd.fderiv]
  rfl

theorem second_parameter_gaussianStep {H : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (q : P) (x : X) (u : P) :
    let G : (P × X) × ℝ → ℝ := fun z => H (z.1.1,(z.1.2,z.2))
    fderiv ℝ (fderiv ℝ (gaussianStep 1 G)) (q,x) (u,0) (u,0) =
      (∫ t, fderiv ℝ (fderiv ℝ H) (q,(x,t)) (u,0) (u,0) +
        (fderiv ℝ H (q,(x,t)) (u,0)) ^ 2 ∂gaussianStepLaw 1 G (q,x)) -
      (∫ t, fderiv ℝ H (q,(x,t)) (u,0) ∂gaussianStepLaw 1 G (q,x)) ^ 2 := by
  let L : (P × X) × ℝ →L[ℝ] P × (X × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P X ℝ).toContinuousLinearMap
  let ι : P × (X × ℝ) → (P × X) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  let G : (P × X) × ℝ → ℝ := fun z => H (L z)
  let W : (P × X) × ℝ → ℝ := fun z => Real.exp (G z)
  let Z : P × X → ℝ := fun z => ∫ t, W (z,t) ∂gaussianReal 0 1
  have hG : ContDiff ℝ 2 G := hH.1.comp L.contDiff
  have hW : ContDiff ℝ 2 W := hG.exp
  have he := hH.expSmooth
  have hg : ParamExpGrowth (fun z : P × (X × ℝ) => W (ι z)) := he.2.1
  have hg1 : ParamExpGrowth (fun z : P × (X × ℝ) => fderiv ℝ W (ι z)) :=
    param_reassoc_fderiv_growth (he.1.differentiable (by norm_num)) he.2.2.1
  have hg2 : ParamExpGrowth (fun z : P × (X × ℝ) => fderiv ℝ (fderiv ℝ W) (ι z)) :=
    param_second_compCLM_growth (fun z => Real.exp (H z)) L ι he.1 he.2.2.2
  have hZ : ContDiff ℝ 2 Z := param_contDiff_gaussian_integral W hW hg hg1 hg2
  have hp (z : P × X) : Z z ≠ 0 :=
    (integral_exp_pos (hg.weakLocallyDominated.integrable_section hW.continuous z)).ne'
  have hstep : gaussianStep 1 G = fun z => Real.log (Z z) := by
    funext z
    simp only [gaussianStep, one_ne_zero, ite_false, positiveGaussianLogStep, one_mul, div_one]
    rfl
  have iD : Integrable (fun t => leftRestrict (fderiv ℝ W ((q,x),t)))
      (gaussianReal 0 1) :=
    (hg1.weakLocallyDominated.clm leftRestrict).integrable_section
      (leftRestrict.continuous.comp (hW.fderiv_right (m := 1) (by norm_num)).continuous) (q,x)
  have hgDD : GaussianLocallyDominated (fun z : (P × X) × ℝ =>
      secondLeftRestrict (fderiv ℝ (fderiv ℝ W) z)) :=
    secondLeftRestrict_local_growth hg2.weakLocallyDominated
  have iDD : Integrable (fun t => secondLeftRestrict (fderiv ℝ (fderiv ℝ W) ((q,x),t)))
      (gaussianReal 0 1) := by
    apply GaussianLocallyDominated.integrable_section hgDD
    exact secondLeftRestrict.continuous.comp
        (hW.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num)).continuous
  have hDG (t : ℝ) : fderiv ℝ G ((q,x),t) =
      (fderiv ℝ H (L ((q,x),t))).comp L :=
    ((hH.1.differentiable (by norm_num) (L ((q,x),t))).hasFDerivAt.comp
      ((q,x),t) L.hasFDerivAt).fderiv
  have hfirst (t : ℝ) : leftRestrict (fderiv ℝ W ((q,x),t)) (u,0) =
      Real.exp (G ((q,x),t)) * fderiv ℝ H (q,(x,t)) (u,0) := by
    rw [(hG.differentiable (by norm_num) ((q,x),t)).hasFDerivAt.exp.fderiv, hDG]
    rfl
  have hsecond (t : ℝ) : secondLeftRestrict (fderiv ℝ (fderiv ℝ W) ((q,x),t)) (u,0) (u,0) =
      Real.exp (G ((q,x),t)) * (fderiv ℝ (fderiv ℝ H) (q,(x,t)) (u,0) (u,0) +
        (fderiv ℝ H (q,(x,t)) (u,0)) ^ 2) := by
    rw [fderiv_fderiv_exp G hG]
    simp only [secondLeftRestrict, leftRestrict, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    rw [second_compCLM_apply hH.1 L, hDG]
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.prodAssoc_apply]
    change Real.exp (G ((q,x),t)) *
        fderiv ℝ (fderiv ℝ H) (q,(x,t)) (u,0) (u,0) +
        Real.exp (G ((q,x),t)) * fderiv ℝ H (q,(x,t)) (u,0) *
          fderiv ℝ H (q,(x,t)) (u,0) =
      Real.exp (G ((q,x),t)) * (fderiv ℝ (fderiv ℝ H) (q,(x,t)) (u,0) (u,0) +
        (fderiv ℝ H (q,(x,t)) (u,0)) ^ 2)
    ring
  change fderiv ℝ (fderiv ℝ (gaussianStep 1 G)) (q,x) (u,0) (u,0) = _
  rw [hstep, fderiv_fderiv_log Z hZ hp,
    fderiv_local_gaussian_integral W (hW.of_le (by norm_num))
      hg.weakLocallyDominated hg1.weakLocallyDominated,
    fderiv_fderiv_local_gaussian_integral W hW hg.weakLocallyDominated
      hg1.weakLocallyDominated hg2.weakLocallyDominated]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply iDD,
    ContinuousLinearMap.integral_apply (iDD.apply_continuousLinearMap (u,0)),
    ContinuousLinearMap.integral_apply iD]
  simp_rw [hfirst, hsecond, gaussianStepLaw_integral_inv_smul]
  simp only [one_mul, smul_eq_mul]
  dsimp only [Z, W, G, L]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.prodAssoc_apply]
  ring

end SecondStep

end SKBarriers2.ParamChain
