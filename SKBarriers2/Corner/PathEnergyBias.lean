module

public import SKBarriers2.Corner.PathEnergyProof4
public import SKBarriers2.Corner.PathEnergyRecursions2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.ParamChain

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

variable {P Y : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem tiltedAverage_eq_vectorStepAverage_fun (m : ℝ) (v : E) (f g : E → ℝ) :
    tiltedAverage m v f g = vectorStepAverage m v f g := rfl

theorem integrable_movingAverage_test {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) (p : P) (x : E) :
    Integrable (fun t : ℝ => G (p,x+t • V p))
      (stepLaw (Real.exp (M p)) (V p) (fun y => F (p,y)) x) := by
  have hH := regular_mul_exp_parameter (regular_movingInput hF V) M
  have hT := smooth_movingInput hG V
  have H := hT.2.1.integrable_paramStepLaw hH hT.1.continuous 1 (p,x)
  simpa [gaussianStepLaw,stepLaw,Function.comp_def,vectorTranslation] using H

def exponentialBias (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)))
    (F G : P × E → ℝ) (z : P × E) : ℝ := exponentialAverage ps F G z-G z

theorem smooth_exponentialBias {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    ParamSmooth (exponentialBias ps F G) := by
  convert (smooth_exponentialAverage ps hF hG).add (hG.const_mul (-1)) using 1
  funext z
  simp only [exponentialBias]
  ring

theorem smooth_exponentialGradientCorrection {B : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (W : P →L[ℝ] E)
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) :
    ParamSmooth (fun z : P × E =>
      (fderiv ℝ (vectorIncrementChain (exponentialSteps ps z.1) f) z.2 (W z.1))^2-
        (fderiv ℝ f z.2 (W z.1))^2) := by
  have hgrad := (testJetFamily_terminalGradient hf W).value
  have hsq := (testJetFamily_terminalGradient_sq hf W).value
  have hA := smooth_exponentialAverage ps (regular_fixedTerminal hf (by norm_num) P) hgrad
  have he : exponentialAverage ps (fun z => f z.2) (fun z => fderiv ℝ f z.2 (W z.1)) =
      fun z : P × E => fderiv ℝ (vectorIncrementChain (exponentialSteps ps z.1) f) z.2 (W z.1) := by
    funext z
    change vectorIncrementAverage (exponentialSteps ps z.1) f
      (fun y => fderiv ℝ f y (W z.1)) z.2 = _
    exact (fderiv_chain_average (exponentialSteps ps z.1)
      (hf.boundedDerivs (by norm_num)) z.2 (W z.1)).symm
  rw [he] at hA
  convert (hA.mul hA).add (hsq.const_mul (-1)) using 1
  funext z
  ring

theorem exponentialChain_append (ls rs : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)))
    (F : P × E → ℝ) : exponentialChain (ls++rs) F = exponentialChain ls (exponentialChain rs F) := by
  funext z
  simp only [exponentialChain,exponentialSteps,List.map_append,vectorIncrementChain_append]

theorem exponentialBias_cons {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (q : (P →L[ℝ] ℝ) × (P →L[ℝ] E))
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) (p : P) (x : E) :
    exponentialBias (q::ps) F G (p,x) =
      tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
        (fun y => exponentialBias ps F G (p,y)) x+
        (tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
          (fun y => G (p,y)) x-G (p,x)) := by
  have hf := regular_exponentialChain ps hF
  have hg := smooth_exponentialAverage ps hF hG
  have hi := integrable_movingAverage_test hf hg q.1 q.2 p x
  have hj := integrable_movingAverage_test hf hG q.1 q.2 p x
  have H := integral_sub hi hj
  change tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
    (fun y => exponentialAverage ps F G (p,y)-G (p,y)) x =
      tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
        (fun y => exponentialAverage ps F G (p,y)) x-
      tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
        (fun y => G (p,y)) x at H
  change tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
    (fun y => exponentialAverage ps F G (p,y)) x-G (p,x) =
      tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
        (fun y => exponentialAverage ps F G (p,y)-G (p,y)) x+
      (tiltedAverage (Real.exp (q.1 p)) (q.2 p) (fun y => exponentialChain ps F (p,y))
        (fun y => G (p,y)) x-G (p,x))
  rw [H]
  ring

theorem linearObservation_curve_twoJet {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (L : P →L[ℝ] Y) :
    deriv (fun t => L (p t)) k = L (deriv p k) ∧
      deriv (deriv (fun t => L (p t))) k = L (deriv (deriv p) k) := by
  have hd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  refine ⟨(L.hasFDerivAt.comp_hasDerivAt k hd).deriv,?_⟩
  have he : deriv (fun t => L (p t)) =ᶠ[𝓝 k] fun t => L (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact (L.hasFDerivAt.comp_hasDerivAt t (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [he.deriv_eq]
  exact (L.hasFDerivAt.comp_hasDerivAt k hdd).deriv

theorem exponentialMass_curve_twoJet {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (M : P →L[ℝ] ℝ) :
    deriv (fun t => Real.exp (M (p t))) k = Real.exp (M (p k))*M (deriv p k) ∧
      deriv (deriv (fun t => Real.exp (M (p t)))) k =
        Real.exp (M (p k))*((M (deriv p k))^2+M (deriv (deriv p) k)) := by
  have hd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hp.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  refine ⟨((M.hasFDerivAt.comp_hasDerivAt k hd).exp).deriv,?_⟩
  have he : deriv (fun t => Real.exp (M (p t))) =ᶠ[𝓝 k]
      fun t => Real.exp (M (p t))*M (deriv p t) := by
    filter_upwards [hp.eventually (by norm_num)] with t ht
    exact ((M.hasFDerivAt.comp_hasDerivAt t
      (ht.differentiableAt (by norm_num)).hasDerivAt).exp).deriv
  rw [he.deriv_eq]
  convert! ((((M.hasFDerivAt.comp_hasDerivAt k hd).exp).mul
    (M.hasFDerivAt.comp_hasDerivAt k hdd)).deriv) using 1
  simp only [Function.comp_def]
  ring

theorem chartAverage_twoJet {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B A C D : ℝ}
    (hf : QPotential 4 B (fun y => F (p k,y)))
    (hF₁ : QBoundedJets 3 A (fun y => deriv (fun t => F (p t,y)) k))
    (hg : QBoundedJets 3 C (fun y => G (p k,y)))
    (ha : QBoundedJets 1 D (fun y => deriv (fun t => G (p t,y)) k))
    (hm : Real.exp (M (p k)) ≤ 1) (x : E) :
    let m := fun t => Real.exp (M (p t))
    let v := fun t => V (p t)
    let f := fun y => F (p k,y)
    let f₁ := fun y => deriv (fun t => F (p t,y)) k
    let f₂ := fun y => deriv (deriv (fun t => F (p t,y))) k
    let g := fun y => G (p k,y)
    let a := fun y => deriv (fun t => G (p t,y)) k
    let q := fun y => deriv (deriv (fun t => G (p t,y))) k
    let T := fun t => tiltedAverage (m t) (v t) (fun y => F (p t,y))
      (fun y => G (p t,y)) x
    ContDiffAt ℝ 2 T k ∧
      deriv T k = firstTiltedAverageSource (m k) (v k) f f₁ g a (deriv m k) (deriv v k) x ∧
      deriv (deriv T) k = secondMovingAverageSource (m k) (deriv m k) (deriv (deriv m) k)
        (v k) (deriv v k) (deriv (deriv v) k) f f₁ f₂ g a q x := by
  dsimp only
  have hfirstF (y : E) : deriv (fun t => F (p t,y)) k =
      fderiv ℝ F (p k,y) (deriv p k,0) := by
    simpa only [Function.comp_def] using
      ((hF.1.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
        ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k y))).deriv
  have hfirstG (y : E) : deriv (fun t => G (p t,y)) k =
      fderiv ℝ G (p k,y) (deriv p k,0) := by
    simpa only [Function.comp_def] using
      ((hG.1.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
        ((hp.differentiableAt (by norm_num)).hasDerivAt.prodMk (hasDerivAt_const k y))).deriv
  have hF₁' : QBoundedJets 3 A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)) := by
    simpa only [hfirstF] using hF₁
  have ha' : QBoundedJets 1 D (fun y => fderiv ℝ G (p k,y) (deriv p k,0)) := by
    simpa only [hfirstG] using ha
  have hfirst := deriv_exponential_movingAverage hF hG M V hp hf hF₁' hg ha' hm x
  have hsecond := second_deriv_exponential_movingAverage hF hG M V hp x
  dsimp only at hsecond
  have hff₁ := (funext hfirstF).symm
  have hgg₁ := (funext hfirstG).symm
  have hff₂ := (funext (fun y : E => second_parameter_curve hF.1 hp y)).symm
  have hgg₂ := (funext (fun y : E => second_parameter_curve hG.1 hp y)).symm
  rw [hff₁,hgg₁] at hfirst
  rw [hff₁,hff₂,hgg₁,hgg₂] at hsecond
  have hmjets := exponentialMass_curve_twoJet hp M
  have hvjets := linearObservation_curve_twoJet hp V
  rw [hmjets.1,hvjets.1]
  refine ⟨hsecond.1,hfirst,?_⟩
  rw [hmjets.2,hvjets.2]
  exact hsecond.2

theorem continuous_second_parameter_curve {F : P × E → ℝ}
    (hF : ContDiff ℝ 2 F) {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) :
    Continuous (fun x => deriv (deriv (fun t => F (p t,x))) k) := by
  have he : (fun x => deriv (deriv (fun t => F (p t,x))) k) =
      fun x => fderiv ℝ (fderiv ℝ F) (p k,x) (deriv p k,0) (deriv p k,0)+
        fderiv ℝ F (p k,x) (deriv (deriv p) k,0) := funext (second_parameter_curve hF hp)
  rw [he]
  have hc : Continuous (fun x : E => (p k,x)) := continuous_const.prodMk continuous_id
  exact (((((hF.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
    (by norm_num)).continuous.comp hc).clm_apply continuous_const).clm_apply continuous_const).add
    (((hF.fderiv_right (m := 1) (by norm_num)).continuous.comp hc).clm_apply continuous_const)

end SKBarriers2.ParamChain

namespace SKBarriers2.Corner

open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

set_option maxHeartbeats 400000 in
theorem exponentialBias_step_jets {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (q : (P →L[ℝ] ℝ) × (P →L[ℝ] E))
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E)))
    {p : ℝ → P} {k B R K D e a b c : ℝ} (hp : ContDiffAt ℝ 2 p k)
    (hK : 0 ≤ K)
    (hK₄ : |tiltedStabilityCoefficient 4 B| ≤ K)
    (hK₂ : |tiltedStabilityCoefficient 2 B| ≤ K)
    (hK₁ : firstTiltedTransportCoefficient B R ≤ K)
    (hKS : secondAverageTransportCoefficient (secondMovingAverageScale B R R)
      (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B) (defectNoiseMomentBound 3 B) ≤ K)
    (hbase : QPotential 5 B (fun x => exponentialChain ps F (p k,x)))
    (hbase₁ : QBoundedJets 3 R (fun x => deriv (fun t => exponentialChain ps F (p t,x)) k))
    (hbase₂ : QBoundedJets 1 R (fun x => deriv (deriv (fun t => exponentialChain ps F (p t,x))) k))
    (hm : Real.exp (q.1 (p k)) ≤ 1)
    (hdm : |deriv (fun t => Real.exp (q.1 (p t))) k| ≤ 1)
    (hddm : |deriv (deriv (fun t => Real.exp (q.1 (p t)))) k| ≤ 1)
    (hv : ‖q.2 (p k)‖ ≤ 1)
    (hsmall : Real.exp (q.1 (p k))*(B*‖q.2 (p k)‖^2) ≤ 1/2)
    (henergy : ‖q.2 (p k)‖^2+‖deriv (fun t => q.2 (p t)) k‖^2+
      ‖deriv (deriv (fun t => q.2 (p t))) k‖^2 ≤ e) (he1 : e ≤ 1)
    (htail : QBoundedJets 4 a (fun x => exponentialBias ps F G (p k,x)))
    (htail₁ : QBoundedJets 2 b (fun x => deriv (fun t => exponentialBias ps F G (p t,x)) k))
    (htail₂ : QBoundedJets 0 c (fun x => deriv (deriv (fun t => exponentialBias ps F G (p t,x))) k))
    (hsource : let L := (fun t x => tiltedAverage (Real.exp (q.1 (p t))) (q.2 (p t))
      (fun y => exponentialChain ps F (p t,y)) (fun y => G (p t,y)) x-G (p t,x));
      QBoundedJets 4 (D*e) (L k) ∧
        QBoundedJets 2 (D*e) (fun x => deriv (fun t => L t x) k) ∧
        QBoundedJets 0 (D*e) (fun x => deriv (deriv (fun t => L t x)) k)) :
    QBoundedJets 4 ((1+K*e)*a+D*e) (fun x => exponentialBias (q::ps) F G (p k,x)) ∧
      QBoundedJets 2 ((1+K*e)*b+K*e*a+D*e)
        (fun x => deriv (fun t => exponentialBias (q::ps) F G (p t,x)) k) ∧
      QBoundedJets 0 ((1+K*e)*c+K*e*(a+b)+D*e)
        (fun x => deriv (deriv (fun t => exponentialBias (q::ps) F G (p t,x))) k) := by
  let H := exponentialChain ps F
  let U := exponentialBias ps F G
  let T := fun t x => tiltedAverage (Real.exp (q.1 (p t))) (q.2 (p t))
    (fun y => H (p t,y)) (fun y => U (p t,y)) x
  let L := fun t x => tiltedAverage (Real.exp (q.1 (p t))) (q.2 (p t))
    (fun y => H (p t,y)) (fun y => G (p t,y)) x-G (p t,x)
  have hH : ParamRegular H := regular_exponentialChain ps hF
  have hU : ParamSmooth U := smooth_exponentialBias hF hG ps
  have hT : ParamSmooth (fun z : P × E => tiltedAverage (Real.exp (q.1 z.1)) (q.2 z.1)
      (fun y => H (z.1,y)) (fun y => U (z.1,y)) z.2) := smooth_movingAverage hH hU q.1 q.2
  have hLc : ParamSmooth (fun z : P × E => tiltedAverage (Real.exp (q.1 z.1)) (q.2 z.1)
      (fun y => H (z.1,y)) (fun y => G (z.1,y)) z.2-G z) := by
    convert (smooth_movingAverage hH hG q.1 q.2).add (hG.const_mul (-1)) using 1
    funext z
    simp only [tiltedAverage_eq_vectorStepAverage_fun]
    ring
  have hTc (x : E) : ContDiffAt ℝ 2 (fun t => T t x) k :=
    (hT.1.contDiffAt (x := (p k,x))).comp (f := fun t : ℝ => (p t,x)) k
      (hp.prodMk (contDiffAt_const (c := x)))
  have hL (x : E) : ContDiffAt ℝ 2 (fun t => L t x) k :=
    (hLc.1.contDiffAt (x := (p k,x))).comp (f := fun t : ℝ => (p t,x)) k
      (hp.prodMk (contDiffAt_const (c := x)))
  have hjet (x : E) := chartAverage_twoJet hH hU q.1 q.2
    (p := p) (k := k) (B := B) (A := R) (C := a) (D := b) hp
    (hbase.of_le (by norm_num : 4 ≤ 5)) hbase₁
    (htail.of_le (by norm_num : 3 ≤ 4)) (htail₁.of_le (by norm_num : 1 ≤ 2)) hm x
  dsimp only at hjet
  have hm' : Real.exp (q.1 (p k)) ∈ Icc (0:ℝ) 1 := ⟨(Real.exp_pos _).le,hm⟩
  have he : 0 ≤ e := by
    nlinarith only [henergy,sq_nonneg ‖q.2 (p k)‖,
      sq_nonneg ‖deriv (fun t => q.2 (p t)) k‖,sq_nonneg ‖deriv (deriv (fun t => q.2 (p t))) k‖]
  have hvE : ‖q.2 (p k)‖^2 ≤ e := by
    nlinarith only [henergy,
      sq_nonneg ‖deriv (fun t => q.2 (p t)) k‖,sq_nonneg ‖deriv (deriv (fun t => q.2 (p t))) k‖]
  have hval : QBoundedJets 4 ((1+K*e)*a) (T k) := by
    apply (qBoundedJets_tiltedAverage 4 hbase (by norm_num) le_rfl htail hm' _ hsmall).mono
    have H₁ := mul_le_mul_of_nonneg_right (le_abs_self (tiltedStabilityCoefficient 4 B))
      (mul_nonneg htail.nonneg (sq_nonneg ‖q.2 (p k)‖))
    have H₂ := mul_le_mul_of_nonneg_right hK₄ (mul_nonneg htail.nonneg (sq_nonneg ‖q.2 (p k)‖))
    have H₃ := mul_le_mul_of_nonneg_left hvE (mul_nonneg hK htail.nonneg)
    nlinarith only [H₁,H₂,H₃]
  have hfirst : QBoundedJets 2 ((1+K*e)*b+K*e*a) (fun x => deriv (fun t => T t x) k) := by
    have H₁ := qBoundedJets_firstTiltedAverageSource_energy hbase hbase₁ htail htail₁
      hbase₁.nonneg le_rfl hm' hdm (q.2 (p k)) (deriv (fun t => q.2 (p t)) k) hv hsmall
      (show ‖q.2 (p k)‖^2+‖deriv (fun t => q.2 (p t)) k‖^2 ≤ e by
        nlinarith only [henergy,sq_nonneg ‖deriv (deriv (fun t => q.2 (p t))) k‖])
    have heq : (fun x => deriv (fun t => T t x) k) = _ := funext (fun x => (hjet x).2.1)
    rw [heq]
    apply H₁.mono
    have H₂ := mul_le_mul_of_nonneg_right hK₂ (mul_nonneg he htail₁.nonneg)
    have H₃ := mul_le_mul_of_nonneg_right hK₁ (mul_nonneg htail.nonneg he)
    nlinarith only [H₂,H₃]
  have ha0 := htail.nonneg
  have hb0 := htail₁.nonneg
  have hc0 := htail₂.nonneg
  have hsecond : QBoundedJets 0 ((1+K*e)*c+K*e*(a+b))
      (fun x => deriv (deriv (fun t => T t x)) k) := by
    refine ⟨by positivity,contDiff_zero.mpr (continuous_second_parameter_curve hT.1 hp),?_⟩
    intro n hn x
    have hn0 : n = 0 := by omega
    subst n
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    rw [(hjet x).2.2]
    have H₁ := abs_secondMovingAverageSource_energy
      (hbase.of_le (by norm_num : 3 ≤ 5)) (hbase₁.of_le (by norm_num : 1 ≤ 3)) hbase₂
      (htail.of_le (by norm_num : 2 ≤ 4)) htail₁ htail₂ hm' hdm hddm _ _ _ henergy he1 x
    have H₂ := mul_le_mul_of_nonneg_right hKS (mul_nonneg (add_nonneg htail.nonneg htail₁.nonneg) he)
    have H₃ := mul_nonneg (mul_nonneg hK he) htail₂.nonneg
    exact H₁.trans (by nlinarith only [H₂,H₃])
  have heq (t : ℝ) (x : E) : exponentialBias (q::ps) F G (p t,x) = T t x+L t x :=
    exponentialBias_cons hF hG q ps (p t) x
  have heq₀ : (fun x => exponentialBias (q::ps) F G (p k,x)) = fun x => T k x+L k x :=
    funext (heq k)
  have heq₁ : (fun x => deriv (fun t => exponentialBias (q::ps) F G (p t,x)) k) =
      fun x => deriv (fun t => T t x) k+deriv (fun t => L t x) k := by
    funext x
    simp_rw [heq]
    exact deriv_fun_add ((hTc x).differentiableAt (by norm_num)) ((hL x).differentiableAt (by norm_num))
  have heq₂ : (fun x => deriv (deriv (fun t => exponentialBias (q::ps) F G (p t,x))) k) =
      fun x => deriv (deriv (fun t => T t x)) k+deriv (deriv (fun t => L t x)) k := by
    funext x
    simp_rw [heq]
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using iteratedDeriv_fun_add (hTc x) (hL x)
  rw [heq₀,heq₁,heq₂]
  exact ⟨hval.add hsource.1,hfirst.add hsource.2.1,hsecond.add hsource.2.2⟩

end SKBarriers2.Corner
