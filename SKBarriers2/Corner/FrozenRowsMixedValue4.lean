module

public import SKBarriers2.Corner.FrozenRowsMixedValue3
public import SKBarriers2.Corner.FrozenRowsMixedCurveJet
public import SKBarriers2.Corner.FrozenRowsNoise7
public import SKBarriers2.Corner.FrozenRowsMixed3

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic

namespace SKBarriers2.Corner
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "X" => (Fin 3 → ℝ)

def frozenRowsCoarseRawJet (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (n : ℕ) (i : Fin 3) (y : X) (k : ℝ) : MomentKJet :=
  MomentKJet.rescale (Real.sqrt h)
    (originalEpsilonKJet (fun t => (frozenSchedule β a (1 / 2) h t).drop n)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z)
      (Real.sqrt h) (fun _ => z) (fun _ => y) (i.val + 1) ε k)

theorem affineCoordinateAverage_eq_tiltedAverage (c : AffineGaussianCoordinate P X)
    (F G : P × X → ℝ) (p : P) (x : X) :
    affineCoordinateAverage c F G (p,x) =
      StepCalculus.tiltedAverage (Real.exp (c.logMass p)) (c.noise p)
        (fun y => F (p,y)) (fun y => G (p,y)) (c.mean p x+c.shift p) := rfl

def AffineGaussianCoordinate.centeredRescale (c : AffineGaussianCoordinate P X)
    (ρ : ℝ) (center : X) : AffineGaussianCoordinate (ℝ × P) X where
  logMass := c.logMass.comp (ContinuousLinearMap.snd ℝ ℝ P)
  mean := c.mean.comp (ContinuousLinearMap.snd ℝ ℝ P)
  shift := ρ⁻¹ •
    (((ContinuousLinearMap.apply ℝ X center).comp c.mean + c.shift).comp
      (ContinuousLinearMap.snd ℝ ℝ P) -
        (ContinuousLinearMap.fst ℝ ℝ P).smulRight center)
  noise := ρ⁻¹ • c.noise.comp (ContinuousLinearMap.snd ℝ ℝ P)

theorem centeredRescale_logMass (c : AffineGaussianCoordinate P X) (ρ : ℝ) (center : X) (p : P) :
    (c.centeredRescale ρ center).logMass (1,p) = c.logMass p := rfl

theorem centeredRescale_mean (c : AffineGaussianCoordinate P X) (ρ : ℝ) (center : X) (p : P) :
    (c.centeredRescale ρ center).mean (1,p) = c.mean p := rfl

theorem centeredRescale_noise (c : AffineGaussianCoordinate P X) (ρ : ℝ) (center : X) (p : P) :
    (c.centeredRescale ρ center).noise (1,p) = ρ⁻¹ • c.noise p := rfl

theorem centeredRescale_shift (c : AffineGaussianCoordinate P X) (ρ : ℝ) (center : X) (p : P) :
    (c.centeredRescale ρ center).shift (1,p) = ρ⁻¹ • (c.mean p center+c.shift p-center) := by
  simp only [AffineGaussianCoordinate.centeredRescale, smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply, add_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', one_smul]

theorem affineCoordinateAverage_centeredRescale {ρ : ℝ} (hρ : ρ ≠ 0) (center : X)
    (c : AffineGaussianCoordinate P X) (F G : P × X → ℝ)
    (F' G' : (ℝ × P) × X → ℝ)
    (hF : ∀ p y, F' ((1,p),y) = F (p,ρ • y+center))
    (hG : ∀ p y, G' ((1,p),y) = G (p,ρ • y+center)) (p : P) (x : X) :
    affineCoordinateAverage (c.centeredRescale ρ center) F' G' ((1,p),x) =
      affineCoordinateAverage c F G (p,ρ • x+center) := by
  have H := congrFun (StepCalculus.spatialRescale_affine_tiltedAverage hρ
    (Real.exp (c.logMass p)) (c.mean p) (c.shift p) center (c.noise p)
    (fun y => F (p,y)) (fun y => G (p,y))) x
  rw [affineCoordinateAverage_eq_tiltedAverage, affineCoordinateAverage_eq_tiltedAverage,
    centeredRescale_logMass, centeredRescale_mean, centeredRescale_noise, centeredRescale_shift]
  have hFfun : (fun y => F' ((1,p),y)) = spatialRescale ρ center (fun y => F (p,y)) :=
    funext (hF p)
  have hGfun : (fun y => G' ((1,p),y)) = spatialRescale ρ center (fun y => G (p,y)) :=
    funext (hG p)
  rw [hFfun,hGfun]
  exact H.symm

theorem affinePotentialChain_centeredRescale {ρ : ℝ} (hρ : ρ ≠ 0) (center : X)
    (cs : List (AffineGaussianCoordinate P X)) (F : P × X → ℝ)
    (F' : (ℝ × P) × X → ℝ)
    (hF : ∀ p y, F' ((1,p),y) = F (p,ρ • y+center)) :
    ∀ p y, affinePotentialChain (cs.map (fun c => c.centeredRescale ρ center)) F' ((1,p),y) =
      affinePotentialChain cs F (p,ρ • y+center) := by
  induction cs with
  | nil => exact hF
  | cons c cs ih =>
    intro p y
    let f := fun x => affinePotentialChain cs F (p,x)
    let A := c.mean p
    let b := c.shift p
    let v := c.noise p
    have H := congrFun (spatialRescale_vectorStep ρ (Real.exp (c.logMass p)) center
      (ρ⁻¹ • v) f) (A y+ρ⁻¹ • (A center+b-center))
    simp only [smul_smul,mul_inv_cancel₀ hρ,one_smul] at H
    dsimp only [spatialRescale] at H
    rw [← StepCalculus.affine_rescale hρ] at H
    simp only [List.map_cons, affinePotentialChain]
    rw [centeredRescale_logMass, centeredRescale_mean, centeredRescale_noise, centeredRescale_shift]
    change vectorStep (Real.exp (c.logMass p)) (ρ⁻¹ • v)
      (fun x => affinePotentialChain (cs.map (fun c => c.centeredRescale ρ center)) F' ((1,p),x))
      (A y+ρ⁻¹ • (A center+b-center)) =
        vectorStep (Real.exp (c.logMass p)) v f (A (ρ • y+center)+b)
    have htail : (fun x => affinePotentialChain
        (cs.map (fun c => c.centeredRescale ρ center)) F' ((1,p),x)) =
        spatialRescale ρ center f := funext (fun x => ih p x)
    rw [htail]
    exact H.symm

theorem affineEpsilonJetChain_centeredRescale {ρ : ℝ} (hρ : ρ ≠ 0) (center : X)
    (cs : List (AffineGaussianCoordinate P X)) (F K : P × X → ℝ)
    (F' K' : (ℝ × P) × X → ℝ)
    (hF : ∀ p y, F' ((1,p),y) = F (p,ρ • y+center))
    (hK : ∀ p y, K' ((1,p),y) = K (p,ρ • y+center)) :
    ∀ i : Fin 3, ∀ p y,
      affineEpsilonJetChain (cs.map (fun c => c.centeredRescale ρ center)) F' K' i ((1,p),y) =
        affineEpsilonJetChain cs F K i (p,ρ • y+center) := by
  induction cs with
  | nil =>
    intro i p y
    fin_cases i
    · exact hK p y
    · rfl
    · rfl
  | cons c cs ih =>
    let m := fun z : P × X => Real.exp (c.logMass z.1)
    let m' := fun z : (ℝ × P) × X => Real.exp ((c.centeredRescale ρ center).logMass z.1)
    let R := affineEpsilonJetChain cs F K
    let R' := affineEpsilonJetChain (cs.map (fun c => c.centeredRescale ρ center)) F' K'
    have hmass (p : P) (y : X) : m' ((1,p),y) = m (p,ρ • y+center) := rfl
    have hBell (i : Fin 3) (p : P) (y : X) :
        epsilonBellFamilies m' R' i ((1,p),y) = epsilonBellFamilies m R i (p,ρ • y+center) := by
      fin_cases i <;> simp only [epsilonBellFamilies, Matrix.cons_val_zero',
        Matrix.cons_val_succ', hmass, R, R', ih]
    have hA (i : Fin 3) (p : P) (y : X) :
        affineCoordinateAverage (c.centeredRescale ρ center)
          (affinePotentialChain (cs.map (fun c => c.centeredRescale ρ center)) F')
          (epsilonBellFamilies m' R' i) ((1,p),y) =
        affineCoordinateAverage c (affinePotentialChain cs F)
          (epsilonBellFamilies m R i) (p,ρ • y+center) :=
      affineCoordinateAverage_centeredRescale hρ center c _ _ _ _
        (affinePotentialChain_centeredRescale hρ center cs F F' hF) (hBell i) p y
    intro i p y
    change epsilonCumulantFamilies m'
      (fun i => affineCoordinateAverage (c.centeredRescale ρ center)
        (affinePotentialChain (cs.map (fun c => c.centeredRescale ρ center)) F')
        (epsilonBellFamilies m' R' i)) i ((1,p),y) =
      epsilonCumulantFamilies m (fun i => affineCoordinateAverage c (affinePotentialChain cs F)
        (epsilonBellFamilies m R i)) i (p,ρ • y+center)
    fin_cases i <;> simp only [epsilonCumulantFamilies, Matrix.cons_val_zero',
      Matrix.cons_val_succ', hA, hmass]

theorem scalarData_frozenTerminal_centered_affine_inputs
    {β s h : ℝ} (D : ScalarData β) (ht : s + 4 * h ∈ Icc (0 : ℝ) 1)
    (ρ z ε : ℝ) :
    ParamRegular (fun q : (ℝ × P) × X => ε *
      frozenTerminal β (cdf (D.μ : Measure ℝ)) s h (ρ • q.2+q.1.1 • (fun _ => z))) ∧
    ParamSmooth (fun q : (ℝ × P) × X =>
      terminalResidual β (cdf (D.μ : Measure ℝ)) s h z
        (ρ • q.2+q.1.1 • (fun _ => z))) := by
  obtain ⟨hF,hK⟩ := scalarData_frozenTerminal_affine_inputs (P := ℝ × P)
    (z := z) (ε := ε) D ht
  let b : (ℝ × P) →L[ℝ] X := (ContinuousLinearMap.fst ℝ ℝ P).smulRight (fun _ => z)
  let A : X →L[ℝ] X := ρ • ContinuousLinearMap.id ℝ X
  exact ⟨(ParamChain.regular_parameterTranslation hF b).fieldComp A,
    (ParamChain.smooth_parameterTranslation hK b).fieldComp A⟩

theorem parameterCurveKJet_Bell {U : Set ℝ} (hU : IsOpen U)
    {p : ℝ → P} (hp : ∀ k ∈ U, ContDiffAt ℝ 2 p k)
    {R : Fin 3 → P × X → ℝ} (hR : ∀ i, ParamSmooth (R i))
    (c : AffineGaussianCoordinate P X) (m : ℝ)
    (hm : ∀ k ∈ U, Real.exp (c.logMass (p k)) = m)
    {k : ℝ} (hk : k ∈ U) (x : X) (ρ : ℝ) (i : Fin 3) :
    MomentKJet.rescale ρ (parameterCurveKJet
      (epsilonBellFamilies (fun z => Real.exp (c.logMass z.1)) R i) p k x) =
      epsilonBellTestsKJet m
        (fun j => MomentKJet.rescale ρ (parameterCurveKJet (R j) p k x)) i := by
  rw [← epsilonBellTestsKJet_rescale]
  congr 1
  have hactual : ∀ t ∈ U, MomentKJet.Differentiates
      (fun t => epsilonBellTestsKJet m (fun j => parameterCurveKJet (R j) p t x) i) t := by
    intro t ht
    exact epsilonBellTestsKJet_differentiates
      (fun j => parameterCurveKJet_differentiates (hR j) (hp t ht) x) m i
  have hvalue : ∀ t ∈ U,
      epsilonBellFamilies (fun z => Real.exp (c.logMass z.1)) R i (p t,x) =
        (epsilonBellTestsKJet m (fun j => parameterCurveKJet (R j) p t x) i).value := by
    intro t ht
    fin_cases i <;> simp only [epsilonBellFamilies, epsilonBellTestsKJet,
      parameterCurveKJet, MomentKJet.add, MomentKJet.scale, MomentKJet.mul,
      Matrix.cons_val_zero', Matrix.cons_val_succ', hm t ht] <;> ring
  exact MomentKJet.actual_of_eqOn
    (J := fun t => epsilonBellTestsKJet m (fun j => parameterCurveKJet (R j) p t x) i)
    (f := fun t => epsilonBellFamilies (fun z => Real.exp (c.logMass z.1)) R i (p t,x))
    hU hactual hvalue hk

theorem parameterCurveKJet_Cumulants {U : Set ℝ} (hU : IsOpen U)
    {p : ℝ → P} (hp : ∀ k ∈ U, ContDiffAt ℝ 2 p k)
    {A : Fin 3 → P × X → ℝ} (hA : ∀ i, ParamSmooth (A i))
    (c : AffineGaussianCoordinate P X) (m : ℝ)
    (hm : ∀ k ∈ U, Real.exp (c.logMass (p k)) = m)
    {k : ℝ} (hk : k ∈ U) (x : X) (ρ : ℝ) (i : Fin 3) :
    MomentKJet.rescale ρ (parameterCurveKJet
      (epsilonCumulantFamilies (fun z => Real.exp (c.logMass z.1)) A i) p k x) =
      epsilonLogCumulantsKJet m
        (fun j => MomentKJet.rescale ρ (parameterCurveKJet (A j) p k x)) i := by
  rw [← epsilonLogCumulantsKJet_rescale]
  congr 1
  have hactual : ∀ t ∈ U, ∀ j, MomentKJet.Differentiates
      (fun t => parameterCurveKJet (A j) p t x) t := by
    intro t ht j
    exact parameterCurveKJet_differentiates (hA j) (hp t ht) x
  have hvalue : ∀ t ∈ U, ∀ j,
      epsilonCumulantFamilies (fun z => Real.exp (c.logMass z.1)) A j (p t,x) =
        (epsilonLogCumulantsKJet m (fun j => parameterCurveKJet (A j) p t x) j).value := by
    intro t ht j
    fin_cases j <;> simp only [epsilonCumulantFamilies, epsilonLogCumulantsKJet,
      parameterCurveKJet, MomentKJet.add, MomentKJet.scale, MomentKJet.mul,
      Matrix.cons_val_zero', Matrix.cons_val_succ', hm t ht] <;> ring
  exact epsilonLogCumulantsKJet_actual (A := fun j t => parameterCurveKJet (A j) p t x)
    (f := fun j t => epsilonCumulantFamilies (fun z => Real.exp (c.logMass z.1)) A j (p t,x))
    hU hactual m hvalue hk i

theorem epsilonLogCumulantsKJet_first_slots_congr
    (m : ℝ) {A B : Fin 3 → MomentKJet}
    (hv : ∀ i, (A i).value = (B i).value)
    (ha : ∀ i, (A i).first = (B i).first) (i : Fin 3) :
    (epsilonLogCumulantsKJet m A i).value = (epsilonLogCumulantsKJet m B i).value ∧
      (epsilonLogCumulantsKJet m A i).first = (epsilonLogCumulantsKJet m B i).first := by
  fin_cases i <;> constructor <;>
    simp only [epsilonLogCumulantsKJet, MomentKJet.add, MomentKJet.mul, MomentKJet.scale,
      Matrix.cons_val_zero', Matrix.cons_val_succ', hv, ha]

theorem epsilonAffineStep_first_degree
    {U : Set ℝ} (hU : IsOpen U) {p : ℝ → P}
    (hp : ∀ k ∈ U, ContDiffAt ℝ 2 p k) {k : ℝ} (hk : k ∈ U)
    {r : ℕ} {B M δ T L K ρ m : ℝ}
    (c : AffineGaussianCoordinate P X) {F : P × X → ℝ}
    (hF : ParamRegular F) {R : Fin 3 → P × X → ℝ} (hR : ∀ i, ParamSmooth (R i))
    (hmass : ∀ t ∈ U, Real.exp (c.logMass (p t)) = m)
    (hm : m ∈ Ioc (0 : ℝ) 1) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hL : 0 ≤ L) (hK : 1 ≤ K) (hv : ‖c.noise (p k)‖ ≤ K)
    (hQ : QPotential (r + 1) B (fun y => F (p k,y)))
    (hs : ContDiff ℝ r (fun z : ℝ × X =>
      ρ * deriv (fun t => affineCoordinateDensityPotential c F (p t,(z.2,z.1))) k))
    (hsj : ∀ q : ℕ, q ≤ 5 → ∀ t : ℝ, WJets r (L * (1 + |t|) ^ (q + 1)) 1
      (fun x => ρ * deriv (fun u => affineCoordinateDensityPotential c F (p u,(x,t))) k))
    (hcoef : ∀ q : ℕ, q ≤ 5 →
      movingAffineFirstCoefficient r q B K L (c.mean (p k)) (ρ • c.mean (deriv p k))
        (c.shift (p k)) (ρ • c.shift (deriv p k)) (c.noise (p k)) (ρ • c.noise (deriv p k)) ≤ T)
    (HJ : ∀ i : Fin 3, MomentKJet.FirstDegreeBound (r + 1)
      ((M * δ) ^ (i.val + 1)) (2 * (i.val + 1) - 1)
      (fun y => MomentKJet.rescale ρ (parameterCurveKJet (R i) p k y))) :
    let mass := fun z : P × X => Real.exp (c.logMass z.1)
    let A := fun i => affineCoordinateAverage c F (epsilonBellFamilies mass R i)
    ∀ i : Fin 3, MomentKJet.FirstDegreeBound r
      ((epsilonSpatialStepBudget (r + 2) T * M * δ) ^ (i.val + 1))
      (2 * (i.val + 1) - 1)
      (fun y => MomentKJet.rescale ρ
        (parameterCurveKJet (epsilonCumulantFamilies mass A i) p k y)) := by
  dsimp only
  let mass := fun z : P × X => Real.exp (c.logMass z.1)
  let A := fun i => affineCoordinateAverage c F (epsilonBellFamilies mass R i)
  let J := fun i y => MomentKJet.rescale ρ (parameterCurveKJet (R i) p k y)
  let s := fun t x => ρ * deriv (fun u => affineCoordinateDensityPotential c F (p u,(x,t))) k
  let avg := movingAffineFirstAverage m (c.noise (p k)) (fun y => F (p k,y))
    (c.mean (p k)) (ρ • c.mean (deriv p k)) (c.shift (p k))
    (ρ • c.shift (deriv p k)) (ρ • c.noise (deriv p k)) s
  have HA : ∀ C : ℝ, ∀ q : ℕ, q ≤ 5 → ∀ W : X → MomentKJet,
      MomentKJet.FirstDegreeBound (r + 1) C q W →
        MomentKJet.FirstDegreeBound r (T*C) q (avg W) := by
    intro C q hq W hW
    have H := firstDegreeBound_movingAffineFirstAverage (s := s) hQ hW hL hK
      (show m ∈ Icc (0 : ℝ) 1 from ⟨hm.1.le,hm.2⟩) (c.noise (p k)) hv
      (c.mean (p k)) (ρ • c.mean (deriv p k)) (c.shift (p k))
      (ρ • c.shift (deriv p k)) (ρ • c.noise (deriv p k)) hs (hsj q hq)
    exact H.mono (mul_le_mul_of_nonneg_right (hcoef q hq) hW.value.value.nonneg) le_rfl
  have Hquant := epsilonBellCumulants_first_degree hm hM hδ hT J avg HJ HA
  have hmassSmooth : ParamSmooth mass := (ParamChain.regular_exp_parameter c.logMass).toSmooth
  have hBell := smooth_epsilonBellFamilies hmassSmooth hR
  have hAvg (i : Fin 3) : ParamSmooth (A i) := smooth_affineCoordinateAverage c hF (hBell i)
  have Hslots (i : Fin 3) (y : X) :
      (avg (fun x => epsilonBellTestsKJet m (fun j => J j x) i) y).value =
        (MomentKJet.rescale ρ (parameterCurveKJet (A i) p k y)).value ∧
      (avg (fun x => epsilonBellTestsKJet m (fun j => J j x) i) y).first =
        (MomentKJet.rescale ρ (parameterCurveKJet (A i) p k y)).first := by
    have H := movingAffineFirstAverage_actual_slots c hF (hBell i) (hp k hk) ρ
      (J := fun x => epsilonBellTestsKJet m (fun j => J j x) i)
      (fun x => congrArg MomentKJet.value (parameterCurveKJet_Bell hU hp hR c m hmass hk x ρ i).symm)
      (fun x => congrArg MomentKJet.first (parameterCurveKJet_Bell hU hp hR c m hmass hk x ρ i).symm) y
    simpa only [avg,s,A,parameterCurveKJet,MomentKJet.rescale,hmass k hk] using H
  intro i
  refine (Hquant i).congr ?_ ?_
  · intro y
    rw [parameterCurveKJet_Cumulants hU hp hAvg c m hmass hk y ρ i]
    exact (epsilonLogCumulantsKJet_first_slots_congr m
      (fun j => (Hslots j y).1.symm) (fun j => (Hslots j y).2.symm) i).1
  · intro y
    rw [parameterCurveKJet_Cumulants hU hp hAvg c m hmass hk y ρ i]
    exact (epsilonLogCumulantsKJet_first_slots_congr m
      (fun j => (Hslots j y).1.symm) (fun j => (Hslots j y).2.symm) i).2

end SKBarriers2.Corner
