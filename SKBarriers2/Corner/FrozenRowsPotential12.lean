module

public import SKBarriers2.Corner.FrozenRowsPotential6
public import SKBarriers2.Corner.FrozenRowsMixed6

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.Corner
open StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem qBoundedJets_second_spatial_curve_order {s : ℕ} {B : ℝ} {f : E → ℝ}
    (hf : QPotential (s + 2) B f) {x : ℝ → E} {k : ℝ}
    (hx : ContDiffAt ℝ 2 x k) :
    QBoundedJets s (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖))
      (fun y => deriv (deriv (fun t => f (y + x t))) k) := by
  have heq : (fun y => deriv (deriv (fun t => f (y + x t))) k) = fun y =>
      fderiv ℝ (fderiv ℝ f) (y + x k) (deriv x k) (deriv x k) +
        fderiv ℝ f (y + x k) (deriv (deriv x) k) :=
    funext (second_spatial_curve (hf.smooth.of_le (by exact_mod_cast (show 2 ≤ s + 2 by omega))) hx)
  rw [heq]
  have hH := (((hf.derivativeJets.derivativeJets.apply_const (deriv x k)).apply_const
    (deriv x k)).translate (x k)).add
      (((hf.derivativeJets.of_le (by omega : s ≤ s + 1)).apply_const
        (deriv (deriv x) k)).translate (x k))
  convert hH using 1
  ring

section Chain
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem qBoundedJets_second_fixedMass_moving_exponentialChain
    {s : ℕ} (hs : 1 ≤ s)
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {F : P × E → ℝ}
    (hF : ParamRegular F) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B A H K : ℝ}
    (hbase₁ : QBoundedJets (s + 2) A (fun x => deriv (fun t => F (p t,x)) k))
    (hbase₂ : QBoundedJets s H (fun x => deriv (deriv (fun t => F (p t,x))) k))
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (s + 2) B ≤ K)
    (hMass : massSensitivityJetCoefficient (s + 1) B ≤ K)
    (hDir : directionSensitivityCoefficient (s + 2) B ≤ K)
    (hsource : ∀ A H : ℝ, 0 ≤ A → 0 ≤ H → ∀ v w b : E,
      fixedMassSecondVariationBound s B A H v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * fixedMassSecondVariationSource A v w b)
    (hpotential : ∀ front tail, ps = front ++ tail →
      QPotential (s + 4) B (fun x => ParamChain.exponentialChain tail F (p k,x)))
    (hgeometry : ∀ c ∈ ps, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      B * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2)
    (hfixed : ∀ c ∈ ps, c.1 (deriv p k) = 0 ∧ c.1 (deriv (deriv p) k) = 0) :
    QBoundedJets s
      (movingSecondMajorant A H K (p k) (deriv p k) (deriv (deriv p) k) ps)
      (fun x => deriv (deriv (fun t => ParamChain.exponentialChain ps F (p t,x))) k) := by
  have hp1 := (hp.differentiableAt (by norm_num)).hasDerivAt
  induction ps with
  | nil => exact hbase₂
  | cons c ps ih =>
    have hpotTail : ∀ front tail, ps = front ++ tail →
        QPotential (s + 4) B (fun x => ParamChain.exponentialChain tail F (p k,x)) := by
      intro front tail hsplit
      apply hpotential (c :: front) tail
      simpa only [List.cons_append, List.cons.injEq, true_and] using hsplit
    have hgeoTail : ∀ d ∈ ps, Real.exp (d.1 (p k)) ≤ 1 ∧ ‖d.2 (p k)‖ ≤ 1 ∧
        B * ‖d.2 (p k)‖ ^ 2 ≤ 1 / 2 :=
      fun d hd => hgeometry d (List.mem_cons_of_mem c hd)
    have hfixedTail : ∀ d ∈ ps,
        d.1 (deriv p k) = 0 ∧ d.1 (deriv (deriv p) k) = 0 :=
      fun d hd => hfixed d (List.mem_cons_of_mem c hd)
    have hinner := ih hpotTail hgeoTail hfixedTail
    have hfirst := qBoundedJets_first_moving_exponentialChain (n := s + 1) ps hF hp1
      (by simpa only [Nat.add_assoc] using hbase₁) hK hTilt hMass hDir
      (by simpa only [Nat.add_assoc] using hpotTail) hgeoTail
    let G := ParamChain.exponentialChain ps F
    have hG : ParamRegular G := ParamChain.regular_exponentialChain ps hF
    have hid₁ : (fun y => fderiv ℝ G (p k,y) (deriv p k,0)) =
        fun y => deriv (fun t => G (p t,y)) k := by
      funext y
      exact (((hG.1.differentiable (by norm_num) (p k,y)).hasFDerivAt.comp_hasDerivAt k
        (hp1.prodMk (hasDerivAt_const k y))).deriv).symm
    have hid₂ : (fun y =>
        fderiv ℝ (fderiv ℝ G) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ G (p k,y) (deriv (deriv p) k,0)) =
        fun y => deriv (deriv (fun t => G (p t,y))) k := by
      funext y
      exact (ParamChain.second_parameter_curve hG.1 hp y).symm
    have hg : QBoundedJets (s + 2) (movingFirstMajorant A K (p k) (deriv p k) ps)
        (fun y => fderiv ℝ G (p k,y) (deriv p k,0)) := by
      rw [hid₁]
      simpa only [Nat.add_assoc] using hfirst
    have hh : QBoundedJets s
        (movingSecondMajorant A H K (p k) (deriv p k) (deriv (deriv p) k) ps)
        (fun y => fderiv ℝ (fderiv ℝ G) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ G (p k,y) (deriv (deriv p) k,0)) := by
      rw [hid₂]
      exact hinner
    have hgeo := hgeometry c (List.mem_cons_self ..)
    have hfix := hfixed c (List.mem_cons_self ..)
    have hstep := qBoundedJets_second_deriv_exponential_fixedMassStep_order hs hG c.1 c.2 hp
      ((hpotential [c] ps rfl).of_le (by omega : s + 2 ≤ s + 4)) hg hh
      hfix.1 hfix.2 hgeo.1 hgeo.2.1 hgeo.2.2
    apply hstep.mono
    simpa only [movingSecondMajorant, hfix.1, hfix.2, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add, secondVariationSource, fixedMassSecondVariationSource, abs_zero,
      zero_mul, add_zero] using hsource _ _ hg.nonneg hh.nonneg
      (c.2 (p k)) (c.2 (deriv p k)) (c.2 (deriv (deriv p) k))

end Chain

theorem fixedMassChain_moving_endpoint_jets_order {s n : ℕ} (hs : 1 ≤ s)
    (m : Fin n → ℝ) {v : ℝ → Fin n → E} {x : ℝ → E} {k : ℝ}
    {B K : ℝ} {f : E → ℝ} (hf : QPotential (s + 4) B f)
    (hv : ContDiffAt ℝ 2 v k) (hx : ContDiffAt ℝ 2 x k)
    (hm : ∀ i, 0 < m i ∧ m i ≤ 1)
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient (s + 2) (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient (s + 1) (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient (s + 2) (B + 1) ≤ K)
    (hsource : ∀ A H : ℝ, 0 ≤ A → 0 ≤ H → ∀ v w b : E,
      fixedMassSecondVariationBound s (B + 1) A H v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * fixedMassSecondVariationSource A v w b)
    (hgeometry : ∀ i, ‖v k i‖ ≤ 1 ∧ ‖deriv v k i‖ ≤ 1 ∧
      ‖deriv (deriv v) k i‖ ≤ 1 ∧ (B + 1) * ‖v k i‖ ^ 2 ≤ 1 / 2)
    (hbudget : (stepStabilityCoefficient (s + 4) (B + 1) + 1) *
      StepCalculus.chainEnergy (List.ofFn (fun i => (m i, v k i))) ≤ 1)
    (hcurv : (B + 1) * StepCalculus.chainEnergy (List.ofFn (fun i => (m i, v k i))) ≤ 1 / 2) :
    let F := fun t y => vectorIncrementChain (List.ofFn (fun i => (m i, v t i))) f (y + x t)
    QBoundedJets (s + 2) ((1 + 6 * K) ^ n * (B * ‖deriv x k‖ + 1))
        (fun y => deriv (fun t => F t y) k) ∧
      QBoundedJets s ((1 + 6 * K) ^ (2 * n) *
        (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖) + (B * ‖deriv x k‖ + 1) ^ 2))
        (fun y => deriv (deriv (fun t => F t y)) k) := by
  let P := FixedMassParameters n
  let S : P →L[ℝ] E := (ContinuousLinearMap.snd ℝ (Fin n → E) E).comp
    (ContinuousLinearMap.snd ℝ ℝ ((Fin n → E) × E))
  let p := fixedMassParameterCurve v x
  let cs := fixedMassCoordinateSteps m
  let G : P × E → ℝ := fun z => f (z.2 + S z.1)
  have hG : ParamRegular G := ParamChain.regular_parameterTranslation
    (ParamChain.regular_fixedTerminal hf (by omega) P) S
  obtain ⟨hp, hp₁, hp₂⟩ := fixedMassParameterCurve_jets hv hx
  have hpath (t : ℝ) : ParamChain.exponentialSteps cs (p t) =
      List.ofFn (fun i => (m i, v t i)) := fixedMassCoordinateSteps_apply m v x (fun i => (hm i).1) t
  have hmass : ∀ c ∈ ParamChain.exponentialSteps cs (p k), c.1 ∈ Icc (0 : ℝ) 1 := by
    rw [hpath]
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨(hm i).1.le, (hm i).2⟩
  have hpot : ∀ front tail, cs = front ++ tail →
      QPotential (s + 4) (B + 1) (fun y => ParamChain.exponentialChain tail G (p k,y)) := by
    intro front tail hsplit
    have he : ParamChain.exponentialSteps cs (p k) =
        ParamChain.exponentialSteps front (p k) ++ ParamChain.exponentialSteps tail (p k) := by
      simp only [ParamChain.exponentialSteps, hsplit, List.map_append]
    apply qPotential_chain_tail (ParamChain.exponentialSteps front (p k))
      (ParamChain.exponentialSteps tail (p k)) (hf.translate (x k)) (by omega)
    · rw [← he]; exact hmass
    · rw [← he, hpath]; exact hbudget
    · rw [← he, hpath]; exact hcurv
  have hgeo : ∀ c ∈ cs, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      (B + 1) * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2 := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    change Real.exp (Real.log (m i) * 1) ≤ 1 ∧ ‖v k i‖ ≤ 1 ∧
      (B + 1) * ‖v k i‖ ^ 2 ≤ 1 / 2
    rw [mul_one, Real.exp_log (hm i).1]
    exact ⟨(hm i).2, (hgeometry i).1, (hgeometry i).2.2.2⟩
  have hgeomJets : ∀ c ∈ cs, c.1 (deriv p k) = 0 ∧
      c.1 (deriv (deriv p) k) = 0 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      ‖c.2 (deriv p k)‖ ≤ 1 ∧ ‖c.2 (deriv (deriv p) k)‖ ≤ 1 := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    rw [hp₁, hp₂]
    change Real.log (m i) * 0 = 0 ∧ Real.log (m i) * 0 = 0 ∧
      ‖v k i‖ ≤ 1 ∧ ‖deriv v k i‖ ≤ 1 ∧ ‖deriv (deriv v) k i‖ ≤ 1
    exact ⟨mul_zero _, mul_zero _, (hgeometry i).1, (hgeometry i).2.1, (hgeometry i).2.2.1⟩
  have hbase₁ : QBoundedJets (s + 2) (B * ‖deriv x k‖)
      (fun y => deriv (fun t => G (p t,y)) k) :=
    qBoundedJets_first_spatial_curve (n := s + 2) (hf.of_le (by omega))
      (hx.differentiableAt (by norm_num))
  have hbase₂ : QBoundedJets s (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖))
      (fun y => deriv (deriv (fun t => G (p t,y))) k) :=
    qBoundedJets_second_spatial_curve_order (hf.of_le (by omega : s + 2 ≤ s + 4)) hx
  have hfirst := qBoundedJets_first_moving_exponentialChain (n := s + 1) cs hG
    (hp.differentiableAt (by norm_num)).hasDerivAt
    (by simpa only [Nat.add_assoc] using hbase₁) hK hTilt hMass hDir
    (by simpa only [Nat.add_assoc] using hpot) hgeo
  have hsecond := qBoundedJets_second_fixedMass_moving_exponentialChain hs cs hG hp hbase₁ hbase₂
    hK hTilt hMass hDir hsource hpot hgeo (fun c hc => ⟨(hgeomJets c hc).1, (hgeomJets c hc).2.1⟩)
  have hF (t : ℝ) (y : E) : ParamChain.exponentialChain cs G (p t,y) =
      vectorIncrementChain (List.ofFn (fun i => (m i, v t i))) f (y + x t) := by
    rw [ParamChain.exponentialChain, hpath]
    exact (vectorIncrementChain_translate_argument _ f (x t) y).symm
  have hb₁ : movingFirstMajorant (B * ‖deriv x k‖) K (p k) (deriv p k) cs ≤
      (1 + 6 * K) ^ n * (B * ‖deriv x k‖ + 1) := by
    have H := movingFirstMajorant_length_bound cs hbase₁.nonneg hK (p k) (deriv p k)
      (fun c hc => let h := hgeomJets c hc; ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
    simpa only [cs, fixedMassCoordinateSteps, List.length_ofFn] using H
  have hb₂ : movingSecondMajorant (B * ‖deriv x k‖)
      (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖)) K (p k) (deriv p k)
        (deriv (deriv p) k) cs ≤ (1 + 6 * K) ^ (2 * n) *
          (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖) + (B * ‖deriv x k‖ + 1) ^ 2) := by
    have H := movingSecondMajorant_length_bound cs hbase₁.nonneg hbase₂.nonneg hK
      (p k) (deriv p k) (deriv (deriv p) k) hgeomJets
    simpa only [cs, fixedMassCoordinateSteps, List.length_ofFn] using H
  constructor
  · convert hfirst.mono hb₁ using 1
    funext y
    apply congrArg (fun H : ℝ → ℝ => deriv H k)
    funext t
    exact (hF t y).symm
  · convert hsecond.mono hb₂ using 1
    funext y
    apply congrArg (fun H : ℝ → ℝ => deriv (deriv H) k)
    funext t
    exact (hF t y).symm

end SKBarriers2.Corner
