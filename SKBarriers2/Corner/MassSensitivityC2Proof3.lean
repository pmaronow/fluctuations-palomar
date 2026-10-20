module

public import SKBarriers2.Corner.MassSensitivityC2Proof2
public import SKBarriers2.Analysis.ParamStep4
public import SKBarriers2.Corner.EntropyInputs

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

theorem secondVariationStep_terminal_eq {B A : ℝ} {f g : E → ℝ}
    (hf : QPotential 3 B f) (hg : QBoundedJets 3 A g)
    (m : ℝ) (v : E) (q : E → ℝ) (x : E) :
    secondVariationStep m v f g q 0 0 0 0 x =
      tiltedAverage m v f q x + m * spatialCovariance m v f g g x := by
  have hvar := secondScoreVariance_eq_variance hf hg m 0 v 0 x
  simp only [zero_mul, mul_zero, add_zero, map_zero] at hvar
  have hcov := spatialCovariance_eq hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 1 ≤ 3)))
    (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num : 1 ≤ 3))) m v x
  have hmeas : Measurable (fun t : ℝ => g (x + t • v)) :=
    (hg.smooth.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).measurable
  rw [covariance_self hmeas.aemeasurable] at hcov
  simp only [secondVariationStep, mixedDirectionSource, directionSource,
    map_zero, mul_zero, zero_mul, add_zero, zero_div, zero_pow (by norm_num : 2 ≠ 0),
    sub_zero, tiltedAverage, noiseMean, integral_zero]
  change _ + m * secondScoreVariance m 0 v 0 f g x = _
  rw [hvar, ← hcov]

def terminalSecondGenerator (m : ℝ) (v : E) (f g q : E → ℝ) (x : E) : ℝ :=
  q x + m * fderiv ℝ f x v * fderiv ℝ q x v +
    directionalJet v 2 q x / 2 + m * (fderiv ℝ g x v)^2

theorem abs_secondVariationStep_terminal_remainder_le {B A H : ℝ}
    {f g q : E → ℝ} (hf : QPotential 4 B f)
    (hg : QBoundedJets 4 A g) (hq : QBoundedJets 4 H q)
    {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) (v x : E) (hv : ‖v‖ ≤ 1) :
    |secondVariationStep m v f g q 0 0 0 0 x -
      terminalSecondGenerator m v f g q x| ≤
      (H * pathExpansionConstant B +
        A^2 * (18 * pathExpansionConstant B + (1+B)^4)) * ‖v‖^4 := by
  rw [secondVariationStep_terminal_eq (hf.of_le (by norm_num))
    (hg.of_le (by norm_num))]
  have hlinear := abs_noiseMean_generator_remainder_le hf (by norm_num)
    (qBoundedJets_iff_qBddSmooth.mp hq).potential (by norm_num) hm v x hv
  have hquadratic := abs_spatialCovariance_sub_gradient_le hf le_rfl hg hg hm v x hv
  have hnonneg : 0 ≤ A^2 * (18 * pathExpansionConstant B + (1+B)^4) * ‖v‖^4 := by
    have hP := pathExpansionConstant_nonneg hf.nonneg
    positivity
  have he : tiltedAverage m v f q x + m * spatialCovariance m v f g g x -
      terminalSecondGenerator m v f g q x =
      (tiltedAverage m v f q x - q x -
        m * fderiv ℝ f x v * fderiv ℝ q x v - directionalJet v 2 q x / 2) +
      m * (spatialCovariance m v f g g x - fderiv ℝ g x v * fderiv ℝ g x v) := by
    unfold terminalSecondGenerator
    ring
  rw [he]
  calc
    _ ≤ |tiltedAverage m v f q x - q x -
        m * fderiv ℝ f x v * fderiv ℝ q x v - directionalJet v 2 q x / 2| +
        |m * (spatialCovariance m v f g g x - fderiv ℝ g x v * fderiv ℝ g x v)| :=
      abs_add_le _ _
    _ ≤ H * pathExpansionConstant B * ‖v‖^4 +
        m * (A^2 * (18 * pathExpansionConstant B + (1+B)^4) * ‖v‖^4) := by
      apply add_le_add hlinear
      rw [abs_mul, abs_of_nonneg hm.1]
      apply mul_le_mul_of_nonneg_left _ hm.1
      exact hquadratic.trans_eq (by ring)
    _ ≤ H * pathExpansionConstant B * ‖v‖^4 +
        A^2 * (18 * pathExpansionConstant B + (1+B)^4) * ‖v‖^4 :=
      add_le_add le_rfl (mul_le_of_le_one_left hnonneg hm.2)
    _ = _ := by ring

section ActualTerminalCurve

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem abs_second_deriv_movingStep_terminal_remainder_le
    {F : P × E → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (V : P →L[ℝ] E) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) {B A H : ℝ}
    (hf : QPotential 4 B (fun y => F (p k,y)))
    (hg : QBoundedJets 4 A (fun y => fderiv ℝ F (p k,y) (deriv p k,0)))
    (hq : QBoundedJets 4 H (fun y =>
      fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
        fderiv ℝ F (p k,y) (deriv (deriv p) k,0)))
    (hM : M (deriv p k) = 0) (hMM : M (deriv (deriv p) k) = 0)
    (hV : V (deriv p k) = 0) (hVV : V (deriv (deriv p) k) = 0)
    (hm : Real.exp (M (p k)) ≤ 1) (hv : ‖V (p k)‖ ≤ 1) (x : E) :
    |iteratedDeriv 2 (fun t => vectorStep (Real.exp (M (p t))) (V (p t))
        (fun y => F (p t,y)) x) k -
      terminalSecondGenerator (Real.exp (M (p k))) (V (p k))
        (fun y => F (p k,y)) (fun y => fderiv ℝ F (p k,y) (deriv p k,0))
        (fun y => fderiv ℝ (fderiv ℝ F) (p k,y) (deriv p k,0) (deriv p k,0) +
          fderiv ℝ F (p k,y) (deriv (deriv p) k,0)) x| ≤
      (H * pathExpansionConstant B +
        A^2 * (18 * pathExpansionConstant B + (1+B)^4)) * ‖V (p k)‖^4 := by
  have hd := second_deriv_exponential_movingStep hF M V hp
    (hf.of_le (by norm_num : 3 ≤ 4)) (hg.of_le (by norm_num : 3 ≤ 4))
    (hq.of_le (by norm_num : 1 ≤ 4)) x
  simp only [hM,hMM,hV,hVV,zero_pow (by norm_num : 2 ≠ 0),add_zero,mul_zero] at hd
  rw [iteratedDeriv_succ,iteratedDeriv_one,hd]
  exact abs_secondVariationStep_terminal_remainder_le hf hg hq
    ⟨(Real.exp_pos _).le,hm⟩ (V (p k)) x hv

end ActualTerminalCurve

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

theorem scalarData_window_secondTerminalSource_remainder {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q)
    (hK : KStabilityInputs β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ᶠ N : ℕ in atTop,
        ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap → ∀ x : E,
          let α := cdf (D.μ : Measure ℝ)
          let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
          let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
          let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
          let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
          let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
          |secondVariationStep m v F (G 1) (G 2) 0 0 0 0 x -
            terminalSecondGenerator m v F (G 1) (G 2) x| ≤ K*h^3/(N:ℝ)^2 := by
  let α := cdf (D.μ : Measure ℝ)
  obtain ⟨B,hK0,kapK,hB,hhK,hkapK,hK⟩ := hK
  obtain ⟨A,a0,S,hA0,kapA,hA,ha0,hS,hhA,hkapA,hentropy⟩ :=
    scalarData_uniformWindowEntropyInputs D hl hu
  let P := pathExpansionConstant A
  let Q := 18*P+(1+A)^4
  let K := (B*P+B^2*Q)*S^2
  have hP : 0 ≤ P := pathExpansionConstant_nonneg hA
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hKnonneg : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K,min hK0 (min hA0 1),min kapK kapA,hKnonneg,
    lt_min hhK (lt_min hhA (by norm_num)),lt_min hkapK hkapA,?_⟩
  intro r hr h hh hh0
  have hhK' : h ≤ hK0 := hh0.trans (min_le_left _ _)
  have hhA' : h ≤ hA0 := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlim : Tendsto (fun N : ℕ => S*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))] with N hN hsmall
  intro lam hlam j k hk x
  dsimp only
  let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
  let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
  let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
  let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
  let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
  obtain ⟨_,hentropyN⟩ := hentropy r hr h hh hhA' k
    (hk.trans (min_le_right _ _)) N hN
  obtain ⟨hinner,hentry⟩ := hentropyN lam hlam
  have hF : QPotential 4 A F := by
    simpa only [F,orderedInnerChain,massPath,List.map_drop,jj,windowEntryIndex] using
      (hinner jj.val jj.isLt).of_le (by norm_num : 4 ≤ 10)
  have hm : m ∈ Icc (0:ℝ) 1 :=
    ⟨ha0.le.trans (hentry jj).1.1,(hentry jj).1.2⟩
  have hdir : ‖v‖^2 ≤ S*h/(N:ℝ) := (hentry jj).2
  have hv : ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v]
  have hv4 : ‖v‖^4 ≤ (S*h/(N:ℝ))^2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hdir 2
  have hjets := (hK r hr h hh hhK' N hN lam hlam).1
  have hG (c : ℕ) (hc : c=1 ∨ c=2) : QBoundedJets 4 (B*h) (G c) := by
    exact qBoundedJets_iff_qBddSmooth.mpr
      ((hjets k (hk.trans (min_le_left _ _)) jj.val jj.isLt c hc).of_le (by norm_num : 4 ≤ 8))
  have H := abs_secondVariationStep_terminal_remainder_le hF (hG 1 (Or.inl rfl))
    (hG 2 (Or.inr rfl)) hm v x hv
  change |secondVariationStep m v F (G 1) (G 2) 0 0 0 0 x -
    terminalSecondGenerator m v F (G 1) (G 2) x| ≤ K*h^3/(N:ℝ)^2
  calc
    _ ≤ ((B*h)*P+(B*h)^2*Q)*‖v‖^4 := H
    _ ≤ ((B*h)*P+(B*h)^2*Q)*(S*h/(N:ℝ))^2 :=
      mul_le_mul_of_nonneg_left hv4 (by positivity)
    _ = ((B*P)*S^2*h^3+(B^2*Q)*S^2*h^4)/(N:ℝ)^2 := by ring
    _ ≤ ((B*P)*S^2*h^3+(B^2*Q)*S^2*h^3)/(N:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ B^2*Q*S^2)
      calc
        h^4 = h^3*h := by ring
        _ ≤ h^3 := mul_le_of_le_one_right (pow_nonneg hh.le 3) hh1
    _ = _ := by dsimp only [K]; ring

end SKBarriers2.Corner
