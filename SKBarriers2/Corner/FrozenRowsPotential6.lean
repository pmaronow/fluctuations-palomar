module

public import SKBarriers2.Corner.FrozenRowsPotential4
public import SKBarriers2.Corner.FrozenRowsNoiseCore

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.Corner
open StepCalculus

local notation "E" => (Fin 3 → ℝ)

abbrev FixedMassParameters (n : ℕ) := ℝ × ((Fin n → E) × E)

def fixedMassParameterCurve {n : ℕ} (v : ℝ → Fin n → E) (x : ℝ → E)
    (k : ℝ) : FixedMassParameters n := (1, (v k, x k))

def fixedMassCoordinateSteps {n : ℕ} (m : Fin n → ℝ) :
    List ((FixedMassParameters n →L[ℝ] ℝ) × (FixedMassParameters n →L[ℝ] E)) :=
  List.ofFn (fun i =>
    ((Real.log (m i)) • ContinuousLinearMap.fst ℝ ℝ ((Fin n → E) × E),
      (ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.fst ℝ (Fin n → E) E).comp
          (ContinuousLinearMap.snd ℝ ℝ ((Fin n → E) × E)))))

theorem fixedMassParameterCurve_jets {n : ℕ} {v : ℝ → Fin n → E}
    {x : ℝ → E} {k : ℝ} (hv : ContDiffAt ℝ 2 v k) (hx : ContDiffAt ℝ 2 x k) :
    ContDiffAt ℝ 2 (fixedMassParameterCurve v x) k ∧
      deriv (fixedMassParameterCurve v x) k = (0, (deriv v k, deriv x k)) ∧
      deriv (deriv (fixedMassParameterCurve v x)) k =
        (0, (deriv (deriv v) k, deriv (deriv x) k)) := by
  have hd := (hv.differentiableAt (by norm_num)).hasDerivAt
  have he := (hx.differentiableAt (by norm_num)).hasDerivAt
  have hdd := ((hv.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hee := ((hx.derivWithin (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hfirst := ((hasDerivAt_const k (1 : ℝ)).prodMk (hd.prodMk he)).deriv
  have hnear : deriv (fixedMassParameterCurve v x) =ᶠ[𝓝 k]
      fun t => (0, (deriv v t, deriv x t)) := by
    filter_upwards [hv.eventually (by norm_num), hx.eventually (by norm_num)] with t hvt hxt
    exact ((hasDerivAt_const t (1 : ℝ)).prodMk
      (((hvt.differentiableAt (by norm_num)).hasDerivAt).prodMk
        ((hxt.differentiableAt (by norm_num)).hasDerivAt))).deriv
  refine ⟨contDiffAt_const.prodMk (hv.prodMk hx), hfirst, ?_⟩
  rw [hnear.deriv_eq]
  exact ((hasDerivAt_const k (0 : ℝ)).prodMk (hdd.prodMk hee)).deriv

theorem fixedMassCoordinateSteps_apply {n : ℕ} (m : Fin n → ℝ)
    (v : ℝ → Fin n → E) (x : ℝ → E) (hm : ∀ i, 0 < m i) (k : ℝ) :
    ParamChain.exponentialSteps (fixedMassCoordinateSteps m) (fixedMassParameterCurve v x k) =
      List.ofFn (fun i => (m i, v k i)) := by
  simp only [ParamChain.exponentialSteps, fixedMassCoordinateSteps, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change (Real.exp (Real.log (m i) * 1), v k i) = _
  rw [mul_one, Real.exp_log (hm i)]

theorem fixedMassChain_moving_endpoint_contDiffAt {n : ℕ} (m : Fin n → ℝ)
    {v : ℝ → Fin n → E} {x : ℝ → E} {k B : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (hv : ContDiffAt ℝ 2 v k) (hx : ContDiffAt ℝ 2 x k)
    (hm : ∀ i, 0 < m i) :
    ContDiffAt ℝ 2 (fun t => vectorIncrementChain
      (List.ofFn (fun i => (m i, v t i))) f (x t)) k := by
  let ps : List (ℝ → ℝ × E) := List.ofFn (fun i t => (m i, v t i))
  have hreg : ∀ c ∈ ps, ContDiffAt ℝ 2 c k := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact contDiffAt_const.prodMk ((contDiffAt_pi.mp hv) i)
  have hmass : ∀ c ∈ ps, 0 < (c k).1 := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact hm i
  have H := (ParamChain.contDiffAt_curveChain ps hf (by norm_num) hreg hmass (x k)).comp k
    (contDiffAt_id.prodMk hx)
  simpa only [ps, List.map_ofFn, Function.comp_def, id_eq] using H

theorem fixedMassChain_moving_endpoint_jets {n : ℕ} (m : Fin n → ℝ)
    {v : ℝ → Fin n → E} {x : ℝ → E} {k : ℝ} {B R K : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (hv : ContDiffAt ℝ 2 v k) (hx : ContDiffAt ℝ 2 x k)
    (hm : ∀ i, 0 < m i ∧ m i ≤ 1 ∧ (m i)⁻¹ ≤ R)
    (hK : 0 ≤ K) (hTilt : tiltedStabilityCoefficient 3 (B + 1) ≤ K)
    (hMass : massSensitivityJetCoefficient 2 (B + 1) ≤ K)
    (hDir : directionSensitivityCoefficient 3 (B + 1) ≤ K)
    (hsource : ∀ A H m dm ddm : ℝ, 0 ≤ A → 0 ≤ H → 0 < m → m⁻¹ ≤ R →
      ∀ v w b : E, secondVariationBound (B + 1) A H m dm ddm v w b ≤
        (1 + K * ‖v‖ ^ 2) * H + K * secondVariationSource A dm ddm v w b)
    (hgeometry : ∀ i, ‖v k i‖ ≤ 1 ∧ ‖deriv v k i‖ ≤ 1 ∧
      ‖deriv (deriv v) k i‖ ≤ 1 ∧ (B + 1) * ‖v k i‖ ^ 2 ≤ 1 / 2)
    (hbudget : (stepStabilityCoefficient 5 (B + 1) + 1) *
      StepCalculus.chainEnergy (List.ofFn (fun i => (m i, v k i))) ≤ 1)
    (hcurv : (B + 1) * StepCalculus.chainEnergy (List.ofFn (fun i => (m i, v k i))) ≤ 1 / 2) :
    let F := fun t y => vectorIncrementChain (List.ofFn (fun i => (m i, v t i))) f (y + x t)
    QBoundedJets 3 ((1 + 6 * K) ^ n * (B * ‖deriv x k‖ + 1))
        (fun y => deriv (fun t => F t y) k) ∧
      QBoundedJets 1 ((1 + 6 * K) ^ (2 * n) *
        (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖) + (B * ‖deriv x k‖ + 1) ^ 2))
        (fun y => deriv (deriv (fun t => F t y)) k) := by
  let P := FixedMassParameters n
  let S : P →L[ℝ] E := (ContinuousLinearMap.snd ℝ (Fin n → E) E).comp
    (ContinuousLinearMap.snd ℝ ℝ ((Fin n → E) × E))
  let p := fixedMassParameterCurve v x
  let cs := fixedMassCoordinateSteps m
  let G : P × E → ℝ := fun z => f (z.2 + S z.1)
  have hG : ParamRegular G := ParamChain.regular_parameterTranslation
    (ParamChain.regular_fixedTerminal hf (by norm_num) P) S
  obtain ⟨hp, hp₁, hp₂⟩ := fixedMassParameterCurve_jets hv hx
  have hpath (t : ℝ) : ParamChain.exponentialSteps cs (p t) =
      List.ofFn (fun i => (m i, v t i)) := fixedMassCoordinateSteps_apply m v x (fun i => (hm i).1) t
  have hmass : ∀ c ∈ ParamChain.exponentialSteps cs (p k), c.1 ∈ Icc (0 : ℝ) 1 := by
    rw [hpath]
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact ⟨(hm i).1.le, (hm i).2.1⟩
  have hpot : ∀ front tail, cs = front ++ tail →
      QPotential 5 (B + 1) (fun y => ParamChain.exponentialChain tail G (p k,y)) := by
    intro front tail hsplit
    have hs : ParamChain.exponentialSteps cs (p k) =
        ParamChain.exponentialSteps front (p k) ++ ParamChain.exponentialSteps tail (p k) := by
      simp only [ParamChain.exponentialSteps, hsplit, List.map_append]
    apply qPotential_chain_tail (ParamChain.exponentialSteps front (p k))
      (ParamChain.exponentialSteps tail (p k)) (hf.translate (x k)) (by norm_num)
    · rw [← hs]; exact hmass
    · rw [← hs, hpath]; exact hbudget
    · rw [← hs, hpath]; exact hcurv
  have hgeo : ∀ c ∈ cs, Real.exp (c.1 (p k)) ≤ 1 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      (B + 1) * ‖c.2 (p k)‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (c.1 (p k)))⁻¹ ≤ R := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    change Real.exp (Real.log (m i) * 1) ≤ 1 ∧ ‖v k i‖ ≤ 1 ∧
      (B + 1) * ‖v k i‖ ^ 2 ≤ 1 / 2 ∧ (Real.exp (Real.log (m i) * 1))⁻¹ ≤ R
    rw [mul_one, Real.exp_log (hm i).1]
    exact ⟨(hm i).2.1, (hgeometry i).1, (hgeometry i).2.2.2, (hm i).2.2⟩
  have hgeomJets : ∀ c ∈ cs, c.1 (deriv p k) = 0 ∧
      c.1 (deriv (deriv p) k) = 0 ∧ ‖c.2 (p k)‖ ≤ 1 ∧
      ‖c.2 (deriv p k)‖ ≤ 1 ∧ ‖c.2 (deriv (deriv p) k)‖ ≤ 1 := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    rw [hp₁, hp₂]
    change Real.log (m i) * 0 = 0 ∧ Real.log (m i) * 0 = 0 ∧
      ‖v k i‖ ≤ 1 ∧ ‖deriv v k i‖ ≤ 1 ∧ ‖deriv (deriv v) k i‖ ≤ 1
    exact ⟨mul_zero _, mul_zero _, (hgeometry i).1, (hgeometry i).2.1, (hgeometry i).2.2.1⟩
  have hbase₁ : QBoundedJets 3 (B * ‖deriv x k‖)
      (fun y => deriv (fun t => G (p t,y)) k) :=
    qBoundedJets_first_spatial_curve (hf.of_le (by norm_num : 4 ≤ 5))
      (hx.differentiableAt (by norm_num))
  have hbase₂ : QBoundedJets 1 (B * (‖deriv x k‖ ^ 2 + ‖deriv (deriv x) k‖))
      (fun y => deriv (deriv (fun t => G (p t,y))) k) :=
    qBoundedJets_second_spatial_curve (hf.of_le (by norm_num : 3 ≤ 5)) hx
  have hfirst := qBoundedJets_first_moving_exponentialChain cs hG
    (hp.differentiableAt (by norm_num)).hasDerivAt hbase₁ hK hTilt hMass hDir hpot
    (fun c hc => ⟨(hgeo c hc).1, (hgeo c hc).2.1, (hgeo c hc).2.2.1⟩)
  have hsecond := qBoundedJets_second_moving_exponentialChain cs hG hp hbase₁ hbase₂
    hK hTilt hMass hDir hsource hpot hgeo
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
