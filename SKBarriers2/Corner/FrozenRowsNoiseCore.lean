module

public import SKBarriers2.Corner.FrozenRowsQR
public import SKBarriers2.Analysis.ParamChain

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

structure QuadraticFamilyContDiffAt {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (Q : P → QuadraticTerminal) (p : P) : Prop where
  constant : ContDiffAt ℝ ∞ (fun q => (Q q).constant) p
  linear : ∀ i, ContDiffAt ℝ ∞ (fun q => (Q q).linear i) p
  hessian : ∀ i j, ContDiffAt ℝ ∞ (fun q => (Q q).hessian i j) p

namespace QuadraticFamilyContDiffAt

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {Q : P → QuadraticTerminal} {p : P}

theorem const (Q : QuadraticTerminal) (p : P) :
    QuadraticFamilyContDiffAt (fun _ : P => Q) p :=
  ⟨contDiffAt_const, fun _ => contDiffAt_const, fun _ _ => contDiffAt_const⟩

theorem hessianDirection (hQ : QuadraticFamilyContDiffAt Q p)
    {v : P → Vec3} (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => (Q q).hessianDirection (v q) i) p := by
  exact ContDiffAt.sum (fun j _ => (hQ.hessian i j).mul (hv j))

theorem linearDirection (hQ : QuadraticFamilyContDiffAt Q p)
    {v : P → Vec3} (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p) :
    ContDiffAt ℝ ∞ (fun q => (Q q).linearDirection (v q)) p := by
  exact ContDiffAt.sum (fun j _ => (hQ.linear j).mul (hv j))

theorem precision (hQ : QuadraticFamilyContDiffAt Q p)
    {m : P → ℝ} {v : P → Vec3} (hm : ContDiffAt ℝ ∞ m p)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p) :
    ContDiffAt ℝ ∞ (fun q => (Q q).precision (m q) (v q)) p := by
  exact contDiffAt_const.sub
    (hm.mul (ContDiffAt.sum (fun i _ => (hv i).mul (hQ.hessianDirection hv i))))

theorem update (hQ : QuadraticFamilyContDiffAt Q p)
    {m : P → ℝ} {v : P → Vec3} (hm : ContDiffAt ℝ ∞ m p)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p)
    (hm0 : m p ≠ 0) (hP : 0 < (Q p).precision (m p) (v p)) :
    QuadraticFamilyContDiffAt (fun q => (Q q).update (m q) (v q)) p := by
  have hD := hQ.precision hm hv
  have hL := hQ.linearDirection hv
  have hH := hQ.hessianDirection hv
  constructor
  · exact (hQ.constant.sub ((hD.log (ne_of_gt hP)).div
      (contDiffAt_const.mul hm) (mul_ne_zero (by norm_num) hm0))).add
      ((hm.mul (hL.pow 2)).div (contDiffAt_const.mul hD)
        (mul_ne_zero (by norm_num) (ne_of_gt hP)))
  · intro i
    exact (hQ.linear i).add (((hm.div hD (ne_of_gt hP)).mul hL).mul (hH i))
  · intro i j
    exact (hQ.hessian i j).add (((hm.div hD (ne_of_gt hP)).mul (hH i)).mul (hH j))

theorem value (hQ : QuadraticFamilyContDiffAt Q p)
    {x : P → Vec3} (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p) :
    ContDiffAt ℝ ∞ (fun q => (Q q).value (x q)) p := by
  exact (hQ.constant.add (ContDiffAt.sum (fun i _ => (hQ.linear i).mul (hx i)))).add
    (contDiffAt_const.mul (ContDiffAt.sum (fun i _ =>
      ContDiffAt.sum (fun j _ => ((hx i).mul (hQ.hessian i j)).mul (hx j)))))

end QuadraticFamilyContDiffAt

theorem riccatiRecursion_coefficients_contDiffAt {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (l : List ι) (m : ι → P → ℝ) (v : ι → P → Vec3)
    (Q : P → QuadraticTerminal) {p : P}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun q => v j q i) p)
    (hQ : QuadraticFamilyContDiffAt Q p)
    (hA : RiccatiAdmissible (l.map (fun j => (m j p, v j p))) (Q p)) :
    QuadraticFamilyContDiffAt
      (fun q => riccatiRecursion (l.map (fun j => (m j q, v j q))) (Q q)) p := by
  induction l with
  | nil => exact hQ
  | cons j l ih =>
    exact (ih (fun i hi => hm i (List.mem_cons_of_mem _ hi))
      (fun i hi => hv i (List.mem_cons_of_mem _ hi)) hA.1).update
      (hm j List.mem_cons_self) (hv j List.mem_cons_self) hA.2.1 hA.2.2

namespace QuadraticFamilyContDiffAt

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {Q : P → QuadraticTerminal} {p : P}

theorem noiseDirection (hQ : QuadraticFamilyContDiffAt Q p)
    {m : P → ℝ} {v : P → Vec3} (hm : ContDiffAt ℝ ∞ m p)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p)
    (hP : 0 < (Q p).precision (m p) (v p)) :
    ∀ i, ContDiffAt ℝ ∞
      (fun q => ((Real.sqrt (((Q q).precision (m q) (v q))⁻¹)) • v q) i) p := by
  have hD := hQ.precision hm hv
  have hS := (hD.inv (ne_of_gt hP)).sqrt (inv_ne_zero (ne_of_gt hP))
  intro i
  exact hS.mul (hv i)

theorem noiseConstant (hQ : QuadraticFamilyContDiffAt Q p)
    {m : P → ℝ} {v : P → Vec3} (hm : ContDiffAt ℝ ∞ m p)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p)
    (hP : 0 < (Q p).precision (m p) (v p)) :
    ∀ i, ContDiffAt ℝ ∞
      (fun q => quadraticNoiseConstant (Q q) (m q) (v q) i) p := by
  intro i
  exact (((hm.mul (hQ.linearDirection hv)).div (hQ.precision hm hv)
    (ne_of_gt hP)).mul (hv i))

theorem meanTransition (hQ : QuadraticFamilyContDiffAt Q p)
    {m : P → ℝ} {v x : P → Vec3} (hm : ContDiffAt ℝ ∞ m p)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p)
    (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p)
    (hP : 0 < (Q p).precision (m p) (v p)) :
    ∀ i, ContDiffAt ℝ ∞
      (fun q => quadraticMeanTransition (Q q) (m q) (v q) (x q) i) p := by
  have hS : ContDiffAt ℝ ∞ (fun q => (Q q).slope (v q) (x q)) p :=
    (hQ.linearDirection hv).add
      (ContDiffAt.sum (fun i _ => (hx i).mul (hQ.hessianDirection hv i)))
  intro i
  exact (hx i).add (((hm.mul hS).div (hQ.precision hm hv) (ne_of_gt hP)).mul (hv i))

theorem meanLinear (hQ : QuadraticFamilyContDiffAt Q p)
    {m : P → ℝ} {v : P → Vec3} (hm : ContDiffAt ℝ ∞ m p)
    (hv : ∀ i, ContDiffAt ℝ ∞ (fun q => v q i) p)
    (hP : 0 < (Q p).precision (m p) (v p)) :
    ContDiffAt ℝ ∞ (fun q => quadraticMeanLinear (Q q) (m q) (v q)) p := by
  change ContDiffWithinAt ℝ ∞ _ univ p
  apply contDiffWithinAt_clm_apply.mpr
  intro x
  apply contDiffWithinAt_pi.mpr
  intro i
  have heq : (fun q => quadraticMeanLinear (Q q) (m q) (v q) x i) =
      fun q => quadraticMeanTransition (Q q) (m q) (v q) x i -
        quadraticNoiseConstant (Q q) (m q) (v q) i := by
    funext q
    have H := congrArg (fun y : Vec3 => y i)
      (quadraticMeanTransition_eq_affine (Q q) (m q) (v q) x)
    change quadraticMeanTransition (Q q) (m q) (v q) x i =
      quadraticMeanLinear (Q q) (m q) (v q) x i +
        quadraticNoiseConstant (Q q) (m q) (v q) i at H
    linarith
  rw [heq]
  exact ((hQ.meanTransition (x := fun _ => x) hm hv (fun _ => contDiffAt_const) hP i).sub
    (hQ.noiseConstant hm hv hP i)).contDiffWithinAt

end QuadraticFamilyContDiffAt

theorem gaussianPathMean_contDiffAt {P ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (l : List ι) (m : ι → P → ℝ) (v : ι → P → Vec3)
    (Q : P → QuadraticTerminal) {p : P}
    (hm : ∀ j ∈ l, ContDiffAt ℝ ∞ (m j) p)
    (hv : ∀ j ∈ l, ∀ i, ContDiffAt ℝ ∞ (fun q => v j q i) p)
    (hQ : QuadraticFamilyContDiffAt Q p)
    (hA : RiccatiAdmissible (l.map (fun j => (m j p, v j p))) (Q p))
    (x : P → Vec3) (hx : ∀ i, ContDiffAt ℝ ∞ (fun q => x q i) p) :
    ∀ i, ContDiffAt ℝ ∞
      (fun q => gaussianPathMean (l.map (fun j => (m j q, v j q))) (Q q) (x q) i) p := by
  induction l generalizing x with
  | nil => exact hx
  | cons j l ih =>
    have hmt := fun i hi => hm i (List.mem_cons_of_mem _ hi)
    have hvt := fun i hi => hv i (List.mem_cons_of_mem _ hi)
    have hR := riccatiRecursion_coefficients_contDiffAt l m v Q hmt hvt hQ hA.1
    exact ih hmt hvt hA.1 _
      (hR.meanTransition (hm j List.mem_cons_self) (hv j List.mem_cons_self) hx hA.2.2)

end SKBarriers2.Corner

namespace SKBarriers2.ParamChain

section AffineParameters

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem growth_parameterTranslation {Y : Type} [Norm Y] {f : P × X → Y}
    (hf : ParamExpGrowth f) (B : P →L[ℝ] X) :
    ParamExpGrowth (fun z : P × X => f (z.1, z.2 + B z.1)) := by
  intro R
  obtain ⟨C, M, hC, hM, hb⟩ := hf R
  let D : ℝ := ‖B‖ * max R 0
  refine ⟨C * Real.exp (M * D), M, by positivity, hM, ?_⟩
  intro p x hp
  have hBp : ‖B p‖ ≤ D := (B.le_opNorm p).trans
    (mul_le_mul_of_nonneg_left (hp.trans (le_max_left _ _)) (norm_nonneg B))
  calc
    _ ≤ C * Real.exp (M * ‖x + B p‖) := hb p _ hp
    _ ≤ C * Real.exp (M * (‖x‖ + D)) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add le_rfl hBp)
    _ = _ := by rw [mul_add, Real.exp_add]; ring

theorem smooth_parameterTranslation {f : P × X → ℝ} (hf : ParamSmooth f)
    (B : P →L[ℝ] X) :
    ParamSmooth (fun z : P × X => f (z.1, z.2 + B z.1)) := by
  let A : P × X →L[ℝ] P × X := (ContinuousLinearMap.fst ℝ P X).prod
    ((ContinuousLinearMap.snd ℝ P X) + B.comp (ContinuousLinearMap.fst ℝ P X))
  exact ⟨hf.1.comp A.contDiff, growth_parameterTranslation hf.2.1 B,
    param_fderiv_compCLM_growth f A id (hf.1.differentiable (by norm_num))
      (growth_parameterTranslation hf.2.2.1 B),
    param_second_compCLM_growth f A id hf.1 (growth_parameterTranslation hf.2.2.2 B)⟩

theorem regular_parameterTranslation {f : P × X → ℝ} (hf : ParamRegular f)
    (B : P →L[ℝ] X) :
    ParamRegular (fun z : P × X => f (z.1, z.2 + B z.1)) := by
  have hS := smooth_parameterTranslation hf.toSmooth B
  refine ⟨hS.1, ?_, hS.2.2⟩
  intro R
  obtain ⟨C, hC, hb⟩ := hf.2.1 R
  let D : ℝ := ‖B‖ * max R 0
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨C * (1 + D), by positivity, ?_⟩
  intro p x hp
  have hBp : ‖B p‖ ≤ D := (B.le_opNorm p).trans
    (mul_le_mul_of_nonneg_left (hp.trans (le_max_left _ _)) (norm_nonneg B))
  have hx := norm_add_le x (B p)
  exact (hb p _ hp).trans (by
    nlinarith [mul_le_mul_of_nonneg_left (hx.trans (add_le_add le_rfl hBp)) hC,
      mul_nonneg (mul_nonneg hC hD) (norm_nonneg x)])

theorem regular_movingAffineStep {F : P × X → ℝ} (hF : ParamRegular F)
    (M : P →L[ℝ] ℝ) (A : P →L[ℝ] X →L[ℝ] X)
    (B V : P →L[ℝ] X) :
    ParamRegular (fun z : P × X => vectorStep (Real.exp (M z.1)) (V z.1)
      (fun y => F (z.1, y)) (A z.1 z.2 + B z.1)) := by
  simpa only [zero_apply, zero_add] using regular_affineBilinear
    (regular_parameterTranslation (regular_movingStep hF M V) B) 0 A

theorem smooth_movingAffineAverage {F G : P × X → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (M : P →L[ℝ] ℝ) (A : P →L[ℝ] X →L[ℝ] X)
    (B V : P →L[ℝ] X) :
    ParamSmooth (fun z : P × X => vectorStepAverage (Real.exp (M z.1)) (V z.1)
      (fun y => F (z.1, y)) (fun y => G (z.1, y)) (A z.1 z.2 + B z.1)) := by
  simpa only [zero_apply, zero_add] using smooth_affineBilinear
    (smooth_parameterTranslation (smooth_movingAverage hF hG M V) B) 0 A

end AffineParameters

end SKBarriers2.ParamChain
