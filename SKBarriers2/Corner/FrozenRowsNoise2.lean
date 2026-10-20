module

public import SKBarriers2.Corner.FrozenRowsNoiseCore

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

section AffineCumulants

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

structure AffineGaussianCoordinate (P X : Type) [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] where
  logMass : P →L[ℝ] ℝ
  mean : P →L[ℝ] X →L[ℝ] X
  shift : P →L[ℝ] X
  noise : P →L[ℝ] X

def affinePotentialChain : List (AffineGaussianCoordinate P X) →
    (P × X → ℝ) → P × X → ℝ
  | [], F => F
  | c :: cs, F => fun z => vectorStep (Real.exp (c.logMass z.1)) (c.noise z.1)
      (fun y => affinePotentialChain cs F (z.1, y)) (c.mean z.1 z.2 + c.shift z.1)

theorem regular_affinePotentialChain (cs : List (AffineGaussianCoordinate P X))
    {F : P × X → ℝ} (hF : ParamRegular F) : ParamRegular (affinePotentialChain cs F) := by
  induction cs with
  | nil => exact hF
  | cons c cs ih =>
    exact ParamChain.regular_movingAffineStep ih c.logMass c.mean c.shift c.noise

def affineCoordinateAverage (c : AffineGaussianCoordinate P X) (F G : P × X → ℝ)
    (z : P × X) : ℝ :=
  vectorStepAverage (Real.exp (c.logMass z.1)) (c.noise z.1)
    (fun y => F (z.1, y)) (fun y => G (z.1, y)) (c.mean z.1 z.2 + c.shift z.1)

theorem smooth_affineCoordinateAverage (c : AffineGaussianCoordinate P X)
    {F G : P × X → ℝ} (hF : ParamRegular F) (hG : ParamSmooth G) :
    ParamSmooth (affineCoordinateAverage c F G) :=
  ParamChain.smooth_movingAffineAverage hF hG c.logMass c.mean c.shift c.noise

def epsilonBellFamilies (m : P × X → ℝ) (R : Fin 3 → P × X → ℝ) :
    Fin 3 → P × X → ℝ :=
  ![R 0, (fun z => R 1 z + m z * R 0 z ^ 2),
    (fun z => R 2 z + 3 * m z * R 0 z * R 1 z + m z ^ 2 * R 0 z ^ 3)]

def epsilonCumulantFamilies (m : P × X → ℝ) (A : Fin 3 → P × X → ℝ) :
    Fin 3 → P × X → ℝ :=
  ![A 0, (fun z => A 1 z - m z * A 0 z ^ 2),
    (fun z => A 2 z - 3 * m z * A 0 z * A 1 z + 2 * m z ^ 2 * A 0 z ^ 3)]

private theorem smooth_pow {f : P × X → ℝ} (hf : ParamSmooth f) (n : ℕ) :
    ParamSmooth (fun z => f z ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (paramSmooth_const (P := P) (E := X) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private theorem smooth_sub {f g : P × X → ℝ} (hf : ParamSmooth f) (hg : ParamSmooth g) :
    ParamSmooth (fun z => f z - g z) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hg.const_mul (-1))

theorem smooth_epsilonBellFamilies {m : P × X → ℝ} {R : Fin 3 → P × X → ℝ}
    (hm : ParamSmooth m) (hR : ∀ i, ParamSmooth (R i)) :
    ∀ i, ParamSmooth (epsilonBellFamilies m R i) := by
  intro i
  fin_cases i
  · exact hR 0
  · exact (hR 1).add (hm.mul (smooth_pow (hR 0) 2))
  · exact ((hR 2).add (((hm.const_mul 3).mul (hR 0)).mul (hR 1))).add
      ((smooth_pow hm 2).mul (smooth_pow (hR 0) 3))

theorem smooth_epsilonCumulantFamilies {m : P × X → ℝ} {A : Fin 3 → P × X → ℝ}
    (hm : ParamSmooth m) (hA : ∀ i, ParamSmooth (A i)) :
    ∀ i, ParamSmooth (epsilonCumulantFamilies m A i) := by
  intro i
  fin_cases i
  · exact hA 0
  · exact smooth_sub (hA 1) (hm.mul (smooth_pow (hA 0) 2))
  · exact (smooth_sub (hA 2) (((hm.const_mul 3).mul (hA 0)).mul (hA 1))).add
      (((smooth_pow hm 2).const_mul 2).mul (smooth_pow (hA 0) 3))

def affineEpsilonJetChain : List (AffineGaussianCoordinate P X) →
    (P × X → ℝ) → (P × X → ℝ) → Fin 3 → P × X → ℝ
  | [], _, K => ![K, fun _ => 0, fun _ => 0]
  | c :: cs, F, K =>
      let R := affineEpsilonJetChain cs F K
      let m := fun z : P × X => Real.exp (c.logMass z.1)
      let A := fun i => affineCoordinateAverage c (affinePotentialChain cs F)
        (epsilonBellFamilies m R i)
      epsilonCumulantFamilies m A

theorem smooth_affineEpsilonJetChain (cs : List (AffineGaussianCoordinate P X))
    {F K : P × X → ℝ} (hF : ParamRegular F) (hK : ParamSmooth K) :
    ∀ i, ParamSmooth (affineEpsilonJetChain cs F K i) := by
  induction cs with
  | nil =>
    intro i
    fin_cases i
    · exact hK
    · exact paramSmooth_const 0
    · exact paramSmooth_const 0
  | cons c cs ih =>
    have hm : ParamSmooth (fun z : P × X => Real.exp (c.logMass z.1)) :=
      (ParamChain.regular_exp_parameter c.logMass).toSmooth
    have hT := regular_affinePotentialChain cs hF
    have hB := smooth_epsilonBellFamilies hm ih
    exact smooth_epsilonCumulantFamilies hm (fun i =>
      smooth_affineCoordinateAverage c hT (hB i))

end AffineCumulants

section Terminal

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem smooth_fieldCLM (L : Vec3 →L[ℝ] ℝ) :
    ParamSmooth (fun z : P × Vec3 => L z.2) := by
  let A : P × Vec3 →L[ℝ] ℝ := L.comp (ContinuousLinearMap.snd ℝ P Vec3)
  have hD : fderiv ℝ (fun z : P × Vec3 => L z.2) = fun _ => A :=
    funext (fun z => A.fderiv)
  refine ⟨A.contDiff, ParamExpGrowth.continuousLinearMap A, ?_, ?_⟩
  · rw [hD]
    exact ParamExpGrowth.of_bounded (norm_nonneg A) (fun _ => le_rfl)
  · rw [hD]
    have hDD : fderiv ℝ (fun _ : P × Vec3 => A) =
        fun _ => (0 : P × Vec3 →L[ℝ] P × Vec3 →L[ℝ] ℝ) :=
      funext (fun _ => fderiv_const_apply A)
    rw [hDD]
    exact ParamExpGrowth.of_bounded
      (f := fun _ : P × Vec3 => (0 : P × Vec3 →L[ℝ] P × Vec3 →L[ℝ] ℝ)) (C := 0) le_rfl
      (fun _ => le_of_eq ContinuousLinearMap.opNorm_zero)

theorem smooth_quadraticValue (Q : QuadraticTerminal) :
    ParamSmooth (fun z : P × Vec3 => Q.value z.2) := by
  have hc (i : Fin 3) : ParamSmooth (fun z : P × Vec3 => z.2 i) :=
    smooth_fieldCLM (ContinuousLinearMap.proj i)
  exact ((paramSmooth_const Q.constant).add
    (ParamSmooth.sum Finset.univ (fun (i : Fin 3) (z : P × Vec3) => Q.linear i * z.2 i)
      (fun i _ => (hc i).const_mul (Q.linear i)))).add
    ((ParamSmooth.sum Finset.univ (fun (i : Fin 3) (z : P × Vec3) => ∑ j : Fin 3,
      z.2 i * Q.hessian i j * z.2 j) (fun i _ =>
      ParamSmooth.sum Finset.univ _ (fun j _ => by
        convert ((hc i).const_mul (Q.hessian i j)).mul (hc j) using 1
        funext z
        ring))).const_mul (1 / 2))

theorem scalarData_frozenTerminal_paramRegular {β s h : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) :
    ParamRegular (fun z : P × Vec3 => frozenTerminal β (cdf (D.μ : Measure ℝ)) s h z.2) := by
  have H := StepCalculus.paramRegular_affineBilinear
    (P := P) (scalarData_frozenTerminal_qPotential D 2 ht) (by norm_num)
    (ContinuousLinearMap.id ℝ Vec3) 0
  simpa only [ContinuousLinearMap.id_apply, zero_apply, add_zero]
    using H

theorem scalarData_frozenTerminal_affine_inputs {β s h z ε : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) :
    ParamRegular (fun p : P × Vec3 => ε * frozenTerminal β (cdf (D.μ : Measure ℝ)) s h p.2) ∧
      ParamSmooth (fun p : P × Vec3 => terminalResidual β (cdf (D.μ : Measure ℝ)) s h z p.2) := by
  have H := scalarData_frozenTerminal_paramRegular (P := P) D ht
  refine ⟨H.const_mul ε, ?_⟩
  exact smooth_sub H.toSmooth (smooth_quadraticValue _)

end Terminal

end SKBarriers2.Corner
