module

public import SKConstants.ParisiCDFOverlapDerivative

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic

variable (β : ℝ) (α : StieltjesFunction ℝ)
  (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
  {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)

include ha h1 hβ hT0 hT1

lemma compactCDFValueRate_jet_two (t x : ℝ) :
    iteratedDeriv 2 (compactCDFValueRate β α T t) x =
      -(β^2/2)*compactCDFJet β α T 3 t x - β^2*compactCDFCoefficient α T t*
        ((compactCDFJet β α T 1 t x)^2+
          compactCDFJet β α T 0 t x*compactCDFJet β α T 2 t x) := by
  have he : deriv (compactCDFValueRate β α T t) = fun y =>
      -(β^2/2)*compactCDFJet β α T 2 t y -
        β^2*compactCDFCoefficient α T t*compactCDFJet β α T 0 t y*compactCDFJet β α T 1 t y := by
    funext y
    rw [compactCDFValueRate_deriv β α ha h1 hβ hT0 hT1]
    ring
  have hd (n : ℕ) := compactCDFJet_hasDerivAt β α ha h1 hβ hT0 hT1 n t x
  have hdv := (((hd 2).const_mul (-(β^2/2))).sub
    (((hd 0).const_mul (β^2*compactCDFCoefficient α T t)).mul (hd 1))).deriv
  change deriv (fun y => -(β^2/2)*compactCDFJet β α T 2 t y -
    β^2*compactCDFCoefficient α T t*compactCDFJet β α T 0 t y*compactCDFJet β α T 1 t y) x = _ at hdv
  rw [show (2:ℕ)=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, he, hdv]
  ring

lemma compactCDFValueRate_jet_three (t x : ℝ) :
    iteratedDeriv 3 (compactCDFValueRate β α T t) x =
      -(β^2/2)*compactCDFJet β α T 4 t x - β^2*compactCDFCoefficient α T t*
        (3*compactCDFJet β α T 1 t x*compactCDFJet β α T 2 t x+
          compactCDFJet β α T 0 t x*compactCDFJet β α T 3 t x) := by
  have he : iteratedDeriv 2 (compactCDFValueRate β α T t) = fun y =>
      -(β^2/2)*compactCDFJet β α T 3 t y - β^2*compactCDFCoefficient α T t*
        ((compactCDFJet β α T 1 t y)^2+
          compactCDFJet β α T 0 t y*compactCDFJet β α T 2 t y) :=
    funext (compactCDFValueRate_jet_two β α ha h1 hβ hT0 hT1 t)
  have hd (n : ℕ) := compactCDFJet_hasDerivAt β α ha h1 hβ hT0 hT1 n t x
  have hdv := (((hd 3).const_mul (-(β^2/2))).sub
    ((((hd 1).pow 2).add ((hd 0).mul (hd 2))).const_mul
      (β^2*compactCDFCoefficient α T t))).deriv
  change deriv (fun y => -(β^2/2)*compactCDFJet β α T 3 t y -
    β^2*compactCDFCoefficient α T t*((compactCDFJet β α T 1 t y)^2+
      compactCDFJet β α T 0 t y*compactCDFJet β α T 2 t y)) x = _ at hdv
  rw [show (3:ℕ)=2+1 from rfl, iteratedDeriv_succ, he, hdv]
  ring

lemma physicalCDFJetField_generator_one (t x : ℝ) :
    (physicalCDFJetField β α ha h1 hβ hT0 hT1 1).generator
      (physicalCDFCompactDrift β α T) t x =
        -compactCDFCoefficient α T (t/β^2)*(compactCDFJet β α T 1 (t/β^2) x)^2 := by
  dsimp only [TimeField.generator, physicalCDFJetField, rescaleTimeField, compactCDFJetField]
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1,
    deriv_compactCDFJet β α ha h1 hβ hT0 hT1,
    compactCDFValueRate_jet_two β α ha h1 hβ hT0 hT1]
  rw [show (1/β^2)*t=t/β^2 by ring]
  unfold physicalCDFCompactDrift
  field_simp
  ring

lemma physicalCDFJetField_generator_two (t x : ℝ) :
    (physicalCDFJetField β α ha h1 hβ hT0 hT1 2).generator
      (physicalCDFCompactDrift β α T) t x =
        -3*compactCDFCoefficient α T (t/β^2)*compactCDFJet β α T 1 (t/β^2) x*
          compactCDFJet β α T 2 (t/β^2) x := by
  dsimp only [TimeField.generator, physicalCDFJetField, rescaleTimeField, compactCDFJetField]
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1,
    deriv_compactCDFJet β α ha h1 hβ hT0 hT1,
    compactCDFValueRate_jet_three β α ha h1 hβ hT0 hT1]
  rw [show (1/β^2)*t=t/β^2 by ring]
  unfold physicalCDFCompactDrift
  field_simp
  ring

def physicalCDFCurvatureField : TimeField (T/(1/β^2)) :=
  (physicalCDFJetField β α ha h1 hβ hT0 hT1 1).mul
    (physicalCDFJetField β α ha h1 hβ hT0 hT1 1)

def physicalCDFSecondCurvatureField (c : ℝ) : TimeField (T/(1/β^2)) :=
  ((physicalCDFJetField β α ha h1 hβ hT0 hT1 2).mul
    (physicalCDFJetField β α ha h1 hβ hT0 hT1 2)).add
    (((physicalCDFCurvatureField β α ha h1 hβ hT0 hT1).mul
      (physicalCDFJetField β α ha h1 hβ hT0 hT1 1)).const_mul (-2*c))

lemma physicalCDFCurvatureField_deriv (t x : ℝ) :
    deriv ((physicalCDFCurvatureField β α ha h1 hβ hT0 hT1).f t) x =
      2*compactCDFJet β α T 1 (t/β^2) x*compactCDFJet β α T 2 (t/β^2) x := by
  have hd := compactCDFJet_hasDerivAt β α ha h1 hβ hT0 hT1 1 (t/β^2) x
  change deriv (fun y => compactCDFJet β α T 1 ((1/β^2)*t) y*
    compactCDFJet β α T 1 ((1/β^2)*t) y) x = _
  rw [show (1/β^2)*t=t/β^2 by ring]
  exact (hd.mul hd).deriv.trans (by ring)

lemma physicalCDFCurvatureField_generator (t x : ℝ) :
    (physicalCDFCurvatureField β α ha h1 hβ hT0 hT1).generator
      (physicalCDFCompactDrift β α T) t x =
        (physicalCDFSecondCurvatureField β α ha h1 hβ hT0 hT1
          (compactCDFCoefficient α T (t/β^2))).f t x := by
  unfold physicalCDFCurvatureField
  rw [TimeField.generator_mul, physicalCDFJetField_generator_one β α ha h1 hβ hT0 hT1]
  dsimp only [physicalCDFJetField, rescaleTimeField, compactCDFJetField]
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1]
  dsimp only [physicalCDFSecondCurvatureField, physicalCDFCurvatureField,
    TimeField.add, TimeField.mul, TimeField.const_mul, physicalCDFJetField,
    rescaleTimeField, compactCDFJetField]
  rw [show (1/β^2)*t=t/β^2 by ring]
  ring

lemma physicalCDFSecondCurvatureField_generator (c t x : ℝ)
    (hc : compactCDFCoefficient α T (t/β^2)=c) :
    (physicalCDFSecondCurvatureField β α ha h1 hβ hT0 hT1 c).generator
      (physicalCDFCompactDrift β α T) t x =
        (compactCDFJet β α T 3 (t/β^2) x)^2-
          12*c*compactCDFJet β α T 1 (t/β^2) x*(compactCDFJet β α T 2 (t/β^2) x)^2+
          6*c^2*(compactCDFJet β α T 1 (t/β^2) x)^4 := by
  unfold physicalCDFSecondCurvatureField
  rw [TimeField.generator_add, TimeField.generator_const_mul,
    TimeField.generator_mul, TimeField.generator_mul,
    physicalCDFCurvatureField_generator β α ha h1 hβ hT0 hT1,
    physicalCDFJetField_generator_one β α ha h1 hβ hT0 hT1,
    physicalCDFJetField_generator_two β α ha h1 hβ hT0 hT1,
    physicalCDFCurvatureField_deriv β α ha h1 hβ hT0 hT1]
  dsimp only [physicalCDFJetField, rescaleTimeField, compactCDFJetField]
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1,
    deriv_compactCDFJet β α ha h1 hβ hT0 hT1]
  dsimp only [physicalCDFSecondCurvatureField, physicalCDFCurvatureField,
    TimeField.add, TimeField.mul, TimeField.const_mul, physicalCDFJetField,
    rescaleTimeField, compactCDFJetField]
  rw [show (1/β^2)*t=t/β^2 by ring, hc]
  ring

end SKConstants.ParisiFullSupport
