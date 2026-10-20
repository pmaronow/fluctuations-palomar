module

public import SKConstants.ParisiCDFTimeField

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

lemma deriv_compactCDFJet (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (n : ℕ) (t : ℝ) :
    deriv (compactCDFJet β α T n t) = compactCDFJet β α T (n+1) t :=
  funext (fun x => (compactCDFJet_hasDerivAt β α ha h1 hβ hT0 hT1 n t x).deriv)

lemma compactCDFValueRate_deriv (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    deriv (compactCDFValueRate β α T t) x = -(β^2/2)*
      (compactCDFJet β α T 2 t x + 2*compactCDFCoefficient α T t*
        compactCDFJet β α T 0 t x*compactCDFJet β α T 1 t x) := by
  have H := compactCDFValueRate_jet β α ha h1 hβ hT0 hT1 1 t x
  have hg := compactCDFJet_hasDerivAt β α ha h1 hβ hT0 hT1 0 t x
  have hgg := (hg.mul hg).deriv
  change deriv (fun y => compactCDFGradient β α T t y*compactCDFGradient β α T t y) x = _ at hgg
  simp only [iteratedDeriv_one, Nat.reduceAdd] at H
  rw [hgg] at H
  exact H.trans (by
    simp only [compactCDFJet, Nat.reduceAdd, iteratedDeriv_zero, iteratedDeriv_one]
    ring)

def physicalCDFCompactDrift (β : ℝ) (α : ℝ → ℝ) (T t x : ℝ) : ℝ :=
  compactCDFCoefficient α T (t/β^2)*compactCDFJet β α T 0 (t/β^2) x

lemma physicalCDFGradient_generator_zero (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    (physicalCDFJetField β α ha h1 hβ hT0 hT1 0).generator
      (physicalCDFCompactDrift β α T) t x = 0 := by
  unfold TimeField.generator physicalCDFJetField rescaleTimeField compactCDFJetField
  dsimp only
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1,
    deriv_compactCDFJet β α ha h1 hβ hT0 hT1, iteratedDeriv_one,
    compactCDFValueRate_deriv β α ha h1 hβ hT0 hT1]
  rw [show (1/β^2)*t = t/β^2 by ring]
  unfold physicalCDFCompactDrift
  field_simp
  ring

lemma physicalCDFGradient_square_generator (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (t x : ℝ) :
    ((physicalCDFJetField β α ha h1 hβ hT0 hT1 0).mul
      (physicalCDFJetField β α ha h1 hβ hT0 hT1 0)).generator
      (physicalCDFCompactDrift β α T) t x =
        (compactCDFJet β α T 1 (t/β^2) x)^2 := by
  rw [TimeField.generator_mul, physicalCDFGradient_generator_zero β α ha h1 hβ hT0 hT1]
  simp only [mul_zero, zero_add]
  change deriv (compactCDFJet β α T 0 ((1/β^2)*t)) x *
    deriv (compactCDFJet β α T 0 ((1/β^2)*t)) x = _
  rw [deriv_compactCDFJet β α ha h1 hβ hT0 hT1]
  rw [show (1/β^2)*t = t/β^2 by ring]
  ring

lemma finiteTemperatureCDFDrift_eq_compact (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T t : ℝ} (hT1 : T ≤ 1) (ht : t/β^2 ∈ Icc (0:ℝ) T) (x : ℝ) :
    (finiteTemperatureCDFDrift β α ha h1).f t x = physicalCDFCompactDrift β α T t x := by
  have hc : cdfTimeClamp (t/β^2) = t/β^2 := cdfTimeClamp_eq ⟨ht.1,ht.2.trans hT1⟩
  simp only [finiteTemperatureCDFDrift, physicalCDFCompactDrift, compactCDFCoefficient,
    compactCDFJet, iteratedDeriv_zero, compactCDFGradient, hc, cdfStripTime_eq ht]

end SKConstants.ParisiFullSupport
