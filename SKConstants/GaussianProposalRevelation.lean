module

public import SKConstants.GaussianProposal
public import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKConstants.GaussianProposal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem goeBilinear_family_gaussian (sigma : ℝ) (u v : κ → ι → ℝ) :
    HasGaussianLaw (fun z : EuclideanSpace ℝ (ι × ι) =>
      fun k => goeBilinear sigma (u k) (v k) z) (primitiveGaussian (ι × ι)) := by
  have h := (IsGaussian.hasGaussianLaw_id (μ := primitiveGaussian (ι × ι))).map_fun
    (ContinuousLinearMap.pi (fun k => linearFormCLM
      (fun p : ι × ι => sigma * (u k p.1 * v k p.2 + u k p.2 * v k p.1))))
  apply h.congr
  apply Filter.Eventually.of_forall
  intro z
  funext k
  simp only [id_eq, ContinuousLinearMap.pi_apply, linearFormCLM_apply, goeBilinear]

variable [LinearOrder ι]

abbrev UpperPair (ι : Type*) [LinearOrder ι] := {p : ι × ι // p.1 ≤ p.2}

@[expose] def basisEntry (sigma : ℝ) (basis : ι → ι → ℝ) (p : UpperPair ι)
    (z : EuclideanSpace ℝ (ι × ι)) : ℝ :=
  goeBilinear sigma (basis p.1.1) (basis p.1.2) z

theorem basisEntry_covariance (sigma : ℝ) (basis : ι → ι → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0)
    (p q : UpperPair ι) :
    cov[basisEntry sigma basis p, basisEntry sigma basis q;
      primitiveGaussian (ι × ι)] =
      if p = q then (if p.1.1 = p.1.2 then 4 * sigma ^ 2 else 2 * sigma ^ 2)
      else 0 := by
  unfold basisEntry
  rw [goeBilinear_covariance]
  simp_rw [horth]
  by_cases hpq : p = q
  · subst q
    by_cases hdiag : p.1.1 = p.1.2 <;> simp [hdiag] <;> ring
  · have hdirect : ¬(p.1.1 = q.1.1 ∧ p.1.2 = q.1.2) := by
      rintro ⟨h1,h2⟩
      apply hpq
      exact Subtype.ext (Prod.ext h1 h2)
    have hreverse : ¬(p.1.1 = q.1.2 ∧ p.1.2 = q.1.1) := by
      rintro ⟨h1,h2⟩
      have hdiag : p.1.1 = p.1.2 := le_antisymm p.property
        (by simpa only [h1,h2] using q.property)
      apply hpq
      apply Subtype.ext
      apply Prod.ext
      · exact hdiag.trans h2
      · exact hdiag.symm.trans h1
    by_cases h11 : p.1.1 = q.1.1 <;> by_cases h22 : p.1.2 = q.1.2 <;>
      by_cases h12 : p.1.1 = q.1.2 <;> by_cases h21 : p.1.2 = q.1.1 <;>
      simp_all

theorem basisEntries_independent (sigma : ℝ) (basis : ι → ι → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    iIndepFun (basisEntry sigma basis) (primitiveGaussian (ι × ι)) := by
  have hjoint := goeBilinear_family_gaussian sigma
    (fun p : UpperPair ι => basis p.1.1) (fun p => basis p.1.2)
  apply hjoint.iIndepFun_of_covariance_eq_zero
  intro p q hpq
  change cov[basisEntry sigma basis p, basisEntry sigma basis q;
    primitiveGaussian (ι × ι)] = 0
  rw [basisEntry_covariance sigma basis horth p q, if_neg hpq]

theorem basisEntry_law (sigma : ℝ) (basis : ι → ι → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0)
    (p : UpperPair ι) :
    (primitiveGaussian (ι × ι)).map (basisEntry sigma basis p) =
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * sigma ^ 2).toNNReal
        else (2 * sigma ^ 2).toNNReal) := by
  have hgauss := goeBilinear_gaussian sigma (basis p.1.1) (basis p.1.2)
  change HasGaussianLaw (basisEntry sigma basis p) (primitiveGaussian (ι × ι)) at hgauss
  rw [hgauss.map_eq_gaussianReal]
  have hmean : (∫ z, basisEntry sigma basis p z ∂primitiveGaussian (ι × ι)) = 0 :=
    goeBilinear_mean sigma _ _
  have hvar : Var[basisEntry sigma basis p; primitiveGaussian (ι × ι)] =
      if p.1.1 = p.1.2 then 4 * sigma ^ 2 else 2 * sigma ^ 2 := by
    rw [← covariance_self hgauss.aemeasurable,
      basisEntry_covariance sigma basis horth p p]
    simp
  change gaussianReal (∫ z, basisEntry sigma basis p z ∂primitiveGaussian (ι × ι))
    Var[basisEntry sigma basis p; primitiveGaussian (ι × ι)].toNNReal = _
  rw [hmean,hvar]
  split_ifs <;> rfl

set_option maxHeartbeats 800000 in
theorem basisEntries_joint_law (sigma : ℝ) (basis : ι → ι → ℝ)
    (horth : ∀ i j, dot (basis i) (basis j) = if i = j then 1 else 0) :
    (primitiveGaussian (ι × ι)).map (fun z p => basisEntry sigma basis p z) =
      Measure.pi (fun p : UpperPair ι => gaussianReal 0
        (if p.1.1 = p.1.2 then (4 * sigma ^ 2).toNNReal
          else (2 * sigma ^ 2).toNNReal)) := by
  have hmeas (p : UpperPair ι) : AEMeasurable (basisEntry sigma basis p)
      (primitiveGaussian (ι × ι)) := by
    exact (goeBilinear_gaussian sigma (basis p.1.1) (basis p.1.2)).aemeasurable
  have hmap := iIndepFun.map_fun_eq_pi_map
    (μ := primitiveGaussian (ι × ι)) (f := basisEntry sigma basis)
      hmeas (basisEntries_independent sigma basis horth)
  calc
    _ = Measure.pi (fun p => (primitiveGaussian (ι × ι)).map
          (basisEntry sigma basis p)) := hmap
    _ = _ := ?_
  congr 1
  funext p
  exact basisEntry_law sigma basis horth p

end SKConstants.GaussianProposal
