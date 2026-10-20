module

public import SKConstants.GaussianProposalConditionalRegression

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.M6

abbrev MatrixSeed (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

def matrixDriversLaw (n : ℕ) :
    Measure (MatrixSeed n × (MatrixSeed n × (MatrixSeed n × MatrixSeed n))) :=
  let gamma := GaussianProposal.primitiveGaussian (Fin n × Fin n)
  gamma.prod (gamma.prod (gamma.prod gamma))

def coupledMatrixInput {n : ℕ} (delta theta : ℝ)
    (p : MatrixSeed n × (MatrixSeed n × (MatrixSeed n × MatrixSeed n))) : MatrixSeed n :=
  Real.sqrt (1 - delta) •
      (Real.sqrt (1 - delta) • p.1 + Real.sqrt delta • p.2.1) +
    Real.sqrt delta • (Real.cos theta • p.2.2.1 + Real.sin theta • p.2.2.2)

theorem primitiveGaussian_normalized_sum_law {ι : Type*} [Fintype ι]
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((GaussianProposal.primitiveGaussian ι).prod
      (GaussianProposal.primitiveGaussian ι)).map (fun p => c • p.1 + s • p.2) =
      GaussianProposal.primitiveGaussian ι := by
  rw [primitiveGaussian_weighted_sum_law, hcs, Real.sqrt_one]
  rw [show (fun z : EuclideanSpace ℝ ι => (1 : ℝ) • z) = id by
    funext z; exact one_smul ℝ z, Measure.map_id]

theorem primitiveGaussian_rotation_law {ι : Type*} [Fintype ι] (theta : ℝ) :
    ((GaussianProposal.primitiveGaussian ι).prod
      (GaussianProposal.primitiveGaussian ι)).map
        (fun p => Real.cos theta • p.1 + Real.sin theta • p.2) =
      GaussianProposal.primitiveGaussian ι := by
  exact primitiveGaussian_normalized_sum_law _ _ (by
    nlinarith [Real.sin_sq_add_cos_sq theta])

theorem regression_noise_law {ι : Type*} [Fintype ι]
    (delta theta : ℝ) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    ((GaussianProposal.primitiveGaussian ι).prod
      ((GaussianProposal.primitiveGaussian ι).prod
        (GaussianProposal.primitiveGaussian ι))).map
      (fun p => Real.sqrt (1 - delta) • (Real.sqrt delta • p.1) +
        Real.sqrt delta • (Real.cos theta • p.2.1 + Real.sin theta • p.2.2)) =
      (GaussianProposal.primitiveGaussian ι).map
        (fun z => Real.sqrt (delta * (2 - delta)) • z) := by
  let gamma := GaussianProposal.primitiveGaussian ι
  let rot : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun p => Real.cos theta • p.1 + Real.sin theta • p.2
  have hrot : Measurable rot := by fun_prop
  have hpair : (gamma.prod (gamma.prod gamma)).map (Prod.map id rot) =
      gamma.prod gamma := by
    rw [← Measure.map_prod_map _ _ measurable_id hrot, Measure.map_id,
      primitiveGaussian_rotation_law]
  have hvar : (Real.sqrt (1 - delta) * Real.sqrt delta)^2 +
      (Real.sqrt delta)^2 = delta * (2 - delta) := by
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hdelta1), Real.sq_sqrt hdelta]
    ring
  have hm := congrArg (fun mu : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) =>
    mu.map (fun p => (Real.sqrt (1 - delta) * Real.sqrt delta) • p.1 +
      Real.sqrt delta • p.2)) hpair
  rw [Measure.map_map (by fun_prop) (measurable_id.prodMap hrot),
    primitiveGaussian_weighted_sum_law, hvar] at hm
  simpa only [Function.comp_def, Prod.map_apply', id_eq, smul_smul, rot, gamma] using hm

theorem coupledMatrix_target_pair_law (n : ℕ) (delta theta : ℝ)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (matrixDriversLaw n).map (fun p => (p.1, coupledMatrixInput delta theta p)) =
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) ⊗ₘ
        gaussianEuclideanSmoothingKernel (1 - delta) (delta * (2 - delta)).toNNReal := by
  let gamma := GaussianProposal.primitiveGaussian (Fin n × Fin n)
  let noise : MatrixSeed n × (MatrixSeed n × MatrixSeed n) → MatrixSeed n :=
    fun p => Real.sqrt (1 - delta) • (Real.sqrt delta • p.1) +
      Real.sqrt delta • (Real.cos theta • p.2.1 + Real.sin theta • p.2.2)
  have hnoise : Measurable noise := by fun_prop
  have hprod : (matrixDriversLaw n).map (Prod.map id noise) =
      gamma.prod (gamma.map (fun z => Real.sqrt (delta * (2 - delta)) • z)) := by
    rw [matrixDriversLaw, ← Measure.map_prod_map _ _ measurable_id hnoise,
      Measure.map_id, regression_noise_law delta theta hdelta hdelta1]
  have hvar : 0 ≤ delta * (2 - delta) := mul_nonneg hdelta (by linarith)
  rw [gaussianEuclideanSmoothing_compProd_eq_affine_map,
    Real.coe_toNNReal _ hvar]
  have hmean : (Real.sqrt (1 - delta))^2 = 1 - delta :=
    Real.sq_sqrt (sub_nonneg.mpr hdelta1)
  calc
    _ = ((matrixDriversLaw n).map (Prod.map id noise)).map
        (fun p => (p.1, (1 - delta) • p.1 + p.2)) := by
      rw [Measure.map_map (by fun_prop) (measurable_id.prodMap hnoise)]
      congr 1
      funext p
      apply Prod.ext
      · rfl
      · dsimp [coupledMatrixInput, noise]
        rw [smul_add, smul_smul, ← pow_two, hmean]
        abel
    _ = (gamma.prod (gamma.map (fun z => Real.sqrt (delta * (2 - delta)) • z))).map
        (fun p => (p.1, (1 - delta) • p.1 + p.2)) := by rw [hprod]
    _ = _ := by
      have hp : gamma.prod (gamma.map (fun z => Real.sqrt (delta * (2 - delta)) • z)) =
          (gamma.prod gamma).map
            (Prod.map id (fun z => Real.sqrt (delta * (2 - delta)) • z)) := by
        rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
      rw [hp, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl

end SKConstants.M6
