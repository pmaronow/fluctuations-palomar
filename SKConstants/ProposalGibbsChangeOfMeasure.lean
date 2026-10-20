module

public import SKConstants.ConditionalGibbsDisintegration
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal Topology Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def uniformSpinLaw (n : ℕ) : Measure (Spin n) :=
  finiteWeightMeasure (fun _ => 1 / (2 : ℝ) ^ n)

instance uniformSpinLaw_isProbability (n : ℕ) : IsProbabilityMeasure (uniformSpinLaw n) := by
  change IsProbabilityMeasure (finiteWeightMeasure (fun _ : Spin n => 1 / (2 : ℝ) ^ n))
  rw [← conditionalGibbsSpinLaw_sk n 0]
  infer_instance

def unlinkedPrimitiveSpinFirstLaw (n : ℕ) :
    Measure (Spin n × EuclideanSpace ℝ (Fin n × Fin n)) :=
  (uniformSpinLaw n).prod (GaussianProposal.primitiveGaussian (Fin n × Fin n))

instance unlinkedPrimitiveSpinFirstLaw_isProbability (n : ℕ) :
    IsProbabilityMeasure (unlinkedPrimitiveSpinFirstLaw n) := by
  unfold unlinkedPrimitiveSpinFirstLaw
  infer_instance

def primitiveGibbsLinkDensity (n : ℕ) (beta : ℝ)
    (p : Spin n × EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  (2 : ℝ) ^ n * gibbsProbability beta
    (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) p.2) p.1

theorem primitiveGibbsLinkDensity_pos (n : ℕ) (beta : ℝ)
    (p : Spin n × EuclideanSpace ℝ (Fin n × Fin n)) :
    0 < primitiveGibbsLinkDensity n beta p :=
  mul_pos (pow_pos (by norm_num) _) (gibbsProbability_pos beta _ _)

theorem primitiveGibbsLinkDensity_measurable (n : ℕ) (beta : ℝ) :
    Measurable (primitiveGibbsLinkDensity n beta) := by
  apply measurable_from_prod_countable_right
  intro x
  exact (measurable_const.mul (((continuous_gibbsProbability beta x).comp
    (continuous_goeMatrix (1 / Real.sqrt (2 * (n : ℝ))))).measurable))

theorem log_primitiveGibbsLinkDensity (n : ℕ) (beta : ℝ)
    (p : Spin n × EuclideanSpace ℝ (Fin n × Fin n)) :
    Real.log (primitiveGibbsLinkDensity n beta p) =
      (n : ℝ) * Real.log 2 + beta * goeSpinHamiltonian
        (1 / Real.sqrt (2 * (n : ℝ))) p.1 p.2 -
      Real.log (gibbsPartition beta (GaussianProposal.goeMatrix
        (1 / Real.sqrt (2 * (n : ℝ))) p.2)) := by
  rw [primitiveGibbsLinkDensity, Real.log_mul (pow_ne_zero _ (by norm_num))
    (gibbsProbability_pos beta _ _).ne', Real.log_pow, log_gibbsProbability]
  unfold goeSpinHamiltonian
  ring

theorem unlinkedPrimitiveSpinFirstLaw_withDensity_gibbs (n : ℕ) (beta : ℝ) :
    (unlinkedPrimitiveSpinFirstLaw n).withDensity
      (fun p => ENNReal.ofReal (primitiveGibbsLinkDensity n beta p)) =
      (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap := by
  let σ := 1 / Real.sqrt (2 * (n : ℝ))
  let g : Spin n → EuclideanSpace ℝ (Fin n × Fin n) → ℝ≥0∞ :=
    fun x z => ENNReal.ofReal (primitiveGibbsLinkDensity n beta (x, z))
  have hg : Measurable (Function.uncurry g) := (primitiveGibbsLinkDensity_measurable n beta).ennreal_ofReal
  let κ := Kernel.const (Spin n) (GaussianProposal.primitiveGaussian (Fin n × Fin n))
  have hk : conditionalGibbsGaussianKernel n beta σ = κ.withDensity g := by
    apply Kernel.ext
    intro x
    rw [Kernel.withDensity_apply κ hg]
    exact conditionalGibbsGaussianLaw_sk beta x
  let _ : IsMarkovKernel (κ.withDensity g) := by rw [← hk]; infer_instance
  rw [primitiveJointGibbsLaw_disintegrated, conditionalGibbsSpinLaw_sk, hk,
    Measure.compProd_withDensity hg, Measure.compProd_const]
  rfl

theorem map_withDensity_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (Y : A → B) (hY : Measurable Y) (g : B → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (g ∘ Y)).map Y = (μ.map Y).withDensity g := by
  ext s hs
  rw [Measure.map_apply hY hs, withDensity_apply _ (hY hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hY]
  rfl

theorem enlargedReference_gibbs_tilt_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (beta : ℝ) (R : Measure Ω)
    (Y : Ω → Spin n × EuclideanSpace ℝ (Fin n × Fin n)) (hY : Measurable Y)
    (hR : R.map Y = unlinkedPrimitiveSpinFirstLaw n) :
    (R.withDensity (fun ω => ENNReal.ofReal (primitiveGibbsLinkDensity n beta (Y ω)))).map Y =
      (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap := by
  rw [show (fun ω => ENNReal.ofReal (primitiveGibbsLinkDensity n beta (Y ω))) =
    (fun p => ENNReal.ofReal (primitiveGibbsLinkDensity n beta p)) ∘ Y by rfl,
    map_withDensity_comp R Y hY _ (primitiveGibbsLinkDensity_measurable n beta).ennreal_ofReal,
    hR, unlinkedPrimitiveSpinFirstLaw_withDensity_gibbs]

theorem klDiv_positive_density_experiments {Ω : Type*} [MeasurableSpace Ω]
    (R : Measure Ω) [IsProbabilityMeasure R] (f g : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hfpos : ∀ ω, 0 < f ω) (hgpos : ∀ ω, 0 < g ω)
    [IsProbabilityMeasure (R.withDensity (fun ω => ENNReal.ofReal (f ω)))]
    [IsProbabilityMeasure (R.withDensity (fun ω => ENNReal.ofReal (g ω)))]
    (hint : Integrable (fun ω => Real.log (f ω) - Real.log (g ω))
      (R.withDensity (fun ω => ENNReal.ofReal (f ω)))) :
    klDiv (R.withDensity (fun ω => ENNReal.ofReal (f ω)))
      (R.withDensity (fun ω => ENNReal.ofReal (g ω))) =
      ENNReal.ofReal (∫ ω, Real.log (f ω) - Real.log (g ω)
        ∂(R.withDensity (fun ω => ENNReal.ofReal (f ω)))) := by
  let L := R.withDensity (fun ω => ENNReal.ofReal (f ω))
  let P := R.withDensity (fun ω => ENNReal.ofReal (g ω))
  have hLR : L ≪ R := withDensity_absolutelyContinuous _ _
  have hRP : R ≪ P := withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun ω => ENNReal.ofReal_ne_zero_iff.mpr (hgpos ω)))
  have hac : L ≪ P := hLR.trans hRP
  have hRN := Measure.rnDeriv_withDensity_right L R hg.ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun ω => ENNReal.ofReal_ne_zero_iff.mpr (hgpos ω)))
    (ae_of_all _ (fun ω => ENNReal.ofReal_ne_top))
  have hRF := Measure.rnDeriv_withDensity R hf.ennreal_ofReal
  have hllr : llr L P =ᵐ[L] fun ω => Real.log (f ω) - Real.log (g ω) := by
    filter_upwards [hRN.filter_mono hLR.ae_le, hRF.filter_mono hLR.ae_le] with ω hω hωf
    change (L.rnDeriv P) ω = (ENNReal.ofReal (g ω))⁻¹ * (L.rnDeriv R) ω at hω
    change (L.rnDeriv R) ω = ENNReal.ofReal (f ω) at hωf
    change Real.log ((L.rnDeriv P) ω).toReal = _
    rw [hω, hωf]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (hgpos ω).le, ENNReal.toReal_ofReal (hfpos ω).le]
    rw [Real.log_mul (inv_ne_zero (hgpos ω).ne') (hfpos ω).ne', Real.log_inv]
    ring
  rw [klDiv_of_ac_of_integrable hac (hint.congr hllr.symm), integral_congr_ae hllr]
  simp [L, P]

def proposalGibbsLogRatio {Ω : Type*} (n : ℕ) (beta : ℝ)
    (Y : Ω → Spin n × EuclideanSpace ℝ (Fin n × Fin n)) (eB : Ω → ℝ) (ω : Ω) : ℝ :=
  Real.log (eB ω) - (n : ℝ) * Real.log 2 +
    Real.log (gibbsPartition beta (GaussianProposal.goeMatrix
      (1 / Real.sqrt (2 * (n : ℝ))) (Y ω).2)) -
    beta * goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) (Y ω).1 (Y ω).2

theorem proposalGibbsLogRatio_eq_log_ratio {Ω : Type*} (n : ℕ) (beta : ℝ)
    (Y : Ω → Spin n × EuclideanSpace ℝ (Fin n × Fin n)) (eB : Ω → ℝ) (ω : Ω) :
    proposalGibbsLogRatio n beta Y eB ω =
      Real.log (eB ω) - Real.log (primitiveGibbsLinkDensity n beta (Y ω)) := by
  rw [log_primitiveGibbsLinkDensity, proposalGibbsLogRatio]
  ring

theorem enlargedReference_gibbs_KL_contraction {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (beta : ℝ) (R : Measure Ω) [IsProbabilityMeasure R]
    (Y : Ω → Spin n × EuclideanSpace ℝ (Fin n × Fin n)) (hY : Measurable Y)
    (hR : R.map Y = unlinkedPrimitiveSpinFirstLaw n)
    (eB : Ω → ℝ) (heB : Measurable eB) (heBpos : ∀ ω, 0 < eB ω)
    [IsProbabilityMeasure (R.withDensity (fun ω => ENNReal.ofReal (eB ω)))]
    (hint : Integrable (proposalGibbsLogRatio n beta Y eB)
      (R.withDensity (fun ω => ENNReal.ofReal (eB ω)))) :
    klDiv ((R.withDensity (fun ω => ENNReal.ofReal (eB ω))).map Y)
      ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) ≤
      ENNReal.ofReal (∫ ω, proposalGibbsLogRatio n beta Y eB ω
        ∂(R.withDensity (fun ω => ENNReal.ofReal (eB ω)))) := by
  let g : Ω → ℝ := fun ω => primitiveGibbsLinkDensity n beta (Y ω)
  let P := R.withDensity (fun ω => ENNReal.ofReal (g ω))
  have hP : P.map Y = (primitiveJointGibbsLaw n beta
      (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap := enlargedReference_gibbs_tilt_endpoint n beta R Y hY hR
  let _ : IsProbabilityMeasure P := by
    constructor
    have hu : (P.map Y) univ = P univ := by rw [Measure.map_apply hY .univ, preimage_univ]
    rw [← hu, hP, measure_univ]
  have hi : Integrable (fun ω => Real.log (eB ω) - Real.log (g ω))
      (R.withDensity (fun ω => ENNReal.ofReal (eB ω))) := by
    simpa only [g, ← proposalGibbsLogRatio_eq_log_ratio] using hint
  have hKL := klDiv_positive_density_experiments R eB g heB
    ((primitiveGibbsLinkDensity_measurable n beta).comp hY) heBpos
    (fun ω => primitiveGibbsLinkDensity_pos n beta (Y ω)) hi
  have h := klDiv_map_le (R.withDensity (fun ω => ENNReal.ofReal (eB ω))) P hY
  rw [hP, hKL] at h
  simpa only [g, ← proposalGibbsLogRatio_eq_log_ratio] using h

theorem positive_density_restrict_le_exp_logratio {Ω : Type*} [MeasurableSpace Ω]
    (R : Measure Ω) (f g : Ω → ℝ) (hg : Measurable g)
    (hfpos : ∀ ω, 0 < f ω) (hgpos : ∀ ω, 0 < g ω)
    (S : Set Ω) (hS : MeasurableSet S) (K : ℝ)
    (hbound : ∀ ω ∈ S, Real.log (f ω) - Real.log (g ω) ≤ K) :
    (R.withDensity (fun ω => ENNReal.ofReal (f ω))).restrict S ≤
      ENNReal.ofReal (Real.exp K) • (R.withDensity (fun ω => ENNReal.ofReal (g ω))) := by
  let C := ENNReal.ofReal (Real.exp K)
  have hfg : (fun ω => ENNReal.ofReal (f ω)) ≤ᵐ[R.restrict S]
      C • (fun ω => ENNReal.ofReal (g ω)) := by
    filter_upwards [ae_restrict_mem hS] with ω hω
    have hb : f ω ≤ Real.exp K * g ω := by
      calc
        f ω = Real.exp (Real.log (f ω)) := (Real.exp_log (hfpos ω)).symm
        _ ≤ Real.exp (K + Real.log (g ω)) := Real.exp_le_exp.mpr (by linarith [hbound ω hω])
        _ = Real.exp K * g ω := by rw [Real.exp_add, Real.exp_log (hgpos ω)]
    simpa only [Pi.smul_apply, smul_eq_mul, C,
      ← ENNReal.ofReal_mul (Real.exp_pos K).le] using ENNReal.ofReal_le_ofReal hb
  calc
    _ ≤ C • ((R.withDensity (fun ω => ENNReal.ofReal (g ω))).restrict S) := by
      rw [restrict_withDensity hS, restrict_withDensity hS,
        ← withDensity_smul C hg.ennreal_ofReal]
      exact withDensity_mono hfg
    _ ≤ C • (R.withDensity (fun ω => ENNReal.ofReal (g ω))) := by
      gcongr
      exact Measure.restrict_le_self

theorem enlargedReference_gibbs_restricted_endpoint_domination
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (beta : ℝ) (R : Measure Ω)
    (Y : Ω → Spin n × EuclideanSpace ℝ (Fin n × Fin n)) (hY : Measurable Y)
    (hR : R.map Y = unlinkedPrimitiveSpinFirstLaw n)
    (eB : Ω → ℝ) (heBpos : ∀ ω, 0 < eB ω)
    (S : Set Ω) (hS : MeasurableSet S) (K : ℝ)
    (hbound : ∀ ω ∈ S, proposalGibbsLogRatio n beta Y eB ω ≤ K) :
    ((R.withDensity (fun ω => ENNReal.ofReal (eB ω))).restrict S).map Y ≤
      ENNReal.ofReal (Real.exp K) •
        ((primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).map Prod.swap) := by
  have h := positive_density_restrict_le_exp_logratio R eB
    (fun ω => primitiveGibbsLinkDensity n beta (Y ω))
    ((primitiveGibbsLinkDensity_measurable n beta).comp hY) heBpos
    (fun ω => primitiveGibbsLinkDensity_pos n beta (Y ω)) S hS K
    (fun ω hω => by simpa only [← proposalGibbsLogRatio_eq_log_ratio] using hbound ω hω)
  have hm := Measure.map_mono h hY
  rw [Measure.map_smul _ hY.aemeasurable,
    enlargedReference_gibbs_tilt_endpoint n beta R Y hY hR] at hm
  exact hm

end SKConstants
