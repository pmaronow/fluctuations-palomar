module

public import SKConstants.ParisiContinuumEquilibrium
public import SKConstants.Upstream.OAI.Probability.SKBarriers.SpinGlass.GaugeSymmetry
public import SKConstants.SKSparseBoundaryRate

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem centeredGaussian_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : HasGaussianLaw X μ) (hmean : ∫ w, X w ∂μ = 0) :
    HasSubgaussianMGF X (Var[X; μ]).toNNReal μ := by
  have hLaw : HasLaw X (gaussianReal 0 (Var[X; μ]).toNNReal) μ :=
    ⟨hX.aemeasurable, by simpa only [hmean] using hX.map_eq_gaussianReal⟩
  exact ⟨fun t => hLaw.integrable_comp (integrable_exp_mul_gaussianReal t),
    fun t => by rw [mgf_gaussianReal hLaw]; simp⟩

def goeDiagonalShift {n : ℕ} (beta sigma : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  beta * ((1 / 2) * ∑ i, GaussianProposal.goeMatrix sigma z i i)

theorem goeDiagonalShift_eq_linearForm {n : ℕ} (beta sigma : ℝ) :
    goeDiagonalShift (n := n) beta sigma = GaussianProposal.linearForm
      (fun p : Fin n × Fin n => if p.1 = p.2 then beta * sigma else 0) := by
  funext z
  simp only [goeDiagonalShift, GaussianProposal.linearForm, Fintype.sum_prod_type]
  simp [GaussianProposal.goeMatrix, Finset.mul_sum]
  ring

theorem goeDiagonalShift_variance {n : ℕ} (beta sigma : ℝ) :
    Var[goeDiagonalShift (n := n) beta sigma;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] = beta^2 * sigma^2 * n := by
  rw [goeDiagonalShift_eq_linearForm, ← covariance_self
    (GaussianProposal.linearForm_gaussian _).aemeasurable,
    GaussianProposal.linearForm_covariance, Fintype.sum_prod_type]
  simp only [ite_mul_ite, mul_zero, zero_mul, zero_add, add_zero]
  simp
  ring

theorem goeDiagonalShift_sk_subgaussian {n : ℕ} (hn : 0 < n) (beta : ℝ) :
    HasSubgaussianMGF (goeDiagonalShift (n := n) beta (1 / Real.sqrt (2 * (n : ℝ))))
      (NNReal.mk (beta^2 / 2) (by positivity)) (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have hG : HasGaussianLaw (goeDiagonalShift (n := n) beta (1 / Real.sqrt (2 * (n : ℝ))))
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
    rw [goeDiagonalShift_eq_linearForm]
    exact GaussianProposal.linearForm_gaussian _
  have hmean : ∫ z, goeDiagonalShift (n := n) beta (1 / Real.sqrt (2 * (n : ℝ))) z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) = 0 := by
    rw [goeDiagonalShift_eq_linearForm]
    exact GaussianProposal.linearForm_mean _
  have hv : Var[goeDiagonalShift (n := n) beta (1 / Real.sqrt (2 * (n : ℝ)));
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] = beta^2 / 2 := by
    rw [goeDiagonalShift_variance, div_pow, one_pow, Real.sq_sqrt (by positivity)]
    have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    field_simp
  have h := centeredGaussian_hasSubgaussianMGF hG hmean
  rw [hv] at h
  simpa only [Real.toNNReal_of_nonneg (show 0 ≤ beta^2 / 2 by positivity)] using h

def primitiveGOEPressure (n : ℕ) (beta : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  Real.log (gibbsPartition beta (GaussianProposal.goeMatrix (1 / Real.sqrt (2 * (n : ℝ))) z))

theorem primitiveGOEPressure_integral_eq_upstream (n : ℕ) (beta : ℝ) :
    (∫ z, primitiveGOEPressure n beta z ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) =
      ∫ J, SKConstantsOAI.SK.logPartition beta J ∂SKConstantsOAI.SK.disorderLaw n := by
  have h := ParisiGOEBridge.expected_logPartition_eq_upstream n beta
  unfold skDisorderLaw at h
  rw [integral_map (continuous_goeMatrix _).measurable.aemeasurable
    ((continuous_gibbsPartition beta).log (fun W => (gibbsPartition_pos beta W).ne')).measurable.aestronglyMeasurable] at h
  exact h

theorem primitiveGOEPressure_centered_subgaussian {n : ℕ} (hn : 0 < n) (beta : ℝ) :
    HasSubgaussianMGF (fun z => primitiveGOEPressure n beta z -
      ∫ w, primitiveGOEPressure n beta w ∂GaussianProposal.primitiveGaussian (Fin n × Fin n))
      ((NNReal.sqrt (SKConstantsOAI.SK.logPartitionProxy beta n) +
        NNReal.sqrt (NNReal.mk (beta^2 / 2) (by positivity)))^2)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have hu : HasSubgaussianMGF (fun J => SKConstantsOAI.SK.logPartition beta J -
      ∫ K, SKConstantsOAI.SK.logPartition beta K ∂SKConstantsOAI.SK.disorderLaw n)
      (SKConstantsOAI.SK.logPartitionProxy beta n)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).map
        (ParisiGOEBridge.edgeDisorder n)) := by
    rw [(ParisiGOEBridge.edgeDisorder_hasLaw n).map_eq]
    exact SKConstantsOAI.SK.logPartition_subGaussian hn beta
  have hUp := HasSubgaussianMGF.of_map (ParisiGOEBridge.edgeDisorder_hasLaw n).aemeasurable hu
  have h := hUp.add (goeDiagonalShift_sk_subgaussian hn beta)
  apply h.congr
  exact ae_of_all _ (fun z => by
    rw [primitiveGOEPressure_integral_eq_upstream]
    simp only [Function.comp_def,
      primitiveGOEPressure, ParisiGOEBridge.log_gibbsPartition_goe_eq, goeDiagonalShift]
    unfold SKConstantsOAI.SK.logPartition
    ring)

def pressureVarianceConstant (beta : ℝ) : ℝ := (Real.pi^2 / 4 + 1) * beta^2

def pressureVarianceProxy (n : ℕ) (beta : ℝ) : ℝ≥0 :=
  NNReal.mk (pressureVarianceConstant beta * n) (by unfold pressureVarianceConstant; positivity)

theorem pressure_variance_proxy_bound {n : ℕ} (hn : 0 < n) (beta : ℝ) :
    (NNReal.sqrt (SKConstantsOAI.SK.logPartitionProxy beta n) +
      NNReal.sqrt (NNReal.mk (beta^2 / 2) (by positivity)))^2 ≤
        pressureVarianceProxy n beta := by
  let X := SKConstantsOAI.SK.logPartitionProxy beta n
  let Y := NNReal.mk (beta^2 / 2) (show 0 ≤ beta^2 / 2 by positivity)
  have hsX : ((NNReal.sqrt X : ℝ≥0) : ℝ)^2 = (X : ℝ) := by
    exact_mod_cast NNReal.sq_sqrt X
  have hsY : ((NNReal.sqrt Y : ℝ≥0) : ℝ)^2 = (Y : ℝ) := by
    exact_mod_cast NNReal.sq_sqrt Y
  have h := sq_nonneg (((NNReal.sqrt X : ℝ≥0) : ℝ) - ((NNReal.sqrt Y : ℝ≥0) : ℝ))
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply NNReal.coe_le_coe.mp
  change (((NNReal.sqrt X : ℝ≥0) : ℝ) + ((NNReal.sqrt Y : ℝ≥0) : ℝ))^2 ≤ _
  simp only [pressureVarianceProxy, pressureVarianceConstant, NNReal.coe_mk]
  change ((NNReal.sqrt X : ℝ≥0) : ℝ)^2 = Real.pi^2 * beta^2 * (n : ℝ) / 8 at hsX
  change ((NNReal.sqrt Y : ℝ≥0) : ℝ)^2 = beta^2 / 2 at hsY
  nlinarith [mul_le_mul_of_nonneg_left hnR (sq_nonneg beta)]

theorem primitiveGOEPressure_centered_subgaussian_linear_proxy {n : ℕ}
    (hn : 0 < n) (beta : ℝ) :
    HasSubgaussianMGF (fun z => primitiveGOEPressure n beta z -
      ∫ w, primitiveGOEPressure n beta w ∂GaussianProposal.primitiveGaussian (Fin n × Fin n))
      (pressureVarianceProxy n beta) (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  have h := primitiveGOEPressure_centered_subgaussian hn beta
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (pressure_variance_proxy_bound hn beta))
      (sq_nonneg t)) (by norm_num)

theorem primitiveGOEPressure_mean_le_parisi {n : ℕ} (hn : 0 < n) (beta : ℝ) :
    (∫ z, primitiveGOEPressure n beta z ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
      (n : ℝ) * parisiContinuumFunctional beta (cdf (parisiEquilibriumMeasure beta : Measure ℝ)) := by
  have h := sk_expected_pressure_le_parisiEquilibrium n hn beta
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [div_le_iff₀ hnR] at h
  have he : (∫ W, Real.log (gibbsPartition beta W) ∂skDisorderLaw n) =
      ∫ z, primitiveGOEPressure n beta z ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
    unfold skDisorderLaw
    rw [integral_map (continuous_goeMatrix _).measurable.aemeasurable
      ((continuous_gibbsPartition beta).log (fun W => (gibbsPartition_pos beta W).ne')).measurable.aestronglyMeasurable]
    rfl
  rw [he] at h
  simpa only [mul_comm] using h

theorem primitiveGOEPressure_parisi_upper_tail {n : ℕ} (hn : 0 < n) (beta u : ℝ)
    (hu : 0 ≤ u) :
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
      {z | (n : ℝ) * parisiContinuumFunctional beta
        (cdf (parisiEquilibriumMeasure beta : Measure ℝ)) + u ≤ primitiveGOEPressure n beta z} ≤
      Real.exp (-u^2 / (2 * pressureVarianceConstant beta * (n : ℝ))) := by
  have h := (primitiveGOEPressure_centered_subgaussian_linear_proxy hn beta).measure_ge_le hu
  have hm := primitiveGOEPressure_mean_le_parisi hn beta
  have hsub : {z | (n : ℝ) * parisiContinuumFunctional beta
      (cdf (parisiEquilibriumMeasure beta : Measure ℝ)) + u ≤ primitiveGOEPressure n beta z} ⊆
      {z | u ≤ primitiveGOEPressure n beta z -
        ∫ w, primitiveGOEPressure n beta w ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    linarith
  apply (measureReal_mono hsub).trans
  convert h using 1
  simp only [pressureVarianceProxy, NNReal.coe_mk]
  congr 2
  ring

def parisiPressureUpperEvent (n : ℕ) (beta z : ℝ) :
    Set (EuclideanSpace ℝ (Fin n × Fin n)) :=
  {w | (n : ℝ) * parisiContinuumFunctional beta
    (cdf (parisiEquilibriumMeasure beta : Measure ℝ)) + (n : ℝ)^(1 - z) ≤
      primitiveGOEPressure n beta w}

theorem primitiveGOEPressure_parisi_stretched_tail {n : ℕ} (hn : 0 < n)
    (beta z : ℝ) (hbeta : beta ≠ 0) :
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
      (parisiPressureUpperEvent n beta z) ≤
      Real.exp (-(1 / (2 * pressureVarianceConstant beta)) * (n : ℝ)^(1 - 2 * z)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hC : 0 < pressureVarianceConstant beta := by
    unfold pressureVarianceConstant
    exact mul_pos (by positivity) (sq_pos_of_ne_zero hbeta)
  have h := primitiveGOEPressure_parisi_upper_tail hn beta ((n : ℝ)^(1 - z))
    (Real.rpow_nonneg hnR.le _)
  have he : ((n : ℝ)^(1 - z))^2 = (n : ℝ)^(1 - 2 * z) * (n : ℝ) := by
    calc
      _ = (n : ℝ)^((1 - z) * 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
        norm_num
      _ = (n : ℝ)^(1 - 2 * z) * (n : ℝ)^(1 : ℝ) := by
        rw [← Real.rpow_add hnR]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  apply h.trans_eq
  congr 1
  rw [he]
  field_simp

theorem parisiPressureUpperEvent_probability_tendsto_zero
    (beta z : ℝ) (hbeta : beta ≠ 0) (hz : z < 1 / 2) :
    Tendsto (fun n : ℕ => (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
      (parisiPressureUpperEvent n beta z)) atTop (𝓝 0) := by
  have hC : 0 < pressureVarianceConstant beta := by
    unfold pressureVarianceConstant
    exact mul_pos (by positivity) (sq_pos_of_ne_zero hbeta)
  have hd := (polynomial_stretched_decay (1 - 2 * z) 0
    (1 / (2 * pressureVarianceConstant beta)) (by linarith) (by positivity)).comp
      tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall (fun _ => measureReal_nonneg)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact primitiveGOEPressure_parisi_stretched_tail (by omega) beta z hbeta
  · simpa only [Function.comp_def, Real.rpow_zero, one_mul] using hd

end SKConstants
