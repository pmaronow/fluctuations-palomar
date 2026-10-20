module
public import SKConstants.ParisiPhysicalNormalization
public import SKConstants.ParisiSupportAT

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
open SKConstantsOAI.SK.Analytic

theorem probability_cdf_one_of_support_bound (μ : ProbabilityMeasure ℝ) (q : ℝ)
    (hbound : (μ : Measure ℝ).support ⊆ Iic q) :
    cdf (μ : Measure ℝ) q = 1 := by
  have hs : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ (μ : Measure ℝ).support :=
    (μ : Measure ℝ).support_mem_ae
  have hae : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Iic q := hs.mono hbound
  have H : (μ : Measure ℝ) (Iic q) = 1 := by
    simpa only [measure_univ] using
      (ae_mem_iff_measure_eq measurableSet_Iic.nullMeasurableSet).mp hae
  rw [cdf_eq_real, Measure.real, H, ENNReal.toReal_one]

theorem parisiEquilibriumMeasure_upstream_spec (β : ℝ) :
    (parisiEquilibriumMeasure β : Measure ℝ) (Icc (0 : ℝ) 1) = 1 ∧
      scalarCDFParisi β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) =
        finiteParisiInf β := by
  exact ⟨(parisiEquilibriumMeasure_spec β).1, by
    rw [← parisiContinuumFunctional_eq_upstream]
    exact (parisiEquilibriumMeasure_spec β).2.1⟩

theorem exists_parisiEquilibrium_greatest_support (β : ℝ) (hβ : β ≠ 0) :
    ∃ Q : ℝ, Q ∈ Ico (0 : ℝ) 1 ∧
      IsGreatest (parisiEquilibriumMeasure β : Measure ℝ).support Q ∧
      (parisiEquilibriumMeasure β : Measure ℝ).support ⊆ Icc 0 Q ∧
      cdf (parisiEquilibriumMeasure β : Measure ℝ) Q = 1 := by
  let μ := parisiEquilibriumMeasure β
  have hμ := (parisiEquilibriumMeasure_upstream_spec β).1
  have hmin := (parisiEquilibriumMeasure_upstream_spec β).2
  have HS := Measure.support_subset_of_isClosed (μ := (μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  have HC : IsCompact (μ : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (μ : Measure ℝ).isClosed_support HS
  have h0 := scalarCDFParisi_zero_mem_support hβ μ hμ hmin
  obtain ⟨Q, hQ⟩ := HC.exists_isGreatest ⟨0, h0⟩
  have hQ1 := ParisiSupportAT.scalarCDFParisi_support_lt_one hβ μ hμ hmin hQ.1
  have hbound : (μ : Measure ℝ).support ⊆ Icc 0 Q :=
    fun x hx => ⟨(HS hx).1, hQ.2 hx⟩
  exact ⟨Q, ⟨(HS hQ.1).1, hQ1⟩, hQ, hbound,
    probability_cdf_one_of_support_bound μ Q (fun x hx => (hbound hx).2)⟩

theorem parisiPhysicalGradient_at_cdf_one (β : ℝ) (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (v : ℝ) (hv : v ∈ Icc 0 (β^2))
    (hcut : cdf (μ : Measure ℝ) (v / β^2) = 1) :
    scalarCDFGradient β (cdf (μ : Measure ℝ)) (v / β^2)
      (Real.toNNReal (1-v/β^2)) = scalarMagnetization := by
  funext y
  have H := (parisiPhysicalValue_spatial_derivatives β hβ μ v hv).1 y
  rw [parisiPhysicalValue_at_cdf_one β hβ μ v hv hcut] at H
  exact H.unique ((scalarSpinTerminal_hasDerivAt y).add_const ((β^2-v)/2))

theorem parisiPhysicalHessian_zero_of_cdf_zero_one (β : ℝ) (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (hcut : cdf (μ : Measure ℝ) 0 = 1) :
    scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0 = 1 := by
  have H := (parisiPhysicalValue_spatial_derivatives β hβ μ 0
    ⟨le_rfl, sq_nonneg β⟩).2.1 0
  have HG := parisiPhysicalGradient_at_cdf_one β hβ μ 0
    ⟨le_rfl, sq_nonneg β⟩ (by simpa only [zero_div] using hcut)
  simp only [zero_div, sub_zero, Real.toNNReal_one] at HG H
  rw [HG] at H
  simpa only [Real.cosh_zero, one_pow, div_one] using
    H.unique (scalarMagnetization_hasDerivAt 0)

theorem parisiEquilibrium_greatest_support_pos (β : ℝ) (hβ : 1 < β)
    {Q : ℝ} (hQ : Q ∈ Ico (0 : ℝ) 1)
    (hbound : (parisiEquilibriumMeasure β : Measure ℝ).support ⊆ Icc 0 Q) : 0 < Q := by
  have hb : β ≠ 0 := ne_of_gt (lt_trans zero_lt_one hβ)
  by_contra h
  have hQ0 : Q = 0 := le_antisymm (le_of_not_gt h) hQ.1
  have hcut := probability_cdf_one_of_support_bound (parisiEquilibriumMeasure β) 0
    (fun x hx => by change x ≤ 0; simpa only [hQ0] using (hbound hx).2)
  have HH := parisiPhysicalHessian_zero_of_cdf_zero_one β hb
    (parisiEquilibriumMeasure β) hcut
  have H := scalarCDFParisi_origin_stability hb (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
    (parisiEquilibriumMeasure_upstream_spec β).2
  rw [HH, one_pow, mul_one] at H
  nlinarith

theorem exists_parisiEquilibrium_physical_endpoint (β : ℝ) (hβ : 1 < β) :
    ∃ Q : ℝ, Q ∈ Ioo (0 : ℝ) 1 ∧
      IsGreatest (parisiEquilibriumMeasure β : Measure ℝ).support Q ∧
      (parisiEquilibriumMeasure β : Measure ℝ).support ⊆ Icc 0 Q ∧
      cdf (parisiPhysicalOrderLaw β (parisiEquilibriumMeasure β)) (β^2*Q) = 1 ∧
      parisiPhysicalValue β (parisiEquilibriumMeasure β) (β^2*Q) =
        fun y => Real.log (2 * Real.cosh y) + (β^2 - β^2*Q) / 2 := by
  have hb : β ≠ 0 := ne_of_gt (lt_trans zero_lt_one hβ)
  obtain ⟨Q,hQ,hgreatest,hbound,hcut⟩ := exists_parisiEquilibrium_greatest_support β hb
  have hQpos := parisiEquilibrium_greatest_support_pos β hβ hQ hbound
  have hdiv : β^2*Q/β^2 = Q := by field_simp
  have hv : β^2*Q ∈ Icc (0 : ℝ) (β^2) :=
    ⟨mul_nonneg (sq_nonneg β) hQ.1, by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hQ.2.le (sq_nonneg β)⟩
  refine ⟨Q, ⟨hQpos,hQ.2⟩, hgreatest, hbound, ?_, ?_⟩
  · rw [parisiPhysicalOrderLaw_cdf β hb, hdiv, hcut]
  · exact parisiPhysicalValue_at_cdf_one β hb _ _ hv (by rwa [hdiv])

def parisiEquilibriumSupportEndpoint (β : ℝ) : ℝ :=
  sSup (parisiEquilibriumMeasure β : Measure ℝ).support

theorem parisiEquilibriumSupportEndpoint_spec (β : ℝ) (hβ : 1 < β) :
    parisiEquilibriumSupportEndpoint β ∈ Ioo (0 : ℝ) 1 ∧
      IsGreatest (parisiEquilibriumMeasure β : Measure ℝ).support
        (parisiEquilibriumSupportEndpoint β) ∧
      (parisiEquilibriumMeasure β : Measure ℝ).support ⊆
        Icc 0 (parisiEquilibriumSupportEndpoint β) ∧
      cdf (parisiPhysicalOrderLaw β (parisiEquilibriumMeasure β))
        (β^2 * parisiEquilibriumSupportEndpoint β) = 1 ∧
      parisiPhysicalValue β (parisiEquilibriumMeasure β)
        (β^2 * parisiEquilibriumSupportEndpoint β) =
        fun y => Real.log (2 * Real.cosh y) +
          (β^2 - β^2 * parisiEquilibriumSupportEndpoint β) / 2 := by
  obtain ⟨Q, hQ, hg, hs, hc, hv⟩ := exists_parisiEquilibrium_physical_endpoint β hβ
  have he : parisiEquilibriumSupportEndpoint β = Q := hg.csSup_eq
  rw [he]
  exact ⟨hQ, hg, hs, hc, hv⟩

end SKConstants
