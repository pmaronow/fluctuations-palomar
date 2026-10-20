module

public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSupportContact
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSquareSusceptibility
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFOriginStability
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSupportGap
import Mathlib

/-!
Support stability from the actual CDF variational problem.  OpenAI's CDF
potential has derivative `q - scalarCDFOverlap q` on `[0,1]`; the potential is
unscaled.  Its actual support minimum and contact identities force the right
overlap derivative to be at most one at every support point below one,
including zero.

The final susceptibility inequality takes the primitive overlap derivative
identity explicitly.  This module does not prove that derivative identity or
assume the susceptibility inequality itself.  At zero the identity must be a
right derivative because the real-valued overlap extension is clamped.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SKConstants.ParisiSupportAT

/-- A stationary right minimum has nonnegative right curvature.  The derivative
function need only agree with the derivative of the potential on the interval. -/
theorem secondDerivative_nonneg_of_right_minimum {f g : ℝ → ℝ} {q b d : ℝ}
    (hqb : q < b) (hf : ContinuousOn f (Icc q b))
    (hfg : ∀ r ∈ Ioo q b, HasDerivAt f (g r) r)
    (hg : HasDerivWithinAt g d (Ici q) q) (hgq : g q = 0)
    (hmin : ∀ r ∈ Icc q b, f q ≤ f r) : 0 ≤ d := by
  by_contra hd
  have hdneg : d < 0 := lt_of_not_ge hd
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hg.Ioi_of_Ici
  have hneg : ∀ᶠ r in 𝓝[>] q, g r < 0 := by
    filter_upwards [hslope.eventually (eventually_lt_nhds hdneg),
      self_mem_nhdsWithin] with r hr hqr
    rw [slope_def_field, hgq, sub_zero] at hr
    simpa only [zero_mul] using (div_lt_iff₀ (sub_pos.mpr hqr)).mp hr
  obtain ⟨u, hqu, hgu⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hqb).mp hneg
  have hfu : ContinuousOn f (Icc q u) := hf.mono
    (fun r hr => ⟨hr.1, hr.2.trans hqu.2⟩)
  have hstrict := strictAntiOn_of_deriv_neg (convex_Icc q u) hfu
    (fun r hr => by
      rw [interior_Icc] at hr
      rw [(hfg r ⟨hr.1, hr.2.trans_le hqu.2⟩).deriv]
      exact hgu hr)
  exact (not_lt_of_ge (hmin u ⟨hqu.1.le, hqu.2⟩))
    (hstrict ⟨le_rfl, hqu.1.le⟩ ⟨hqu.1.le, le_rfl⟩ hqu.1)

/-- At a contact point of an overlap function and the diagonal, a right
minimum of the corresponding potential forces the overlap's right derivative
to be at most one. -/
theorem overlapDerivative_le_one_of_contact_minimum
    {f Γ : ℝ → ℝ} {q b d : ℝ} (hqb : q < b)
    (hf : ContinuousOn f (Icc q b))
    (hdf : ∀ r ∈ Ioo q b, HasDerivAt f (r - Γ r) r)
    (hΓ : HasDerivWithinAt Γ d (Ici q) q) (hcontact : Γ q = q)
    (hmin : ∀ r ∈ Icc q b, f q ≤ f r) : d ≤ 1 := by
  have hg : HasDerivWithinAt (fun r => r - Γ r) (1 - d) (Ici q) q :=
    (hasDerivAt_id q).hasDerivWithinAt.sub hΓ
  have h := secondDerivative_nonneg_of_right_minimum hqb hf hdf hg
    (by simp only [hcontact, sub_self]) hmin
  linarith

open SKConstantsOAI.SK.Analytic

/-- At time zero the actual square-susceptibility average is deterministic. -/
theorem scalarCDFSusceptibilitySquareAverage_zero (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α) :
    scalarCDFSusceptibilitySquareAverage β α 0 =
      (scalarCDFHessian β α 0 1 0) ^ 2 := by
  have HE := scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β ha hmono 0 1 le_rfl)
    (scalarCDFValue_lipschitz β ha hmono 0 1 le_rfl)
    (scalarCDFHessian_square_lipschitz β ha hmono 0 1 le_rfl)
    (B := 1) (scalarCDFHessian_square_bound β ha hmono 0 1 le_rfl)
    β ha hmono [] (by simp) 0 0 (by norm_num) rfl trivial 0
  simpa only [scalarCDFSusceptibilitySquareAverage, sub_zero, Real.toNNReal_one,
    Real.toNNReal_zero, scalarTimeChainAverage, List.length_nil, scalarHierarchyAverage] using HE

/-- The actual upstream origin stability proof gives the AT square-average
bound at zero without an additional overlap-derivative premise. -/
theorem scalarCDFParisi_AT_at_zero {β : ℝ} (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β) :
    β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) 0 ≤ 1 := by
  rw [scalarCDFSusceptibilitySquareAverage_zero β
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) (cdf (μ : Measure ℝ)).mono]
  exact scalarCDFParisi_origin_stability hβ μ hμ hmin

/-- Actual variational support minima and support contact bound any specified
right derivative of the actual CDF overlap. -/
theorem scalarCDFParisi_overlapDerivative_le_one_on_support
    {β : ℝ} (hβ : β ≠ 0) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    {q d : ℝ} (hqs : q ∈ (μ : Measure ℝ).support) (hq1 : q < 1)
    (hderiv : HasDerivWithinAt (scalarCDFOverlap β (cdf (μ : Measure ℝ)))
      d (Ici q) q) : d ≤ 1 := by
  have hs := scalarCDFParisi_support_minima hβ μ hμ hmin q hqs
  have hΓ := scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (supported_probability_cdf_one μ hμ)
  apply overlapDerivative_le_one_of_contact_minimum hq1
    (scalarCDFPotential_continuous hΓ).continuousOn
    (fun r hr => by
      have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hs.1.1.trans hr.1.le, hr.2.le⟩
      simpa only [cdfGradientTest_eq hr01] using scalarCDFPotential_hasDerivAt hΓ r)
    hderiv (scalarCDFParisi_overlap_on_support hβ μ hμ hmin hqs)
  intro r hr
  exact hs.2.2 r ⟨hs.1.1.trans hr.1, hr.2⟩

/-- The AT susceptibility bound at an actual support point follows from the
primitive right overlap derivative identity.  Zero is included. -/
theorem scalarCDFParisi_AT_on_support_of_right_overlap_derivative
    {β : ℝ} (hβ : β ≠ 0) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    {q : ℝ} (hqs : q ∈ (μ : Measure ℝ).support) (hq1 : q < 1)
    (hderiv : HasDerivWithinAt (scalarCDFOverlap β (cdf (μ : Measure ℝ)))
      (β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) q)
      (Ici q) q) :
    β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) q ≤ 1 :=
  scalarCDFParisi_overlapDerivative_le_one_on_support hβ μ hμ hmin hqs hq1 hderiv

/-- Interior version accepting an ordinary derivative identity. -/
theorem scalarCDFParisi_AT_on_interior_support_of_overlap_derivative
    {β : ℝ} (hβ : β ≠ 0) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    {q : ℝ} (hqs : q ∈ (μ : Measure ℝ).support) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hderiv : HasDerivAt (scalarCDFOverlap β (cdf (μ : Measure ℝ)))
      (β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) q) q) :
    β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) q ≤ 1 :=
  scalarCDFParisi_AT_on_support_of_right_overlap_derivative hβ μ hμ hmin hqs hq.2
    hderiv.hasDerivWithinAt

/-- Interior overlap derivatives suffice for all support points below one:
the endpoint zero uses the independently proved actual origin stability. -/
theorem scalarCDFParisi_AT_on_support_of_interior_overlap_derivatives
    {β : ℝ} (hβ : β ≠ 0) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hderiv : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (scalarCDFOverlap β (cdf (μ : Measure ℝ)))
        (β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) r) r)
    {q : ℝ} (hqs : q ∈ (μ : Measure ℝ).support) (hq1 : q < 1) :
    β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) q ≤ 1 := by
  by_cases hq0 : q = 0
  · subst q
    exact scalarCDFParisi_AT_at_zero hβ μ hμ hmin
  have hq01 : q ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (scalarCDFParisi_support_minima hβ μ hμ hmin q hqs).1.1
      (Ne.symm hq0), hq1⟩
  exact scalarCDFParisi_AT_on_interior_support_of_overlap_derivative hβ μ hμ hmin
    hqs hq01 (hderiv q hq01)

/-- Every actual minimizing support point lies below one. -/
theorem scalarCDFParisi_support_lt_one {β : ℝ} (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    {q : ℝ} (hqs : q ∈ (μ : Measure ℝ).support) : q < 1 := by
  obtain ⟨qmax, hmax, hbound⟩ := scalarCDFParisi_support_away_one hβ μ hμ hmin
  exact ((hbound hqs).2).trans_lt hmax.2

/-- On the entire actual minimizing support the primitive interior derivative
identity implies AT.  The origin and support gap are already actual upstream
theorems, so no endpoint derivative or support-bound premise is needed. -/
theorem scalarCDFParisi_AT_on_support_of_overlap_derivatives
    {β : ℝ} (hβ : β ≠ 0) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hderiv : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (scalarCDFOverlap β (cdf (μ : Measure ℝ)))
        (β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) r) r)
    {q : ℝ} (hqs : q ∈ (μ : Measure ℝ).support) :
    β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) q ≤ 1 :=
  scalarCDFParisi_AT_on_support_of_interior_overlap_derivatives hβ μ hμ hmin hderiv
    hqs (scalarCDFParisi_support_lt_one hβ μ hμ hmin hqs)

/-- The support bound also holds almost everywhere for the actual minimizer. -/
theorem scalarCDFParisi_AT_ae_of_overlap_derivatives
    {β : ℝ} (hβ : β ≠ 0) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hderiv : ∀ r ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (scalarCDFOverlap β (cdf (μ : Measure ℝ)))
        (β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) r) r) :
    ∀ᵐ q ∂(μ : Measure ℝ),
      β ^ 2 * scalarCDFSusceptibilitySquareAverage β (cdf (μ : Measure ℝ)) q ≤ 1 := by
  have H : ∀ᵐ q ∂(μ : Measure ℝ), q ∈ (μ : Measure ℝ).support :=
    (μ : Measure ℝ).support_mem_ae
  exact H.mono (fun _ hqs => scalarCDFParisi_AT_on_support_of_overlap_derivatives
    hβ μ hμ hmin hderiv hqs)

end SKConstants.ParisiSupportAT
