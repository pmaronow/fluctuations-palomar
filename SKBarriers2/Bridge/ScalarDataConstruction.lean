module

public import SKBarriers2.Bridge.ScalarLaw
public import OAI.Probability.SKBarriers.Parisi.CDFSupportContact
public import FRSB.Main
public import QuantitativeFollowup.ScalarRootGrowth
public import QuantitativeFollowup.ParisiContinuousTime

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff
open OAI.SK.Analytic Paper

namespace SKBarriers2.Bridge

def scalarDataMeasure (β : ℝ) : ProbabilityMeasure ℝ :=
  realMeasure (FRSB.parisiMinimizer β 0)

theorem scalarData_mass_one (β : ℝ) :
    (scalarDataMeasure β : Measure ℝ) (Icc 0 1) = 1 :=
  realMeasure_mass_one _

theorem scalarData_minimizer (β : ℝ) :
    scalarCDFParisi β (cdf (scalarDataMeasure β : Measure ℝ)) = finiteParisiInf β :=
  (scalarCDFParisi_minimizer_iff β _).mpr (FRSB.isParisiMinimizer_selected β 0)

theorem scalarData_unique (β : ℝ) (hβ : 1 < β) :
    ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc 0 1) = 1 →
      scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β →
        ν = scalarDataMeasure β := by
  intro ν hν hmin
  exact scalarCDFParisi_minimizer_eq_selected β (zero_lt_one.trans hβ).ne' ν hν hmin

theorem support_realMeasure (μ : ParisiMeasure) :
    (realMeasure μ : Measure ℝ).support = FRSB.parisiSupport μ := by
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed (FRSB.parisiSupport_compact μ).isClosed
    rw [coe_realMeasure]
    apply (mem_ae_map_iff measurable_subtype_coe.aemeasurable
      (FRSB.parisiSupport_compact μ).isClosed.measurableSet).mpr
    have hs : ∀ᵐ x ∂(μ : Measure Overlap), x ∈ (μ : Measure Overlap).support :=
      Measure.support_mem_ae
    exact hs.mono (fun x hx => ⟨x, hx, rfl⟩)
  · rintro x ⟨y, hy, rfl⟩
    rw [(nhds_basis_opens (y : ℝ)).mem_measureSupport]
    intro U hU
    rw [coe_realMeasure, Measure.map_apply measurable_subtype_coe hU.2.measurableSet]
    exact ((μ : Measure Overlap).mem_support_iff_forall y).mp hy _
      ((hU.2.preimage continuous_subtype_val).mem_nhds hU.1)

theorem scalarData_support_interval (β : ℝ) (hβ : 1 < β) :
    ∃ q : ℝ, q ∈ Ioo (0 : ℝ) 1 ∧
      (scalarDataMeasure β : Measure ℝ).support = Icc 0 q := by
  obtain ⟨q, hq, c, ρ, _hc, _hatom, _hreg, _hpos, hsupp, _hmeas, _hnorm⟩ :=
    FRSB.fullRSB β hβ
  exact ⟨q, hq, (support_realMeasure _).trans hsupp⟩

def scalarDataEndpoint (β : ℝ) (hβ : 1 < β) : ℝ :=
  (scalarData_support_interval β hβ).choose

theorem scalarData_q_mem (β : ℝ) (hβ : 1 < β) :
    scalarDataEndpoint β hβ ∈ Ioo (0 : ℝ) 1 :=
  (scalarData_support_interval β hβ).choose_spec.1

theorem scalarData_support (β : ℝ) (hβ : 1 < β) :
    (scalarDataMeasure β : Measure ℝ).support = Icc 0 (scalarDataEndpoint β hβ) :=
  (scalarData_support_interval β hβ).choose_spec.2

private theorem scalarData_paper_support (β : ℝ) (hβ : 1 < β) :
    FRSB.parisiSupport (FRSB.parisiMinimizer β 0) = Icc 0 (scalarDataEndpoint β hβ) :=
  (support_realMeasure _).symm.trans (scalarData_support β hβ)

theorem scalarData_overlap_id (β : ℝ) (hβ : 1 < β) :
    ∀ t ∈ Icc 0 (scalarDataEndpoint β hβ),
      scalarCDFOverlap β (cdf (scalarDataMeasure β : Measure ℝ)) t = t := by
  intro t ht
  apply scalarCDFParisi_overlap_on_support (zero_lt_one.trans hβ).ne'
    (scalarDataMeasure β) (scalarData_mass_one β) (scalarData_minimizer β)
  rwa [scalarData_support β hβ]

theorem scalarData_contact₁ (β : ℝ) (hβ : 1 < β) :
    ∀ t ∈ Ioo 0 (scalarDataEndpoint β hβ),
      β ^ 2 * scalarLaw β (cdf (scalarDataMeasure β : Measure ℝ)) t
        (fun x => jet β (cdf (scalarDataMeasure β : Measure ℝ)) 2 t x ^ 2) = 1 :=
  (scalarLaw_contacts_of_minimizer β (zero_lt_one.trans hβ).ne' _
    (scalarData_minimizer β) _ (scalarData_q_mem β hβ)
    (scalarData_paper_support β hβ)).1

theorem scalarData_contact₂ (β : ℝ) (hβ : 1 < β) :
    ∀ t ∈ Ioo 0 (scalarDataEndpoint β hβ),
      scalarLaw β (cdf (scalarDataMeasure β : Measure ℝ)) t
        (fun x => jet β (cdf (scalarDataMeasure β : Measure ℝ)) 3 t x ^ 2) =
      2 * cdf (scalarDataMeasure β : Measure ℝ) t *
        scalarLaw β (cdf (scalarDataMeasure β : Measure ℝ)) t
          (fun x => jet β (cdf (scalarDataMeasure β : Measure ℝ)) 2 t x ^ 3) :=
  (scalarLaw_contacts_of_minimizer β (zero_lt_one.trans hβ).ne' _
    (scalarData_minimizer β) _ (scalarData_q_mem β hβ)
    (scalarData_paper_support β hβ)).2

theorem scalarData_smooth (β : ℝ) (hβ : 1 < β) :
    ContDiffOn ℝ ∞ (cdf (scalarDataMeasure β : Measure ℝ))
      (Ioo 0 (scalarDataEndpoint β hβ)) := by
  rw [scalarDataMeasure, cdf_realMeasure_eq]
  have hq : scalarDataEndpoint β hβ ∈ Ioo (0 : ℝ) 1 := scalarData_q_mem β hβ
  have hm : ContDiffOn ℝ ∞
      (FRSB.momentQuotient β (FRSB.parisiMinimizer β 0))
      (Icc 0 (scalarDataEndpoint β hβ)) :=
    (FRSB.moments_contDiffOn_on_support_interval β (zero_lt_one.trans hβ).ne' _
      (FRSB.isParisiMinimizer_selected β 0) _ hq.1 hq.2.le
      (scalarData_paper_support β hβ)).2
  apply (hm.mono Ioo_subset_Icc_self).congr
  intro t ht
  exact FRSB.parisiCDF_eq_momentQuotient_on_support_interval β
    (zero_lt_one.trans hβ).ne' _ (FRSB.isParisiMinimizer_selected β 0)
    _ hq.1 hq.2.le (scalarData_paper_support β hβ) t ⟨ht.1.le, ht.2⟩

theorem scalarData_lin_lower (β : ℝ) (hβ : 1 < β) :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧
      ∀ t ∈ Icc 0 T, c * t ≤ cdf (scalarDataMeasure β : Measure ℝ) t := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  obtain ⟨k, T, hk, hT, hbound⟩ :=
    QuantitativeFollowup.scalar_minimizer_cdf_linear_lower β hβ0 _
      (FRSB.isParisiMinimizer_selected β 0) _ (scalarData_q_mem β hβ)
      (scalarData_paper_support β hβ)
  refine ⟨k / β, T, div_pos hk hβ0, hT.1, ?_⟩
  intro t ht
  rw [scalarDataMeasure, cdf_realMeasure, div_mul_eq_mul_div]
  exact (div_le_iff₀ hβ0).mpr (by simpa only [mul_comm β] using hbound t ht)

theorem jet_succ_eq_parisiSpatialField (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    jet β (cdf (realMeasure μ : Measure ℝ)) (j + 1) t x =
      parisiSpatialField β μ (j + 1) (t, x) := by
  rw [jet_succ_eq_parisiSpatialJet β μ j t ht x,
    FRSB.parisiSpatialJet_eq_iteratedDeriv β μ (j + 1) t x ht,
    parisiSpatialField_eq_iteratedDeriv β μ (j + 1) t x ht]

theorem scalarData_jets (β : ℝ) :
    ∀ j : ℕ, ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      |jet β (cdf (scalarDataMeasure β : Measure ℝ)) (j + 1) t x| ≤ K := by
  intro j
  refine ⟨FRSB.uniformSpatialConstant β j, ?_⟩
  intro t ht x
  rw [scalarDataMeasure, jet_succ_eq_parisiSpatialField β _ j t ht x]
  exact FRSB.parisiSpatialField_uniform_bound β j _ (t, x)

private theorem jet_eq_spatialField_add_constant (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    jet β (cdf (realMeasure μ : Measure ℝ)) j t x =
      parisiSpatialField β μ j (t, x) + (if j = 0 then Real.log 2 else 0) := by
  cases j with
  | zero =>
    exact congrFun (Phi_eq_parisiPotential β μ t ht) x
  | succ j =>
    simpa only [Nat.succ_ne_zero, ite_false, add_zero] using
      jet_succ_eq_parisiSpatialField β μ j t ht x

theorem parisiSquareSpatialField_eq_jet_square (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    parisiSquareSpatialField β μ j (t, x) =
      iteratedDeriv j
        (fun y => jet β (cdf (realMeasure μ : Measure ℝ)) 1 t y ^ 2) x := by
  induction j generalizing x with
  | zero =>
    rw [parisiSquareSpatialField_zero, iteratedDeriv_zero,
      jet_succ_eq_parisiSpatialField β μ 0 t ht x, parisiSpatialField_one]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv j
        (fun y => jet β (cdf (realMeasure μ : Measure ℝ)) 1 t y ^ 2) =
        fun y => parisiSquareSpatialField β μ j (t, y) :=
      funext (fun y => (ih y).symm)
    rw [he]
    exact (hasDerivAt_parisiSquareSpatialField β μ j t x).deriv.symm

theorem scalarData_time_deriv (β : ℝ) (hβ : 1 < β) :
    ∀ j : ℕ, ∀ t ∈ Ioo 0 (scalarDataEndpoint β hβ), ∀ x,
      HasDerivAt (fun τ => jet β (cdf (scalarDataMeasure β : Measure ℝ)) j τ x)
        (-(β ^ 2 / 2) *
          (jet β (cdf (scalarDataMeasure β : Measure ℝ)) (j + 2) t x +
            cdf (scalarDataMeasure β : Measure ℝ) t *
              iteratedDeriv j
                (fun y => jet β (cdf (scalarDataMeasure β : Measure ℝ)) 1 t y ^ 2) x)) t := by
  intro j t ht x
  let μ : ParisiMeasure := FRSB.parisiMinimizer β 0
  have ht1 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨ht.1, ht.2.trans (scalarData_q_mem β hβ).2⟩
  have hc : ContinuousAt (parisiCDF μ) t :=
    QuantitativeFollowup.continuousAt_minimizer_cdf_on_support β
      (zero_lt_one.trans hβ).ne' μ (FRSB.isParisiMinimizer_selected β 0)
      _ (scalarData_q_mem β hβ) (scalarData_paper_support β hβ) t ht
  have hd : HasDerivAt (fun s => parisiSpatialField β μ j (s, x))
      (parisiTimeField β μ j (t, x)) t :=
    QuantitativeFollowup.hasDerivAt_parisiSpatialField_time_of_cdf β
      (zero_lt_one.trans hβ).ne' μ j t x ht1 hc
  have he : (fun s => jet β (cdf (realMeasure μ : Measure ℝ)) j s x) =ᶠ[𝓝 t]
      (fun s => parisiSpatialField β μ j (s, x) +
        (if j = 0 then Real.log 2 else 0)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht1] with s hs
    exact jet_eq_spatialField_add_constant β μ j s ⟨hs.1.le, hs.2.le⟩ x
  have hjet : HasDerivAt (fun s => jet β (cdf (realMeasure μ : Measure ℝ)) j s x)
      (parisiTimeField β μ j (t, x)) t :=
    (hd.add_const (if j = 0 then Real.log 2 else 0)).congr_of_eventuallyEq he
  have hfield : parisiTimeField β μ j (t, x) =
      -(β ^ 2 / 2) *
        (jet β (cdf (realMeasure μ : Measure ℝ)) (j + 2) t x +
          cdf (realMeasure μ : Measure ℝ) t *
            iteratedDeriv j
              (fun y => jet β (cdf (realMeasure μ : Measure ℝ)) 1 t y ^ 2) x) := by
    rw [parisiTimeField, cdf_realMeasure,
      jet_succ_eq_parisiSpatialField β μ (j + 1) t ⟨ht1.1.le, ht1.2.le⟩ x,
      parisiSquareSpatialField_eq_jet_square β μ j t ⟨ht1.1.le, ht1.2.le⟩ x]
  rw [hfield] at hjet
  exact hjet

end SKBarriers2.Bridge

namespace SKBarriers2
open Bridge

def scalarData (β : ℝ) (hβ : 1 < β) : ScalarData β where
  μ := scalarDataMeasure β
  mass_one := scalarData_mass_one β
  minimizer := scalarData_minimizer β
  unique := scalarData_unique β hβ
  q := scalarDataEndpoint β hβ
  q_mem := scalarData_q_mem β hβ
  support := scalarData_support β hβ
  smooth := scalarData_smooth β hβ
  lin_lower := scalarData_lin_lower β hβ
  jets := scalarData_jets β
  time_deriv := scalarData_time_deriv β hβ
  overlap_id := scalarData_overlap_id β hβ
  contact₁ := scalarData_contact₁ β hβ
  contact₂ := scalarData_contact₂ β hβ

theorem scalarData_exists (β : ℝ) (hβ : 1 < β) : Nonempty (ScalarData β) :=
  ⟨scalarData β hβ⟩

end SKBarriers2
