module

public import SKConstants.Completion.LC4a.ReplayInformation
public import SKConstants.Completion.LM4.All

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LM4b
open SKConstantsOAI.ZeroTemperatureSK LC4a

variable {Ω : Type*} [MeasurableSpace Ω]

def replayRowLeftSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (i : Fin (ranks + q)) (l : ℕ) : GrowingReplaySpace Ω δ ranks q → ℝ :=
  brownianVectorContinuousCoordinateLeftSum W.B i
    (fun t u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q t u i)
    (brownianDyadicGrid V) 1 l

def replayRowBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (i : Fin (ranks + q)) : GrowingReplaySpace Ω δ ranks q → ℝ :=
  brownianVectorContinuousCoordinateQuadraticVariation W.B i
    (fun t u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q t u i) V

def IsReplayRowIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (i : Fin (ranks + q)) (J : GrowingReplaySpace Ω δ ranks q → ℝ) : Prop :=
  MemLp J 2 (growingReplayUnlinkedLaw W δ ranks q) ∧
    (∀ l, Integrable (fun u => (replayRowLeftSum W β hβ δ hδ ranks q V i l u - J u)^2)
      (growingReplayUnlinkedLaw W δ ranks q)) ∧
    Tendsto (fun l => ∫ u, (replayRowLeftSum W β hβ δ hδ ranks q V i l u - J u)^2
      ∂growingReplayUnlinkedLaw W δ ranks q) atTop (𝓝 0)

theorem replayRowBracket_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (i : Fin (ranks + q)) (u : GrowingReplaySpace Ω δ ranks q) :
    0 ≤ replayRowBracket W β hβ δ hδ ranks q V i u ∧
      replayRowBracket W β hβ δ hδ ranks q V i u ≤ 4 * (V : ℝ) := by
  simpa only [replayRowBracket, show (2 : ℝ)^2 = 4 by norm_num] using
    brownianVectorContinuousCoordinateQuadraticVariation_bounds W.B i
      (fun t u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q t u i)
      2 (fun t u => replayDCoefficient_bound W β hβ δ hδ ranks q t u i) V u

theorem replayRowLeftSum_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (i : Fin (ranks + q)) (l : ℕ) :
    HasSubgaussianMGF (replayRowLeftSum W β hβ δ hδ ranks q V i l) (4 * V)
      (growingReplayUnlinkedLaw W δ ranks q) := by
  let := W.isProbability
  let P := parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q
  let t := (brownianDyadicGrid V).time l
  let H := brownianVectorContinuousMeshCoefficient
    (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) t
  have hH (k : ℕ) : Measurable (H k) := measurable_replayDCoefficient W β hβ δ hδ ranks q _
  have hsnd := (measurePreserving_snd (μ := P)
    (ν := Measure.pi (fun _ : Fin (ranks + q) => W.law))).hasLaw
  have hX (k : ℕ) : HasLaw
      (fun u : GrowingReplaySpace Ω δ ranks q => brownianVectorMeshIncrement W.B t k u.2 i)
      (gaussianReal 0 (brownianMeshVariance t k)) (growingReplayUnlinkedLaw W δ ranks q) :=
    ((measurePreserving_eval (fun _ : Fin (ranks + q) =>
      gaussianReal 0 (brownianMeshVariance t k)) i).hasLaw.comp
        (brownianVectorMeshIncrement_hasLaw W.law W.B W.brownian.toIsPreBrownianReal
          t (brownianDyadicGrid V |>.monotone l) k)).comp hsnd
  have hcoef (k : ℕ) : AEMeasurable
      (fun u : GrowingReplaySpace Ω δ ranks q => brownianVectorStaticCoefficient W.B t H k u i)
      (growingReplayUnlinkedLaw W δ ranks q) := ((measurable_pi_apply i).comp
    (measurable_brownianVectorStaticCoefficient W.B W.measurable t H hH k)).aemeasurable
  have hcap (u : GrowingReplaySpace Ω δ ranks q) :
      brownianVectorCoordinateVariation W.B t H i (1 * 2^l) u ≤ 4 * (V : ℝ) := by
    have h := brownianVectorContinuousCoordinateVariation_le W.B i
      (fun s u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q s u i)
      2 (fun s u => replayDCoefficient_bound W β hβ δ hδ ranks q s u i)
      (brownianDyadicGrid V) 1 l u
    have he : brownianVectorCoordinateVariation W.B t H i (1 * 2^l) u =
        brownianVectorCoordinatePredictableVariation W.B i (brownianDyadicGrid V |>.time l)
          (brownianVectorContinuousCoordinateMeshCoefficient
            (fun s u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q s u i)
            (brownianDyadicGrid V |>.time l)) (1 * 2^l) u := rfl
    rw [he]
    simpa only [brownianDyadicGrid_horizon, show (2 : ℝ)^2 = 4 by norm_num] using h
  have hi := brownianVectorCoordinate_state_indep_increment P W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable t
    (brownianDyadicGrid V |>.monotone l) H hH i
  constructor
  · intro θ
    exact (predictableGaussianSum_mgf_bound _ _ _ _ hX hcoef hi θ (1 * 2^l)
      (4 * (V : ℝ)) (ae_of_all _ hcap)).1
  · intro θ
    have hh := (predictableGaussianSum_mgf_bound _ _ _ _ hX hcoef hi θ (1 * 2^l)
        (4 * (V : ℝ)) (ae_of_all _ hcap)).2
    have he : predictableGaussianSum
        (fun k (u : GrowingReplaySpace Ω δ ranks q) => brownianVectorMeshIncrement W.B t k u.2 i)
        (fun k u => brownianVectorStaticCoefficient W.B t H k u i) (1 * 2^l) =
        replayRowLeftSum W β hβ δ hδ ranks q V i l := rfl
    rw [he] at hh
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_comm (θ^2)] using hh

theorem replayRowIntegral_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (i : Fin (ranks + q)) (J : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hJ : IsReplayRowIntegral W β hβ δ hδ ranks q V i J) :
    HasSubgaussianMGF J (4 * V) (growingReplayUnlinkedLaw W δ ranks q) :=
  hasSubgaussianMGF_of_tendsto_integral_sq
    (replayRowLeftSum_hasSubgaussianMGF W β hβ δ hδ ranks q V i)
    hJ.2.1 hJ.2.2 tendsto_const_nhds

theorem replayRowIntegral_exists (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks + q)) :
    ∃ J : GrowingReplaySpace Ω δ ranks q → ℝ,
      Measurable J ∧ IsReplayRowIntegral W β hβ δ hδ ranks q V i J := by
  let := W.isProbability
  obtain ⟨J, hJ, hJi, hlim⟩ := brownianVectorContinuousCoordinateLeftSum_exists_L2_limit
    (parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q) W.law W.B i
    W.brownian.toIsPreBrownianReal W.measurable
    (fun t u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q t u i)
    (fun t => (measurable_pi_apply i).comp (measurable_replayDCoefficient W β hβ δ hδ ranks q t))
    2 (fun t u => replayDCoefficient_bound W β hβ δ hδ ranks q t u i)
    (replayDCoefficient_continuous_ae W β hβ δ hδ ranks q i)
    (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l d j _ => brownianDyadicGrid_left_le V l d j)
  let K := hJ.aestronglyMeasurable.mk J
  have he : J =ᵐ[growingReplayUnlinkedLaw W δ ranks q] K := hJ.aestronglyMeasurable.ae_eq_mk
  refine ⟨K, hJ.aestronglyMeasurable.measurable_mk, ?_, ?_, ?_⟩
  · exact hJ.ae_eq he
  · intro l
    exact (hJi l).congr (he.mono (fun u hu => by dsimp only; rw [hu]; rfl))
  · convert hlim using 1
    funext l
    exact integral_congr_ae (he.mono (fun u hu => by dsimp only; rw [hu]; rfl))

theorem replayRowBracket_measurable_version
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (i : Fin (ranks + q)) :
    ∃ Q : GrowingReplaySpace Ω δ ranks q → ℝ, Measurable Q ∧
      Q =ᵐ[growingReplayUnlinkedLaw W δ ranks q] replayRowBracket W β hβ δ hδ ranks q V i ∧
      (∀ᵐ u ∂growingReplayUnlinkedLaw W δ ranks q, 0 ≤ Q u ∧ Q u ≤ 4 * (V : ℝ)) := by
  let := W.isProbability
  have hm := (brownianVectorContinuousCoordinateVariation_tendsto_L2
    (parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q) W.law W.B i
    W.brownian.toIsPreBrownianReal W.measurable
    (fun t u => actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q t u i)
    (fun t => (measurable_pi_apply i).comp (measurable_replayDCoefficient W β hβ δ hδ ranks q t))
    2 (fun t u => replayDCoefficient_bound W β hβ δ hδ ranks q t u i)
    (replayDCoefficient_continuous_ae W β hβ δ hδ ranks q i)
    (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l j _ => brownianDyadicGrid_width_le V l j)).1
  simp only [brownianDyadicGrid_horizon] at hm
  refine ⟨hm.mk _, hm.measurable_mk, hm.ae_eq_mk.symm, ?_⟩
  filter_upwards [hm.ae_eq_mk] with u hu
  rw [← hu]
  exact replayRowBracket_bounds W β hβ δ hδ ranks q V i u

theorem sum_replayRowIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (J : Fin (ranks + q) → GrowingReplaySpace Ω δ ranks q → ℝ)
    (hJ : ∀ i, IsReplayRowIntegral W β hβ δ hδ ranks q V i (J i)) :
    IsGrowingReplayDIntegral W β hβ δ hδ ranks q V (fun u => ∑ i, J i u) := by
  have hmem (i : Fin (ranks + q)) (l : ℕ) :
      MemLp (replayRowLeftSum W β hβ δ hδ ranks q V i l) 2
        (growingReplayUnlinkedLaw W δ ranks q) :=
    (replayRowLeftSum_hasSubgaussianMGF W β hβ δ hδ ranks q V i l).memLp 2
  have he (l : ℕ) (u : GrowingReplaySpace Ω δ ranks q) :
      growingReplayDLeftSum W β hβ δ hδ ranks q V l u =
        ∑ i, replayRowLeftSum W β hβ δ hδ ranks q V i l u :=
    brownianVectorContinuousLeftSum_eq_sum_coordinate _ _ _ _ _ _
  refine ⟨memLp_finsetSum Finset.univ (fun i _ => (hJ i).1), ?_, ?_⟩
  · intro l
    simp_rw [he, ← Finset.sum_sub_distrib]
    exact integrable_sq_finset_sum Finset.univ
      (fun i _ => ((hmem i l).sub (hJ i).1).aemeasurable)
      (fun i _ => (hJ i).2.1 l)
  · simp_rw [he, ← Finset.sum_sub_distrib]
    exact tendsto_integral_sq_finset_sum Finset.univ
      (fun i _ l => ((hmem i l).sub (hJ i).1).aemeasurable)
      (fun i _ l => (hJ i).2.1 l) (fun i _ => (hJ i).2.2)

theorem growingReplayDIntegral_eq_sum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I)
    (J : Fin (ranks + q) → GrowingReplaySpace Ω δ ranks q → ℝ)
    (hJ : ∀ i, IsReplayRowIntegral W β hβ δ hδ ranks q V i (J i)) :
    I =ᵐ[growingReplayUnlinkedLaw W δ ranks q] (fun u => ∑ i, J i u) :=
  growingReplayDIntegral_unique W β hβ δ hδ ranks q V I _ hI
    (sum_replayRowIntegral W β hβ δ hδ ranks q V J hJ)

theorem growingReplayInformation_eq_sum_rows
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I)
    (J : Fin (ranks + q) → GrowingReplaySpace Ω δ ranks q → ℝ)
    (hJ : ∀ i, IsReplayRowIntegral W β hβ δ hδ ranks q V i (J i)) :
    growingReplayInformation W β hβ δ hδ ranks q V I =ᵐ[
        growingReplayLinkedLaw W β hβ δ ranks q V]
      (fun u => ∑ i, (Real.log (actualParisiSpinLinkDensity β (u.1.2 i) V
        (growingReplayFieldAt W β hβ δ ranks q V u i)) - J i u +
          replayRowBracket W β hβ δ hδ ranks q V i u / 2)) := by
  have he := (withDensity_absolutelyContinuous
    (μ := growingReplayUnlinkedLaw W δ ranks q)
    (f := fun u => ENNReal.ofReal (growingReplayLinkDensity W β hβ δ ranks q V u))).ae_le
      (growingReplayDIntegral_eq_sum W β hβ δ hδ ranks q V I hI J hJ)
  filter_upwards [he] with u hu
  rw [growingReplayInformation_eq, hu]
  simp only [growingReplayLinkDensity, Real.log_prod (fun i _ =>
    (actualParisiSpinLinkDensity_pos β (u.1.2 i) V _).ne'),
    growingReplayDBracket, brownianVectorContinuousQuadraticVariation,
    ← Finset.sum_div, replayRowBracket, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end SKConstants.Completion.LM4b
