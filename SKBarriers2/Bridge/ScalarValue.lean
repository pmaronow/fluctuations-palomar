module

public import SKBarriers2.Bridge.ScalarValueBasic
public import OAI.Probability.SKBarriers.Scalar.PartitionChain
public import OAI.Probability.SKBarriers.Scalar.DyadicCDFStability
public import OAI.Probability.SKBarriers.Parisi.CDFIntervalConvergence
public import FRSB.ConstantMassEvolution
public import FRSB.ParisiGridTopology
public import FRSB.ParisiStrictConvexity
public import Paper.ParisiPDEFormula

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open OAI.SK.Analytic Paper

namespace SKBarriers2.Bridge

open ColeHopfFoundation.ProbabilityTheory

theorem scalarStep_eq_coleHopf (m v : ℝ) {A : ℝ → ℝ} (hA : Measurable A) (x : ℝ) :
    scalarStep m v A x = coleHopf m (v ^ 2).toNNReal A x := by
  have hv : NNReal.mk (v ^ 2) (sq_nonneg v) = (v ^ 2).toNNReal := by
    apply NNReal.coe_injective
    exact (Real.coe_toNNReal _ (sq_nonneg v)).symm
  by_cases hm : m = 0
  · subst m
    simp only [scalarStep, gaussianStep, ite_true, coleHopf_zero]
    simpa only [Function.comp_apply, hv] using integral_gaussian_mul v
      (hA.comp (measurable_const_add x)).stronglyMeasurable
  · have hint : (∫ y, Real.exp (m * A (x + v * y)) ∂gaussianReal 0 1) =
        ∫ y, Real.exp (m * A (x + y)) ∂gaussianReal 0 (v ^ 2).toNNReal := by
      simpa only [Function.comp_apply, hv] using integral_gaussian_mul v
        ((hA.comp (measurable_const_add x)).const_mul m).exp.stronglyMeasurable
    rw [scalarStep, gaussianStep, ite_eq_right hm, positiveGaussianLogStep,
      coleHopf_of_ne hm, hint]
    ring

theorem scalarTimeStep_eq_coleHopf (β m : ℝ) (t : ℝ≥0)
    {A : ℝ → ℝ} (hA : Measurable A) (x : ℝ) :
    scalarTimeStep β m t A x = coleHopf m (β ^ 2 * (t : ℝ)).toNNReal A x := by
  rw [scalarTimeStep, scalarStep_eq_coleHopf m _ hA, mul_pow,
    Real.sq_sqrt t.coe_nonneg]

theorem scalarTimeChain_eq_parisiPotential (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (l : List (ℝ × ℝ≥0)) (s : ℝ) (hs : 0 ≤ s)
    (hend : s + (chainDuration l : ℝ) = 1)
    (hmodel : TimeChainModels (parisiCDF μ) s l) (x : ℝ) :
    scalarTimeChain β l scalarSpinTerminal x = parisiPotential β μ (s, x) + Real.log 2 := by
  induction l generalizing s x with
  | nil =>
    have hs1 : s = 1 := by simpa only [chainDuration_nil, NNReal.coe_zero, add_zero] using hend
    rw [hs1, scalarTimeChain, parisiPotential_terminal, scalarSpinTerminal_eq_log_cosh_add]
  | cons p l ih =>
    rcases p with ⟨m, t⟩
    have hend' : s + (t : ℝ) + (chainDuration l : ℝ) = 1 := by
      simpa only [chainDuration_cons, NNReal.coe_add, ← add_assoc] using hend
    have hs' : 0 ≤ s + (t : ℝ) := add_nonneg hs t.coe_nonneg
    have htail : scalarTimeChain β l scalarSpinTerminal =
        fun y => parisiPotential β μ (s + t, y) + Real.log 2 :=
      funext (fun y => ih (s + t) hs' hend' hmodel.2 y)
    rw [scalarTimeChain, htail]
    by_cases ht : t = 0
    · simp only [ht, scalarTimeStep_zero, NNReal.coe_zero, add_zero]
    · have hst : s < s + (t : ℝ) := lt_add_of_pos_right s (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht))
      have ht1 : s + (t : ℝ) ≤ 1 := by linarith [(chainDuration l).coe_nonneg]
      have hmeas : Measurable (fun y => parisiPotential β μ (s + t, y)) :=
        ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)).measurable
      rw [scalarTimeStep_eq_coleHopf β m t (hmeas.add_const _),
        coleHopf_add_const (FRSB.parisiPotential_hasLinearGrowth β μ (s + t) ⟨hs', ht1⟩)
          hmeas]
      congr 1
      have he := FRSB.parisiPotential_coleHopf_on_constantCDF β hβ μ hs hst ht1 hmodel.1 x
      simpa only [add_sub_cancel_left] using he.symm

private def clippedGrid (n : ℕ) (s : ℝ) (i : Fin (n + 2)) : ℝ :=
  max s ((i : ℝ) / (n + 1 : ℕ))

private theorem clippedGrid_monotone (n : ℕ) (s : ℝ) : Monotone (clippedGrid n s) := by
  intro i j hij
  apply max_le_max_left
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
  exact_mod_cast hij

private theorem clippedGrid_zero (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    clippedGrid n s 0 = s := by
  simp only [clippedGrid, Fin.val_zero, Nat.cast_zero, zero_div, max_eq_left hs]

private theorem clippedGrid_last (n : ℕ) (s : ℝ) (hs : s ≤ 1) :
    clippedGrid n s (Fin.last (n + 1)) = 1 := by
  simp only [clippedGrid, Fin.val_last]
  rw [div_self (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), max_eq_right hs]

private theorem clippedGrid_models (μ : ParisiMeasure) (n : ℕ) (s : ℝ)
    (i : Fin (n + 1)) (z : ℝ)
    (hz : z ∈ Ico (clippedGrid n s i.castSucc) (clippedGrid n s i.succ)) :
    parisiCDF (parisiGridMeasure μ n) z =
      parisiCDF (parisiGridMeasure μ n) ((i : ℝ) / (n + 1 : ℕ)) := by
  apply parisiCDF_grid_eq_node μ n i.val
  have hleft : (i : ℝ) / (n + 1 : ℕ) ≤ z :=
    (le_max_right s _).trans hz.1
  have hs : s ≤ z := (le_max_left _ _).trans hz.1
  have hright : z < ((i.val + 1 : ℕ) : ℝ) / (n + 1 : ℕ) := by
    have hh : z < max s (((i.val + 1 : ℕ) : ℝ) / (n + 1 : ℕ)) := hz.2
    exact (lt_max_iff.mp hh).resolve_left (not_lt.mpr hs)
  exact ⟨hleft, hright⟩

theorem scalarCDFValue_grid (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    scalarCDFValue β (parisiCDF (parisiGridMeasure μ n)) s (1 - s).toNNReal x =
      parisiPotential β (parisiGridMeasure μ n) (s, x) + Real.log 2 := by
  let q := clippedGrid n s
  let hq : Monotone q := clippedGrid_monotone n s
  let m : Fin (n + 1) → ℝ := fun i =>
    parisiCDF (parisiGridMeasure μ n) ((i : ℝ) / (n + 1 : ℕ))
  let l := partitionTimeChain (n + 1) q hq m
  have hq0 : q 0 = s := clippedGrid_zero n s hs.1
  have hq1 : q (Fin.last (n + 1)) = 1 := clippedGrid_last n s hs.2
  have hd : (chainDuration l : ℝ) = 1 - s := by
    rw [partitionTimeChain_duration, hq0, hq1]
  have hmodel : TimeChainModels (parisiCDF (parisiGridMeasure μ n)) s l := by
    rw [← hq0]
    exact partitionTimeChain_models (n + 1) q hq m (clippedGrid_models μ n s)
  have hm : ∀ p ∈ l, p.1 ∈ Icc (0 : ℝ) 1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨parisiCDF_nonneg _ _, parisiCDF_le_one _ _⟩
  have htime : (1 - s).toNNReal ≤ 1 := by
    apply Real.toNNReal_le_one.mpr
    exact sub_le_self 1 hs.1
  have hdur : chainDuration l = (1 - s).toNNReal := by
    apply NNReal.coe_injective
    rw [hd, Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
  have hchain := scalarCDFOperator_eq_chain scalarSpinTerminal_regular
    scalarSpinTerminal_lipschitz β
    (fun z => ⟨parisiCDF_nonneg _ z, parisiCDF_le_one _ z⟩)
    (parisiCDF_monotone _) l hm s _ htime hdur hmodel x
  exact hchain.trans (scalarTimeChain_eq_parisiPotential β hβ _ l s hs.1
    (by rw [hd]; ring) hmodel x)

private theorem cdfDistance_eq_parisiCDFDistance (μ ν : ParisiMeasure) :
    cdfDistance (parisiCDF μ) (parisiCDF ν) = parisiCDFDistance μ ν := by
  rw [cdfDistance, parisiCDFDistance,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Icc_eq_integral_Ioc]

private theorem scalarCDFValue_grid_tendsto (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    Tendsto (fun n => scalarCDFValue β (parisiCDF (parisiGridMeasure μ n))
      s (1 - s).toNNReal x) atTop
      (𝓝 (scalarCDFValue β (parisiCDF μ) s (1 - s).toNNReal x)) := by
  have hD : Tendsto (fun n => cdfDistance (parisiCDF (parisiGridMeasure μ n))
      (parisiCDF μ)) atTop (𝓝 0) := by
    simp_rw [cdfDistance_eq_parisiCDFDistance]
    exact FRSB.tendsto_parisiCDFDistance_of_tendsto (FRSB.tendsto_parisiGridMeasure μ)
  have ht : (1 - s).toNNReal ≤ 1 :=
    Real.toNNReal_le_one.mpr (sub_le_self 1 hs.1)
  have hend : s + ((1 - s).toNNReal : ℝ) ≤ 1 := by
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    linarith
  exact (scalarCDFValue_tendstoUniformly_interval β
    (fun z => ⟨parisiCDF_nonneg _ z, parisiCDF_le_one _ z⟩) (parisiCDF_monotone μ)
    (fun n z => ⟨parisiCDF_nonneg _ z, parisiCDF_le_one _ z⟩)
    (fun n => parisiCDF_monotone (parisiGridMeasure μ n)) hD s _ ht hs.1 hend).tendsto_at x

private theorem dyadicScalar_beta_zero (α : ℝ → ℝ) (n : ℕ)
    (s : ℝ) (t : ℝ≥0) (f : ℝ → ℝ) : dyadicScalar 0 α n s t f = f := by
  induction n generalizing s t f with
  | zero => simp only [dyadicScalar_zero, scalarTimeStep, zero_mul, scalarStep_zero]
  | succ n ih => rw [dyadicScalar_succ, ih, ih]

theorem scalarCDFValue_beta_zero (α : ℝ → ℝ) (s : ℝ) (t : ℝ≥0) (x : ℝ) :
    scalarCDFValue 0 α s t x = scalarSpinTerminal x := by
  simp only [scalarCDFValue, dyadicScalar_beta_zero]
  exact tendsto_const_nhds.limUnder_eq

theorem scalarCDFValue_eq_parisiPotential (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    scalarCDFValue β (cdf (realMeasure μ : Measure ℝ)) s (1 - s).toNNReal x =
      parisiPotential β μ (s, x) + Real.log 2 := by
  rw [cdf_realMeasure_eq]
  by_cases hβ : β = 0
  · subst β
    rw [scalarCDFValue_beta_zero, parisiPotential_zero,
      scalarSpinTerminal_eq_log_cosh_add]
  · have hU := scalarCDFValue_grid_tendsto β μ s hs x
    have hP := (FRSB.tendsto_parisiPotential_of_weak β μ (parisiGridMeasure μ)
      (FRSB.tendsto_parisiGridMeasure μ) s x hs).add_const (Real.log 2)
    exact tendsto_nhds_unique hU (hP.congr' (.of_forall fun n =>
      (scalarCDFValue_grid β hβ μ n s hs x).symm))

theorem scalarCDFParisi_eq_parisiPDEFunctional (β : ℝ) (μ : ParisiMeasure) :
    scalarCDFParisi β (cdf (realMeasure μ : Measure ℝ)) = parisiPDEFunctional β 0 μ := by
  apply scalarCDFParisi_eq_of_value
  simpa only [sub_zero, Real.toNNReal_one] using
    scalarCDFValue_eq_parisiPotential β μ 0 ⟨le_rfl, zero_le_one⟩ 0

theorem scalarCDFValue_eq_overlapMeasure (β : ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc 0 1) = 1)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    scalarCDFValue β (cdf (μ : Measure ℝ)) s (1 - s).toNNReal x =
      parisiPotential β (overlapMeasure μ hμ) (s, x) + Real.log 2 := by
  have he := scalarCDFValue_eq_parisiPotential β (overlapMeasure μ hμ) s hs x
  rw [realMeasure_overlapMeasure] at he
  exact he

theorem scalarCDFParisi_eq_overlapMeasure (β : ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc 0 1) = 1) :
    scalarCDFParisi β (cdf (μ : Measure ℝ)) =
      parisiPDEFunctional β 0 (overlapMeasure μ hμ) := by
  rw [← scalarCDFParisi_eq_parisiPDEFunctional, realMeasure_overlapMeasure]

theorem finiteParisiInf_eq_parisiPDEValue (β : ℝ) :
    finiteParisiInf β = parisiPDEValue β 0 := by
  apply le_antisymm
  · rw [← FRSB.parisiMinimizer_value β 0, ← scalarCDFParisi_eq_parisiPDEFunctional]
    exact finiteParisiInf_le_scalarCDFParisi β _
      (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
      (supported_probability_cdf_one _ (realMeasure_mass_one _))
  · obtain ⟨μ, hμ, hmin, _⟩ := exists_scalarCDFParisi_minimizer β
    calc
      parisiPDEValue β 0 = parisiPDEFunctional β 0 (FRSB.parisiMinimizer β 0) :=
        (FRSB.parisiMinimizer_value β 0).symm
      _ ≤ parisiPDEFunctional β 0 (overlapMeasure μ hμ) :=
        FRSB.parisiMinimizer_minimal β 0 _
      _ = scalarCDFParisi β (cdf (μ : Measure ℝ)) :=
        (scalarCDFParisi_eq_overlapMeasure β μ hμ).symm
      _ = finiteParisiInf β := hmin

theorem scalarCDFParisi_minimizer_iff (β : ℝ) (μ : ParisiMeasure) :
    scalarCDFParisi β (cdf (realMeasure μ : Measure ℝ)) = finiteParisiInf β ↔
      FRSB.IsParisiMinimizer β 0 μ := by
  rw [scalarCDFParisi_eq_parisiPDEFunctional, finiteParisiInf_eq_parisiPDEValue,
    FRSB.isParisiMinimizer_iff_infimum]

theorem scalarCDFParisi_minimizer_iff_overlapMeasure (β : ℝ)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc 0 1) = 1) :
    scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β ↔
      FRSB.IsParisiMinimizer β 0 (overlapMeasure μ hμ) := by
  rw [scalarCDFParisi_eq_overlapMeasure β μ hμ, finiteParisiInf_eq_parisiPDEValue,
    FRSB.isParisiMinimizer_iff_infimum]

theorem scalarCDFParisi_minimizer_eq_selected (β : ℝ) (hβ : β ≠ 0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc 0 1) = 1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β) :
    μ = realMeasure (FRSB.parisiMinimizer β 0) := by
  have hP : FRSB.IsParisiMinimizer β 0 (overlapMeasure μ hμ) :=
    (scalarCDFParisi_minimizer_iff_overlapMeasure β μ hμ).mp hmin
  have he := FRSB.parisiMinimizer_unique β hβ (overlapMeasure μ hμ) hP
  calc
    μ = realMeasure (overlapMeasure μ hμ) := (realMeasure_overlapMeasure μ hμ).symm
    _ = realMeasure (FRSB.parisiMinimizer β 0) := congrArg realMeasure he

theorem scalarCDFParisi_minimizer_unique (β : ℝ) (hβ : β ≠ 0)
    (μ ν : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc 0 1) = 1) (hν : (ν : Measure ℝ) (Icc 0 1) = 1)
    (hminμ : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β)
    (hminν : scalarCDFParisi β (cdf (ν : Measure ℝ)) = finiteParisiInf β) : μ = ν :=
  (scalarCDFParisi_minimizer_eq_selected β hβ μ hμ hminμ).trans
    (scalarCDFParisi_minimizer_eq_selected β hβ ν hν hminν).symm

theorem exists_unique_scalarCDFParisi_minimizer (β : ℝ) (hβ : β ≠ 0) :
    ∃! μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc 0 1) = 1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β := by
  let μ := realMeasure (FRSB.parisiMinimizer β 0)
  have hm : (μ : Measure ℝ) (Icc 0 1) = 1 := realMeasure_mass_one _
  have hmin : scalarCDFParisi β (cdf (μ : Measure ℝ)) = finiteParisiInf β :=
    (scalarCDFParisi_minimizer_iff β _).mpr (FRSB.isParisiMinimizer_selected β 0)
  refine ⟨μ, ⟨hm, hmin⟩, ?_⟩
  intro ν hν
  exact scalarCDFParisi_minimizer_unique β hβ ν μ hν.1 hm hν.2 hmin

theorem scalarCDFParisi_beta_zero (α : ℝ → ℝ) :
    scalarCDFParisi 0 α = Real.log 2 := by
  simp only [scalarCDFParisi, scalarCDFValue_beta_zero, scalarSpinTerminal,
    Real.cosh_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, zero_mul, sub_zero]

theorem finiteParisiInf_beta_zero : finiteParisiInf 0 = Real.log 2 := by
  obtain ⟨μ, _, hmin, _⟩ := exists_scalarCDFParisi_minimizer 0
  exact hmin.symm.trans (scalarCDFParisi_beta_zero (cdf (μ : Measure ℝ)))

end SKBarriers2.Bridge
