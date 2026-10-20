module

public import SKBarriers2.Bridge.ScalarValue
public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Hierarchy.TimeChainAverageAlgebra
public import OAI.Probability.SKBarriers.Gaussian.LipschitzChainRepresentation
public import OAI.Probability.SKBarriers.Parisi.CDFUniformAverage
public import FRSB.ConstantMassLaw
public import FRSB.OptimalDiffusion

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open OAI.SK.Analytic Paper
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory

namespace SKBarriers2.Bridge

theorem Phi_eq_parisiPotential (β : ℝ) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Phi β (cdf (realMeasure μ : Measure ℝ)) t =
      fun x => parisiPotential β μ (t, x) + Real.log 2 :=
  funext (scalarCDFValue_eq_parisiPotential β μ t ht)

theorem Phi_regular (β : ℝ) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    BoundedDerivs (Phi β (cdf (realMeasure μ : Measure ℝ)) t) := by
  unfold Phi
  rw [cdf_realMeasure_eq]
  exact scalarCDFValue_regular β
    (fun z => ⟨parisiCDF_nonneg μ z, parisiCDF_le_one μ z⟩)
    (parisiCDF_monotone μ) t _ (Real.toNNReal_le_one.mpr (sub_le_self 1 ht.1))

theorem Phi_lipschitz (β : ℝ) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    LipschitzWith 1 (Phi β (cdf (realMeasure μ : Measure ℝ)) t) := by
  unfold Phi
  rw [cdf_realMeasure_eq]
  exact scalarCDFValue_lipschitz β
    (fun z => ⟨parisiCDF_nonneg μ z, parisiCDF_le_one μ z⟩)
    (parisiCDF_monotone μ) t _ (Real.toNNReal_le_one.mpr (sub_le_self 1 ht.1))

theorem jet_succ_eq_parisiSpatialJet (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    jet β (cdf (realMeasure μ : Measure ℝ)) (j + 1) t x =
      FRSB.parisiSpatialJet β μ (j + 1) t x := by
  rw [jet, Phi_eq_parisiPotential β μ t ht,
    FRSB.parisiSpatialJet_eq_iteratedDeriv β μ (j + 1) t x ht]
  simpa only [add_comm] using
    (iteratedDeriv_const_add (f := fun y => parisiPotential β μ (t, y))
      (Nat.succ_pos j) (Real.log 2) :
      iteratedDeriv (j + 1) (fun y => Real.log 2 + parisiPotential β μ (t, y)) x = _)

theorem scalarStepAverage_eq_constantMassKernel (m v : ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hfg : HasLinearGrowth f)
    (hg : Measurable g) (x : ℝ) :
    scalarStepAverage m v f g x =
      ∫ y, g y ∂FRSB.constantMassKernel m (v ^ 2).toNNReal f x := by
  have hfm : Measurable f := hf.1.continuous.measurable
  have hfl : BoundedDerivs (fun z : ℝ × ℝ => f (z.1 + v * z.2)) :=
    hf.compCLM (scalarStepLinear v)
  have hv : NNReal.mk (v ^ 2) (sq_nonneg v) = (v ^ 2).toNNReal := by
    apply NNReal.coe_injective
    exact (Real.coe_toNNReal _ (sq_nonneg v)).symm
  rw [FRSB.integral_constantMassKernel m _ f hf.1.continuous hfg x g]
  have hshift : (∫ y, g y * FRSB.constantMassWeight m (v ^ 2).toNNReal f x y
      ∂gaussianReal x (v ^ 2).toNNReal) =
      ∫ y, g (x + y) * FRSB.constantMassWeight m (v ^ 2).toNNReal f x (x + y)
        ∂gaussianReal 0 (v ^ 2).toNNReal := by
    exact integral_gaussianReal_eq_integral_comp_add x _
      (hg.mul (by unfold FRSB.constantMassWeight; fun_prop)).aestronglyMeasurable
  rw [hshift]
  have hw : Measurable (fun y => g (x + y) *
      FRSB.constantMassWeight m (v ^ 2).toNNReal f x (x + y)) :=
    (hg.comp (measurable_const_add x)).mul
      (by unfold FRSB.constantMassWeight; fun_prop)
  have hmul := integral_gaussian_mul v hw.stronglyMeasurable
  rw [hv] at hmul
  rw [← hmul]
  rw [scalarStepAverage, gaussianAverage, gaussianStepLaw_integral hfl]
  apply integral_congr_ae
  exact .of_forall fun y => by
    change Real.exp (m * (f (x + v * y) - scalarStep m v f x)) * g (x + v * y) = _
    rw [scalarStep_eq_coleHopf m v hf.1.continuous.measurable]
    unfold FRSB.constantMassWeight
    ring

private theorem constantMassKernel_add_const (m : ℝ) (v : ℝ≥0)
    (A : ℝ → ℝ) (hAc : Continuous A) (hAg : HasLinearGrowth A) (c : ℝ) :
    FRSB.constantMassKernel m v (fun y => A y + c) =
      FRSB.constantMassKernel m v A := by
  ext x : 1
  rw [FRSB.constantMassKernel_apply m v _ (hAc.add_const c) (hAg.add_const c),
    FRSB.constantMassKernel_apply m v A hAc hAg]
  unfold FRSB.constantMassTransition
  congr 1
  funext y
  unfold FRSB.constantMassWeight
  rw [coleHopf_add_const hAg hAc.measurable]
  rw [add_sub_add_right_eq_sub]

theorem scalarStepAverage_Phi_eq_kernel (β : ℝ) (μ : ParisiMeasure)
    (a d : ℝ≥0) (had : (a : ℝ) + d ≤ 1) (m : ℝ)
    {g : ℝ → ℝ} (hg : Measurable g) (x : ℝ) :
    scalarStepAverage m (β * Real.sqrt (d : ℝ))
      (Phi β (cdf (realMeasure μ : Measure ℝ)) ((a : ℝ) + d)) g x =
      ∫ y, g y ∂FRSB.parisiConstantMassKernel β μ a d m x := by
  have ht : (a : ℝ) + d ∈ Icc (0 : ℝ) 1 := ⟨by positivity, had⟩
  have hAc : Continuous (fun y => parisiPotential β μ ((a : ℝ) + d, y)) :=
    (continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)
  have hAg : HasLinearGrowth (fun y => parisiPotential β μ ((a : ℝ) + d, y)) :=
    FRSB.parisiPotential_hasLinearGrowth β μ _ ht
  rw [scalarStepAverage_eq_constantMassKernel m _ (Phi_regular β μ _ ht)
    (by rw [Phi_eq_parisiPotential β μ _ ht]; exact hAg.add_const _) hg,
    mul_pow, Real.sq_sqrt d.coe_nonneg, Phi_eq_parisiPotential β μ _ ht,
    constantMassKernel_add_const m _ _ hAc hAg]
  rfl

private theorem scalarTimeStep_Phi (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : 0 ≤ s) (d : ℝ≥0) (hsd : s + d ≤ 1) (m : ℝ)
    (hc : ∀ z ∈ Ico s (s + d), parisiCDF μ z = m) :
    scalarTimeStep β m d (Phi β (cdf (realMeasure μ : Measure ℝ)) (s + d)) =
      Phi β (cdf (realMeasure μ : Measure ℝ)) s := by
  have hs1 : s ≤ 1 := (le_add_of_nonneg_right d.coe_nonneg).trans hsd
  by_cases hd : d = 0
  · simp only [hd, NNReal.coe_zero, add_zero, scalarTimeStep_zero]
  · have hAc : Measurable (fun y => parisiPotential β μ (s + d, y)) :=
      ((continuous_parisiPotential β μ).comp
        (continuous_const.prodMk continuous_id)).measurable
    rw [Phi_eq_parisiPotential β μ s ⟨hs, hs1⟩,
      Phi_eq_parisiPotential β μ (s + d) ⟨add_nonneg hs d.coe_nonneg, hsd⟩]
    funext x
    rw [scalarTimeStep_eq_coleHopf β m d (hAc.add_const _),
      coleHopf_add_const (FRSB.parisiPotential_hasLinearGrowth β μ _
        ⟨add_nonneg hs d.coe_nonneg, hsd⟩) hAc]
    congr 1
    have he := FRSB.parisiPotential_coleHopf_on_constantCDF β hβ μ hs
      (lt_add_of_pos_right s (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hd))) hsd hc x
    simpa only [add_sub_cancel_left] using he.symm

theorem scalarTimeChain_Phi (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (l : List (ℝ × ℝ≥0)) (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ 1)
    (hend : s + (chainDuration l : ℝ) = t)
    (hmodel : TimeChainModels (parisiCDF μ) s l) :
    scalarTimeChain β l (Phi β (cdf (realMeasure μ : Measure ℝ)) t) =
      Phi β (cdf (realMeasure μ : Measure ℝ)) s := by
  induction l generalizing s with
  | nil =>
    have he : s = t := by simpa only [chainDuration_nil, NNReal.coe_zero, add_zero] using hend
    simp only [scalarTimeChain, he]
  | cons p l ih =>
    rcases p with ⟨m, d⟩
    have hend' : s + (d : ℝ) + (chainDuration l : ℝ) = t := by
      simpa only [chainDuration_cons, NNReal.coe_add, ← add_assoc] using hend
    have hsd : s + (d : ℝ) ≤ 1 := by linarith [(chainDuration l).coe_nonneg]
    rw [scalarTimeChain, ih (s + d) (add_nonneg hs d.coe_nonneg) hend' hmodel.2]
    exact scalarTimeStep_Phi β hβ μ s hs d hsd m hmodel.1

private theorem scalarTimeChainAverage_cons (β m : ℝ) (d : ℝ≥0)
    (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β ((m, d) :: l) f g =
      scalarStepAverage m (β * Real.sqrt (d : ℝ)) (scalarTimeChain β l f)
        (scalarTimeChainAverage β l f g) := by
  change scalarTimeChainAverage β ([(m, d)] ++ l) f g = _
  rw [scalarTimeChainAverage_append]
  rfl

theorem integral_scalarTimeChainAverage_eq (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (l : List (ℝ × ℝ≥0)) (a t : ℝ≥0)
    (ht : (t : ℝ) ≤ 1) (hend : a + chainDuration l = t)
    (hmodel : TimeChainModels (parisiCDF μ) a l)
    {g : ℝ → ℝ} (hg : BoundedScalar g) :
    (∫ ω, scalarTimeChainAverage β l
      (Phi β (cdf (realMeasure μ : Measure ℝ)) t) g
      (selectedParisiItoState β 0 hβ μ a ω) ∂canonicalBrownianMeasure) =
      ∫ ω, g (selectedParisiItoState β 0 hβ μ t ω) ∂canonicalBrownianMeasure := by
  induction l generalizing a with
  | nil =>
    have he : a = t := by simpa only [chainDuration_nil, add_zero] using hend
    subst a
    rfl
  | cons p l ih =>
    rcases p with ⟨m, d⟩
    have hend' : a + d + chainDuration l = t := by
      simpa only [chainDuration_cons, ← add_assoc] using hend
    have had : (a : ℝ) + d ≤ 1 := by
      have he := congrArg (fun z : ℝ≥0 => (z : ℝ)) hend'
      simp only [NNReal.coe_add] at he
      linarith [(chainDuration l).coe_nonneg]
    have hmodel' : TimeChainModels (parisiCDF μ) (a + d : ℝ≥0) l :=
      hmodel.2
    have htail : scalarTimeChain β l
        (Phi β (cdf (realMeasure μ : Measure ℝ)) t) =
        Phi β (cdf (realMeasure μ : Measure ℝ)) (a + d : ℝ≥0) :=
      scalarTimeChain_Phi β hβ μ l (a + d : ℝ≥0) t (a + d).coe_nonneg ht
        (by exact_mod_cast hend') hmodel'
    let G := scalarTimeChainAverage β l
      (Phi β (cdf (realMeasure μ : Measure ℝ)) t) g
    have hG : BoundedScalar G := scalarHierarchyAverage_bounded
      (Phi_regular β μ t ⟨t.coe_nonneg, ht⟩) hg _ _ _
    rw [scalarTimeChainAverage_cons, htail]
    change (∫ ω, scalarStepAverage m (β * Real.sqrt (d : ℝ))
      (Phi β (cdf (realMeasure μ : Measure ℝ)) (a + d : ℝ≥0)) G
      (selectedParisiItoState β 0 hβ μ a ω) ∂canonicalBrownianMeasure) = _
    by_cases hd : d = 0
    · subst d
      simp only [NNReal.coe_zero, Real.sqrt_zero, mul_zero,
        scalarStepAverage_zero_coefficient, add_zero] at *
      exact ih a hend' hmodel'
    · obtain ⟨C, _hC, hCb⟩ := hG.bounded
      have hw := FRSB.selectedParisiState_constantMass_weighted_borel β 0 hβ μ a d
        (pos_iff_ne_zero.mpr hd) had m hmodel.1 G hG.continuous.measurable C
        (fun y => hCb y) (fun _ => 1) stronglyMeasurable_const 1 (fun _ => by norm_num)
      simp only [one_mul] at hw
      calc
        _ = ∫ ω, (∫ y, G y ∂FRSB.parisiConstantMassKernel β μ a d m
              (selectedParisiItoState β 0 hβ μ a ω)) ∂canonicalBrownianMeasure := by
          apply integral_congr_ae
          exact .of_forall fun ω => scalarStepAverage_Phi_eq_kernel β μ a d had m
            hG.continuous.measurable _
        _ = ∫ ω, G (selectedParisiItoState β 0 hβ μ (a + d) ω)
              ∂canonicalBrownianMeasure := hw.symm
        _ = _ := ih (a + d) hend' hmodel'

end SKBarriers2.Bridge
