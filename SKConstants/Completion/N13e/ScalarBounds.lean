module

public import SKConstants.Completion.LGram.PopulationNorms
public import SKConstants.Completion.LM4b.CoarseNoiseBudget
public import SKConstants.Completion.Blueprint.NodesLower
public import SKConstants.Completion.LQ.ActualGrowingQuadrature
public import SKConstants.Completion.LBase.FullProfiles

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal RealInnerProductSpace

namespace SKConstants.Completion.N13e
open SKConstantsOAI.ZeroTemperatureSK LGram LM4b LQ
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualCoarseEnergy_eq_population_pairing
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) :
    actualCoarseEnergy W β t k = inner (𝕜 := ℝ)
      (populationTargetSpin W Z β hβ t (fun l => t (l+1)) k (t (k+1)))
      (populationQuerySpin W Z β hβ t (fun l => t (l+1)) k (t (k+1))) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  simp_rw [populationTargetSpin_eq_scale W Z β hβ t ht (fun l => t (l+1)) k
    (t (k+1)) (ht.monotone (Nat.le_succ k)),
    populationQuerySpin_eq_integral W Z β hβ t (fun l => t (l+1))
      (fun _ _ h => ht.monotone (by omega)) k (t (k+1)) le_rfl]
  rw [Finset.sum_fin_eq_sum_range]
  unfold actualCoarseEnergy actualCoarseSpinMean actualQueryCellMean actualCoarseScale
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range.mp hi, dite_true]

theorem actualCoarseEnergy_abs_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) :
    |actualCoarseEnergy W β t k| ≤ 1 := by
  rw [actualCoarseEnergy_eq_population_pairing W W β hβ t ht k]
  calc
    _ ≤ ‖populationTargetSpin W W β hβ t (fun l => t (l+1)) k (t (k+1))‖ *
        ‖populationQuerySpin W W β hβ t (fun l => t (l+1)) k (t (k+1))‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ 1 * 1 := mul_le_mul
      (populationTargetSpin_norm_le_one W W β hβ t ht _ k _)
      (populationQuerySpin_norm_le_one W W β hβ t _
        (ht.comp (fun _ _ h => Nat.add_lt_add_right h 1)) k _)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem profile_product_lower {h P pv R av rv : ℝ}
    (_hh : 0 ≤ h) (hsmall : h ≤ 1/8) (hP : 0 ≤ P)
    (hpv : (1-h)*P ≤ pv) (hpv0 : 0 ≤ pv)
    (_hav : 0 ≤ av) (hR : av ≤ R)
    (hrv : 0 ≤ rv) (hrva : rv ≤ av) (hdrop : R-rv ≤ 4*h*R) :
    (1-5*h)*P*Real.sqrt av ≤ pv*Real.sqrt rv := by
  have hfactor : 0 ≤ 1-4*h := by linarith
  have hrvlo : (1-4*h)*av ≤ rv := by
    have hm := mul_le_mul_of_nonneg_left hR hfactor
    nlinarith only [hm, hdrop]
  have hs := sqrt_drop_le (R := av) (x := rv) (L := 4*h)
    hrv hrva (by nlinarith only [hrvlo])
  have hm := mul_le_mul hpv (show (1-4*h)*Real.sqrt av ≤ Real.sqrt rv by nlinarith)
    (by positivity : 0 ≤ (1-4*h)*Real.sqrt av) hpv0
  have he : (1-5*h)*P*Real.sqrt av ≤ ((1-h)*P)*((1-4*h)*Real.sqrt av) := by
    have hnon := mul_nonneg (sq_nonneg h) (mul_nonneg hP (Real.sqrt_nonneg av))
    nlinarith only [hnon]
  exact he.trans hm

theorem actualCoarseWeight_close
    (hprofile : Blueprint.SusceptibilityProfileStatement)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (W : BrownianSystem Ω₀) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ)
    (hsmall : (growingQueryDuration δ (j+1) : ℝ) ≤ 1/8) :
    |actualCoarseWeight W β (growingQueryTime δ) j -
      β * actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (j+1))| ≤
      10 * β * (growingQueryDuration δ (j+1) : ℝ) *
        actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (j+1)) := by
  let p := actualParisiFullSusceptibilityExpected W β
  let r := actualParisiFullSusceptibilitySquareExpected W β
  let a : ℝ := growingQueryTime δ j
  let b : ℝ := growingQueryTime δ (j+1)
  let c : ℝ := growingQueryTime δ (j+2)
  let d : ℝ := growingQueryDuration δ j
  let h : ℝ := growingQueryDuration δ (j+1)
  let av := (∫ u in a..b, r u) / d
  let P := p b
  let I := ∫ v in b..c, p v * Real.sqrt (r v)
  have hd : 0 < d := meshDuration_pos δ hδ j
  have hh : 0 < h := meshDuration_pos δ hδ (j+1)
  have hdh : d ≤ h := meshDuration_mono δ (Nat.le_succ j)
  have hab : b-a=d := growingQueryTime_sub δ j
  have hbc : c-b=h := growingQueryTime_sub δ (j+1)
  have hab' : a < b := by linarith
  have hbc' : b < c := by linarith
  have ha0 : 0 ≤ a := (growingQueryTime δ j).coe_nonneg
  have hb0 : 0 ≤ b := ha0.trans hab'.le
  have hc0 : 0 ≤ c := hb0.trans hbc'.le
  have hp0 : 0 ≤ P := actualParisiFullSusceptibilityExpected_nonneg W β b
  have hr0 (v : ℝ) : 0 ≤ r v := (actualParisiFullSusceptibilitySquareExpected_bounds W β v).1
  have hrmono := actual_square_profile_antitone W β hβ
  have havg := previous_average_bounds r hab'
    ((continuous_actualParisiFullSusceptibilitySquareExpected W β).intervalIntegrable a b)
    (fun u hu => ⟨hrmono (ha0.trans hu.1) hb0 hu.2, hrmono ha0 (ha0.trans hu.1) hu.1⟩)
  have hav : r b ≤ av ∧ av ≤ r a := by simpa only [hab] using havg
  have havpos : 0 < av := (LBase.actual_square_profile_pos W β hβ b hb0).trans_le hav.1
  have hav0 : 0 ≤ av := havpos.le
  have hsav : 0 < Real.sqrt av := Real.sqrt_pos.mpr havpos
  have hI : IntervalIntegrable (fun v => p v * Real.sqrt (r v)) volume b c :=
    ((continuous_actualParisiFullSusceptibilityExpected W β).mul
      (continuous_actualParisiFullSusceptibilitySquareExpected W β).sqrt).intervalIntegrable b c
  have hprod (v : ℝ) (hv : v ∈ Icc b c) :
      (1-5*h)*P*Real.sqrt av ≤ p v*Real.sqrt (r v) ∧
        p v*Real.sqrt (r v) ≤ P*Real.sqrt av := by
    have hv0 := hb0.trans hv.1
    have hpp := hprofile W β hβ b v hb0 hv.1
    have hplo : (1-h)*P ≤ p v := by
      have hm := mul_le_mul_of_nonneg_left hpp.2 (Real.exp_pos (-(v-b))).le
      have hex : Real.exp (-(v-b)) * Real.exp (v-b) = 1 := by
        rw [← Real.exp_add]; simp
      rw [← mul_assoc, hex, one_mul] at hm
      have hexlo : 1-h ≤ Real.exp (-(v-b)) := by
        have he := Real.add_one_le_exp (-(v-b))
        linarith [hv.2]
      exact (mul_le_mul_of_nonneg_right hexlo hp0).trans hm
    have hrvA : r v ≤ av := (hrmono hb0 hv0 hv.1).trans hav.1
    have hdr : r a-r v ≤ 4*h*r a := by
      have hdrop := actual_square_profile_drop W β hβ a v ha0 (hab'.le.trans hv.1)
      have hspan : v-a ≤ 2*h := by linarith [hv.2]
      have hm := mul_le_mul_of_nonneg_left hspan (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hr0 a))
      nlinarith only [hdrop, hm]
    refine ⟨profile_product_lower hh.le hsmall hp0 hplo
      (actualParisiFullSusceptibilityExpected_nonneg W β v) hav0 hav.2 (hr0 v) hrvA hdr, ?_⟩
    exact mul_le_mul hpp.1 (Real.sqrt_le_sqrt hrvA) (Real.sqrt_nonneg _) hp0
  have hIlow := intervalIntegral.integral_mono_on hbc'.le intervalIntegrable_const hI
    (fun v hv => (hprod v hv).1)
  have hIhigh := intervalIntegral.integral_mono_on hbc'.le hI intervalIntegrable_const
    (fun v hv => (hprod v hv).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul, hbc] at hIlow hIhigh
  have hratio : 1 ≤ Real.sqrt h / Real.sqrt d ∧ Real.sqrt h / Real.sqrt d ≤ 1+h := by
    have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
    refine ⟨(le_div_iff₀ hroot).mpr (by simpa using Real.sqrt_le_sqrt hdh), ?_⟩
    have he : Real.sqrt h / Real.sqrt d = Real.exp (d/8) := by
      have hgeom : h = d * Real.exp (d/4) := meshDuration_succ δ j
      rw [hgeom, Real.sqrt_mul hd.le, ← Real.exp_half]
      have harg : d / 4 / 2 = d/8 := by ring
      rw [harg]
      field_simp
    rw [he]
    have hden : 0 < 1-d/8 := by linarith
    refine (Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans ?_
    apply (div_le_iff₀ hden).mpr
    have hh2 : h*h ≤ h/8 := by nlinarith
    have hdh2 := mul_le_mul_of_nonneg_left hdh hh.le
    nlinarith
  let J := (I/h) / Real.sqrt av
  have hJ : (1-5*h)*P ≤ J ∧ J ≤ P := by
    constructor
    · apply (le_div_iff₀ hsav).mpr
      apply (le_div_iff₀ hh).mpr
      change _ ≤ I
      nlinarith only [hIlow]
    · apply (div_le_iff₀ hsav).mpr
      apply (div_le_iff₀ hh).mpr
      change I ≤ _
      nlinarith only [hIhigh]
  have hJ0 : 0 ≤ J := le_trans (mul_nonneg (by linarith : 0 ≤ 1-5*h) hp0) hJ.1
  have hs : (actualCoarseScale W β (growingQueryTime δ) j : ℝ) =
      Real.sqrt d * Real.sqrt av := by
    rw [actualCoarseScale, actualParisiPosteriorIntervalScale_eq_sqrt_integral W β hβ _ _
      (growingQueryTime_strictMono δ hδ (Nat.lt_succ_self j))]
    have he : (∫ u in a..b, r u) = d*av := by dsimp only [av]; field_simp
    change Real.sqrt (∫ u in a..b, r u) = _
    rw [he, Real.sqrt_mul hd.le]
  have hmean : actualQueryCellMean W β (growingQueryTime δ (j+1))
      (growingQueryTime δ (j+2)) = β*I := by
    rw [actualQueryCellMean, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    dsimp only
    rw [uIcc_of_le hbc'.le] at hv
    rw [actual_rho_eq W β hβ v (hb0.trans hv.1)]
    ring
  have hw : actualCoarseWeight W β (growingQueryTime δ) j =
      β * (Real.sqrt h / Real.sqrt d) * J := by
    rw [actualCoarseWeight, actualCoarseSpinMean, hmean, hs]
    change (β*I / Real.sqrt (c-b)) / (Real.sqrt d * Real.sqrt av) = _
    rw [hbc]
    dsimp only [J]
    have hsd := (Real.sqrt_pos.mpr hd).ne'
    have hsh := (Real.sqrt_pos.mpr hh).ne'
    have hsa := hsav.ne'
    field_simp
    rw [Real.sq_sqrt hh.le]
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hwlo : β*((1-5*h)*P) ≤ actualCoarseWeight W β (growingQueryTime δ) j := by
    rw [hw]
    have hm := mul_le_mul_of_nonneg_right hratio.1 hJ0
    have hl : (1-5*h)*P ≤ (Real.sqrt h/Real.sqrt d)*J := by nlinarith only [hJ.1, hm]
    nlinarith only [mul_le_mul_of_nonneg_left hl hβ0.le]
  have hwhi : actualCoarseWeight W β (growingQueryTime δ) j ≤ β*((1+h)*P) := by
    rw [hw]
    have hm := mul_le_mul hratio.2 hJ.2 hJ0 (by linarith : 0 ≤ 1+h)
    nlinarith only [mul_le_mul_of_nonneg_left hm hβ0.le]
  change |actualCoarseWeight W β (growingQueryTime δ) j-β*P| ≤ 10*β*h*P
  apply abs_le.mpr
  have hnon : 0 ≤ β*h*P := by positivity
  constructor <;> nlinarith only [hwlo, hwhi, hnon]

theorem actualCoarseWeight_error_sum
    (hprofile : Blueprint.SusceptibilityProfileStatement)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (W : BrownianSystem Ω₀) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ)
    (hsmall : ∀ j < k, (growingQueryDuration δ (j+1) : ℝ) ≤ 1/8) :
    (∑ j ∈ Finset.range k, |actualCoarseWeight W β (growingQueryTime δ) j -
      β*actualParisiFullSusceptibilityExpected W β (growingQueryTime δ (j+1))|) ≤
      10*β*(growingQueryTime δ (k+1):ℝ) := by
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  have hsum : (∑ j ∈ Finset.range k, (growingQueryDuration δ (j+1):ℝ)) =
      (growingQueryTime δ (k+1):ℝ) - (growingQueryTime δ 1:ℝ) := by
    have he (j : ℕ) : (growingQueryDuration δ (j+1):ℝ) =
        (growingQueryTime δ ((j+1)+1):ℝ) - (growingQueryTime δ (j+1):ℝ) :=
      (growingQueryTime_sub δ (j+1)).symm
    simp_rw [he]
    exact Finset.sum_range_sub (fun j => (growingQueryTime δ (j+1):ℝ)) k
  calc
    _ ≤ ∑ j ∈ Finset.range k, 10*β*(growingQueryDuration δ (j+1):ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (actualCoarseWeight_close hprofile W β hβ δ hδ j
        (hsmall j (Finset.mem_range.mp hj))).trans
        (mul_le_of_le_one_right (by positivity)
          (LBase.actual_susceptibility_le_one W β _))
    _ = 10*β*((growingQueryTime δ (k+1):ℝ) - (growingQueryTime δ 1:ℝ)) := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sub_le_self _ (growingQueryTime δ 1).coe_nonneg) (by positivity)

theorem actualCoarsePsi_deterministic_inputs
    (hprofile : Blueprint.SusceptibilityProfileStatement)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (W : BrownianSystem Ω₀) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ)
    (hsmall : ∀ j < k, (growingQueryDuration δ (j+1):ℝ) ≤ 1/8) :
    let t := growingQueryTime δ
    let v := fun j => β*actualParisiFullSusceptibilityExpected W β (t (j+1))
    |actualCoarseEnergy W β t k| ≤ 1 ∧ Antitone v ∧ (∀ j, 0 ≤ v j) ∧ v 0 ≤ β ∧
      (∑ j ∈ Finset.range k, |actualCoarseWeight W β t j-v j|) ≤ 10*β*(t (k+1):ℝ) ∧
      (∑ j ∈ Finset.range k, (actualCoarseNoiseWeight W β t j)^2 *
        (brownianMeshVariance (fun j => t (j+1)) j:ℝ)) ≤ 1 := by
  have ht := growingQueryTime_strictMono δ hδ
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ).le
  refine ⟨actualCoarseEnergy_abs_le_one W β hβ _ ht k, ?_, ?_, ?_,
    actualCoarseWeight_error_sum hprofile W β hβ δ hδ k hsmall,
    actualCoarseNoiseWeight_budget W β hβ _ ht k⟩
  · intro i j hij
    exact mul_le_mul_of_nonneg_left
      (hprofile W β hβ _ _ (growingQueryTime δ (i+1)).coe_nonneg
        (NNReal.coe_le_coe.mpr (ht.monotone (Nat.add_le_add_right hij 1)))).1 hβ0
  · intro j
    exact mul_nonneg hβ0 (actualParisiFullSusceptibilityExpected_nonneg W β _)
  · exact mul_le_of_le_one_right hβ0 (LBase.actual_susceptibility_le_one W β _)

end SKConstants.Completion.N13e
