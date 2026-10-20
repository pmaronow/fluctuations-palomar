module

public import SKBarriers2.Corner.GapAssembly

@[expose] public section

noncomputable section
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Set
open OAI.SK.Analytic

namespace SKBarriers2
namespace PrefixMoments

private theorem dyadicIntervals_div_three (α : ℝ → ℝ) (n : ℕ)
    (s : ℝ) (t : ℝ≥0) :
    dyadicIntervals (fun u => α u / 3) n s t =
      (dyadicIntervals α n s t).map (fun p => (p.1 / 3, p.2)) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih => simp only [dyadicIntervals, ih, List.map_append]

private theorem dyadicAverage_div_three (β : ℝ) (α : ℝ → ℝ) (n : ℕ)
    (s : ℝ) (t : ℝ≥0) (f g : ℝ → ℝ) (x : ℝ) :
    dyadicScalarAverage β (fun u => α u / 3) n s t (fun z => 3 * f z) g x =
      dyadicScalarAverage β α n s t f g x := by
  unfold dyadicScalarAverage
  rw [dyadicIntervals_div_three]
  simp only [List.get_eq_getElem, List.getElem_map]
  rw [← vectorHierarchyAverage_real,
    vectorHierarchyAverage_div_scale _ _ _ 3 (by norm_num), vectorHierarchyAverage_real]
  exact congrFun (scalarHierarchyAverage_cast
    (show ((dyadicIntervals α n s t).map (fun p => (p.1 / 3, p.2))).length =
      (dyadicIntervals α n s t).length from List.length_map _)
    (fun i => ((dyadicIntervals α n s t).get i).1)
    (fun i => β * Real.sqrt (((dyadicIntervals α n s t).get i).2 : ℝ)) f g) x

theorem scalarCDFAverage_div_three (β : ℝ) (α : ℝ → ℝ)
    (s : ℝ) (t : ℝ≥0) (f g : ℝ → ℝ) (x : ℝ) :
    scalarCDFAverage β (fun u => α u / 3) s t (fun z => 3 * f z) g x =
      scalarCDFAverage β α s t f g x := by
  unfold scalarCDFAverage
  simp only [dyadicAverage_div_three]

private theorem gridProfile_tendsto {α : ℝ → ℝ} {a len x : ℝ}
    (hlen : 0 < len) (hax : a ≤ x) (hx : ContinuousAt α x) :
    Tendsto (fun N : ℕ => OW.relativeGridProfile α a len (N + 1) x) atTop (𝓝 (α x)) := by
  let p := fun N : ℕ => a + len *
    (⌊(x - a) * ((N + 1 : ℕ) : ℝ) / len⌋₊ : ℝ) / ((N + 1 : ℕ) : ℝ)
  have herr (N : ℕ) : 0 ≤ x - p N ∧ x - p N ≤ len / ((N + 1 : ℕ) : ℝ) := by
    have hN : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    let u : ℝ := (x - a) * ((N + 1 : ℕ) : ℝ) / len
    have hu : 0 ≤ u := div_nonneg (mul_nonneg (sub_nonneg.mpr hax) hN.le) hlen.le
    have hlo := mul_le_mul_of_nonneg_right (Nat.floor_le hu) hlen.le
    have hhi := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one u) hlen
    have he : u * len = (x - a) * ((N + 1 : ℕ) : ℝ) := div_mul_cancel₀ _ hlen.ne'
    rw [he] at hlo hhi
    have hp : (p N - a) * ((N + 1 : ℕ) : ℝ) = len * (⌊u⌋₊ : ℝ) := by
      dsimp only [p, u]
      field_simp
      ring
    have hdiv : (len / ((N + 1 : ℕ) : ℝ)) * ((N + 1 : ℕ) : ℝ) = len :=
      div_mul_cancel₀ _ hN.ne'
    constructor
    · nlinarith only [hlo, hp, hN]
    · nlinarith only [hhi, hp, hdiv, hN]
  have hz : Tendsto (fun N : ℕ => len / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have he := squeeze_zero (fun N => (herr N).1) (fun N => (herr N).2) hz
  have hp : Tendsto p atTop (𝓝 x) := by
    simpa only [sub_zero, sub_sub_cancel] using (tendsto_const_nhds (x := x)).sub he
  exact hx.tendsto.comp hp

private theorem windowProfile_tendsto {α : ℝ → ℝ} {s h x : ℝ}
    (hh : 0 < h) (hx : ContinuousAt α x) :
    Tendsto (fun N : ℕ => OW.relativeWindowProfile α (1 / 2) s h (N + 1) x)
      atTop (𝓝 (α x)) := by
  by_cases h₀ : x < s
  · simpa only [OW.relativeWindowProfile, ite_eq_left h₀] using
      (tendsto_const_nhds : Tendsto (fun _N : ℕ => α x) atTop (𝓝 (α x)))
  by_cases h₁ : x < s + h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_left h₁] using
      gridProfile_tendsto hh (le_of_not_gt h₀) hx
  by_cases h₂ : x < s + (1 + 1 / 2) * h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁, ite_eq_left h₂] using
      gridProfile_tendsto (by positivity : 0 < (1 / 2 : ℝ) * h) (le_of_not_gt h₁) hx
  by_cases h₃ : x < s + 2 * h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁,
      ite_eq_right h₂, ite_eq_left h₃] using
      gridProfile_tendsto (by positivity : 0 < (1 - 1 / 2 : ℝ) * h)
        (le_of_not_gt h₂) hx
  by_cases h₄ : x < s + 4 * h
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁,
      ite_eq_right h₂, ite_eq_right h₃, ite_eq_left h₄] using
      gridProfile_tendsto (by positivity : 0 < 2 * h) (le_of_not_gt h₃) hx
  · simpa only [OW.relativeWindowProfile, ite_eq_right h₀, ite_eq_right h₁,
      ite_eq_right h₂, ite_eq_right h₃, ite_eq_right h₄] using
      (tendsto_const_nhds : Tendsto (fun _N : ℕ => α x) atTop (𝓝 (α x)))

theorem joinedProfile_cdfDistance_tendsto {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s h : ℝ) (hh : 0 < h) :
    Tendsto (fun N : ℕ => cdfDistance
      (OW.joinedWindowProfile α α (1 / 2) s h (N + 1)) α) atTop (𝓝 0) := by
  let A := fun N : ℕ => OW.joinedWindowProfile α α (1 / 2) s h (N + 1)
  have hbA (N : ℕ) (x : ℝ) : A N x ∈ Icc (0 : ℝ) 1 :=
    OW.joinedWindowProfile_bounds α α hα hα _ _ _ _ x
  have hmA (N : ℕ) : Monotone (A N) :=
    OW.joinedWindowProfile_monotone α α hm hm _ _ _ (Nat.succ_pos N) hh
      ⟨by norm_num, by norm_num⟩ le_rfl
  have hc : ∀ᵐ x : ℝ, ContinuousAt α x := by
    filter_upwards [hm.countable_not_continuousAt.ae_notMem volume] with x hx
    exact not_not.mp hx
  have hpoint : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      Tendsto (fun N => |A N x - α x|) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae hc] with x hx
    have hval : Tendsto (fun N => A N x) atTop (𝓝 (α x)) := by
      by_cases hxs : x < s
      · simpa only [A, OW.joinedWindowProfile, ite_eq_left hxs] using
          (tendsto_const_nhds : Tendsto (fun _N : ℕ => α x) atTop (𝓝 (α x)))
      · simpa only [A, OW.joinedWindowProfile, ite_eq_right hxs] using
          windowProfile_tendsto (s := s) hh hx
    simpa only [sub_self, abs_zero] using (hval.sub_const (α x)).abs
  have H := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Icc (0 : ℝ) 1))
    (F := fun N x => |A N x - α x|) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun N => ((hmA N).measurable.sub hm.measurable).abs.aestronglyMeasurable)
    (integrable_const 1) (fun N => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_abs]
      apply abs_le.mpr
      constructor <;> linarith [(hbA N x).1, (hbA N x).2, (hα x).1, (hα x).2])) hpoint
  simpa only [cdfDistance, A, integral_zero] using H

private theorem joinedProfile_tail (α : ℝ → ℝ) (s h : ℝ) (N : ℕ)
    (hh : 0 ≤ h) {x : ℝ} (hx : s + 4 * h ≤ x) :
    OW.joinedWindowProfile α α (1 / 2) s h N x = α x := by
  unfold OW.joinedWindowProfile OW.relativeWindowProfile
  split_ifs <;> first | rfl | (exfalso; linarith)

theorem scalarWindow_eq_step_value {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s h : ℝ) {N : ℕ} (hN : 0 < N) (hh : 0 < h) (hs : 0 ≤ s)
    (hT : s + 4 * h ≤ 1) :
    scalarIncrementChain (OW.scalarWindow β α (1 / 2) s h N) (Phi β α (s + 4 * h)) =
      Phi β (OW.joinedWindowProfile α α (1 / 2) s h N) s := by
  let A := OW.joinedWindowProfile α α (1 / 2) s h N
  have hbA : ∀ x, A x ∈ Icc (0 : ℝ) 1 :=
    OW.joinedWindowProfile_bounds α α hα hα _ _ _ _
  have hp : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmA : Monotone A :=
    OW.joinedWindowProfile_monotone α α hm hm _ _ _ hN hh hp le_rfl
  have ht : Real.toNNReal (1 - (s + 4 * h)) ≤ 1 := Real.toNNReal_le_one.mpr (by linarith)
  have hΦ : BoundedDerivs (Phi β α (s + 4 * h)) :=
    scalarCDFValue_regular β hα hm _ _ ht
  have hLipΦ : LipschitzWith 1 (Phi β α (s + 4 * h)) :=
    scalarCDFValue_lipschitz β hα hm _ _ ht
  have htail : scalarCDFValue β A (s + 4 * h) (Real.toNNReal (1 - (s + 4 * h))) =
      Phi β α (s + 4 * h) := by
    funext z
    have hi : (∫ y in (s + 4 * h)..(s + 4 * h +
        (Real.toNNReal (1 - (s + 4 * h)) : ℝ)), |A y - α y|) = 0 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le
        (show s + 4 * h ≤ s + 4 * h + (Real.toNNReal (1 - (s + 4 * h)) : ℝ) by
          linarith [(Real.toNNReal (1 - (s + 4 * h))).coe_nonneg])
        (show (Ioo (s + 4 * h) (s + 4 * h +
          (Real.toNNReal (1 - (s + 4 * h)) : ℝ))).EqOn
            (fun y => |A y - α y|) (fun _ => 0) from fun y hy => by
              change |A y - α y| = 0
              rw [show A y = α y from joinedProfile_tail α s h N hh.le hy.1.le,
                sub_self, abs_zero]), intervalIntegral.integral_zero]
    have H := scalarCDFValue_cdf_lipschitz β hbA hmA hα hm (s + 4 * h) _ ht z
    rw [hi, mul_zero] at H
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))
  have hchain : scalarCDFOperator β A s (Real.toNNReal (4 * h)) (Phi β α (s + 4 * h)) =
      scalarIncrementChain (OW.scalarWindow β α (1 / 2) s h N) (Phi β α (s + 4 * h)) := by
    rw [OW.scalarWindow_eq_time β α _ _ _ hN hh.le ⟨hp.1.le, hp.2.le⟩,
      scalarIncrementChain_rawTimeChain]
    funext x
    apply scalarCDFOperator_eq_chain hΦ hLipΦ β hbA hmA _
      (OW.windowTimeChain_mass α hα _ _ _ N) s _
      (Real.toNNReal_le_one.mpr (by linarith)) _
      (OW.windowTimeChain_models α α _ _ _ hN hh hp) x
    apply NNReal.coe_injective
    rw [OW.windowTimeChain_duration α _ _ _ hN hh hp,
      Real.coe_toNNReal _ (by positivity)]
  change _ = scalarCDFValue β A s (Real.toNNReal (1 - s))
  rw [OW.scalarCDFValue_suffix_semigroup_monotone β A hbA hmA hs (by linarith) hT,
    htail, show s + 4 * h - s = 4 * h by ring, hchain]

theorem scalarWindow_tendstoUniformly {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s h : ℝ) (hh : 0 < h) (hs : 0 ≤ s) (hT : s + 4 * h ≤ 1) :
    TendstoUniformly
      (fun N : ℕ => scalarIncrementChain (OW.scalarWindow β α (1 / 2) s h (N + 1))
        (Phi β α (s + 4 * h))) (Phi β α s) atTop := by
  let A := fun N : ℕ => OW.joinedWindowProfile α α (1 / 2) s h (N + 1)
  have hbA : ∀ N x, A N x ∈ Icc (0 : ℝ) 1 :=
    fun N => OW.joinedWindowProfile_bounds α α hα hα _ _ _ _
  have hmA : ∀ N, Monotone (A N) := fun N =>
    OW.joinedWindowProfile_monotone α α hm hm _ _ _ (Nat.succ_pos N) hh
      ⟨by norm_num, by norm_num⟩ le_rfl
  have H := scalarCDFValue_tendstoUniformly_interval β hα hm hbA hmA
    (joinedProfile_cdfDistance_tendsto hα hm s h hh) s (Real.toNNReal (1 - s))
    (Real.toNNReal_le_one.mpr (by linarith)) hs
    (by rw [Real.coe_toNNReal _ (by linarith : 0 ≤ 1 - s)]; linarith)
  change TendstoUniformly (fun N => Phi β (A N) s) (Phi β α s) atTop at H
  convert H using 1
  funext N
  exact scalarWindow_eq_step_value hα hm s h (Nat.succ_pos N) hh hs hT

theorem cornerAverage_tendsto {β : ℝ} {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (r h : ℝ) (hh : 0 < h) (hs : 0 ≤ r - h) (hT : r - h + 4 * h ≤ 1)
    {g : ℝ → ℝ} {L B : ℝ≥0} (hg : LipschitzWith L g) (hB : ∀ z, |g z| ≤ B) :
    Tendsto (fun N => cornerAverage β α r h N g) atTop
      (𝓝 (scalarLaw β α (r - h) g)) := by
  let F := fun N : ℕ => scalarIncrementChain
    (OW.scalarWindow β α (1 / 2) (r - h) h (N + 1)) (Phi β α (r - h + 4 * h))
  have ht : Real.toNNReal (1 - (r - h + 4 * h)) ≤ 1 :=
    Real.toNNReal_le_one.mpr (by linarith)
  have hΦ : BoundedDerivs (Phi β α (r - h + 4 * h)) :=
    scalarCDFValue_regular β hα hm _ _ ht
  have hLipΦ : LipschitzWith 1 (Phi β α (r - h + 4 * h)) :=
    scalarCDFValue_lipschitz β hα hm _ _ ht
  have hF (N : ℕ) : BoundedDerivs (F N) := scalarIncrementChain_regular _ hΦ
  have hFK (N : ℕ) : LipschitzWith 1 (F N) :=
    scalarIncrementChain_lipschitz _
      (fun u hu => (OW.scalarWindow_mass_mem β α hα _ _ _ (N + 1) u hu).1) hΦ hLipΦ
  have hts : Real.toNNReal (1 - (r - h)) ≤ 1 := Real.toNNReal_le_one.mpr (by linarith)
  have hf : BoundedDerivs (Phi β α (r - h)) := scalarCDFValue_regular β hα hm _ _ hts
  have hfK : LipschitzWith 1 (Phi β α (r - h)) := scalarCDFValue_lipschitz β hα hm _ _ hts
  have hFU : TendstoUniformly F (Phi β α (r - h)) atTop :=
    scalarWindow_tendstoUniformly hα hm (r - h) h hh hs hT
  have hDU : Tendsto (fun _N : ℕ => cdfDistance α α) atTop (𝓝 0) := by
    simpa only [cdfDistance, sub_self, abs_zero, integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _N : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hgU : TendstoUniformly (fun _N : ℕ => g) g atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact .of_forall fun _ _ => by simpa only [dist_self] using hε
  have hprefix : Real.toNNReal (r - h) ≤ 1 := Real.toNNReal_le_one.mpr (by linarith)
  have H := scalarCDFAverage_tendstoUniformly_varying β hα hm (fun _ => hα) (fun _ => hm)
    hDU hf hF hfK hFK hg (fun _ => hg) hB (fun _ => hB) hFU hgU
    0 (Real.toNNReal (r - h)) hprefix le_rfl
    (by rw [zero_add, Real.coe_toNNReal _ hs]; linarith)
  have hrep (N : ℕ) : cornerAverage β α r h (N + 1) g =
      scalarCDFAverage β α 0 (Real.toNNReal (r - h)) (F N) g 0 := by
    unfold cornerAverage
    have he : OW.boundary β α (1 / 2) (r - h) h 0 (N + 1) = fun z => 3 * F N z :=
      funext (OW.boundary_zero_factorization β α _ _ _ _ hΦ)
    rw [he, scalarCDFAverage_div_three]
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [hrep, scalarLaw] using H.tendsto_at 0

private theorem jet_power_test {β : ℝ} (D : ScalarData β) (j n : ℕ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ L B : ℝ≥0, LipschitzWith L (fun z => jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z ^ n) ∧
      ∀ z, |jet β (cdf (D.μ : Measure ℝ)) (j + 1) s z ^ n| ≤ B := by
  let μ := Bridge.overlapMeasure D.μ D.mass_one
  have H := Bridge.parisiSpatialJet_power_test β μ j n s
  simp_rw [← Bridge.jet_succ_eq_parisiSpatialJet β μ j s hs] at H
  simpa only [μ, Bridge.realMeasure_overlapMeasure] using H

end PrefixMoments

theorem prefixMomentConvergence_of_scalarData {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hu : u < D.q) :
    PrefixMomentConvergence β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  refine ⟨min (l / 2) ((D.q - u) / 4), lt_min (by positivity) (by positivity), ?_⟩
  intro r hr h hh hh₀
  have hhl := hh₀.trans (min_le_left _ _)
  have hhu := hh₀.trans (min_le_right _ _)
  have hs : r - h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2, D.q_mem.2]⟩
  have hT : r - h + 4 * h ≤ 1 := by linarith [hr.2, D.q_mem.2]
  have H (j n : ℕ) : Tendsto
      (fun N => cornerAverage β (cdf (D.μ : Measure ℝ)) r h N
        (fun z => jet β (cdf (D.μ : Measure ℝ)) (j + 1) (r - h) z ^ n)) atTop
      (𝓝 (scalarLaw β (cdf (D.μ : Measure ℝ)) (r - h)
        (fun z => jet β (cdf (D.μ : Measure ℝ)) (j + 1) (r - h) z ^ n))) := by
    obtain ⟨L, B, hL, hB⟩ := PrefixMoments.jet_power_test D j n (r - h) hs
    exact PrefixMoments.cornerAverage_tendsto
      (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩) (cdf _).mono r h hh hs.1 hT hL hB
  exact ⟨H 1 2, H 1 3, H 2 2⟩

theorem cornerInputs_of_coreIdentity' {β l u : ℝ} (D : ScalarData β)
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < D.q)
    (hcore : CoreIdentity β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hpen : PenaltyBound β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    LocalCubicGap β (cdf (D.μ : Measure ℝ)) (Icc l u) ∧
      LocalBoundaryControl β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact cornerInputs_of_coreIdentity D hl hlu hu hcore hpen
    (prefixMomentConvergence_of_scalarData D hl hu)

end SKBarriers2
