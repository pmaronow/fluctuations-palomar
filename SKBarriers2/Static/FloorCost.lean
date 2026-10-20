module

public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Parisi.CDFMassRemainder
public import OAI.Probability.SKBarriers.Parisi.CDFSupportContact

@[expose] public section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Set
open OAI OAI.SK OAI.SK.Analytic

namespace SKBarriers2

private theorem floor_localization {α : ℝ → ℝ} (hm : Monotone α)
    (ha : ∀ t, 0 ≤ α t) {c T s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hlin : ∀ t ∈ Icc (0 : ℝ) T, c * t ≤ α t)
    (hrT : 3 * s / c ≤ T) (hr1 : 3 * s / c ≤ 1) :
    (∀ t, 3 * s / c ≤ t → max (α t) (3 * s) = α t) ∧
      cdfDistance (fun t => max (α t) (3 * s)) α ≤ (9 / c) * s ^ 2 := by
  let r : ℝ := 3 * s / c
  have hr : 0 ≤ r := div_nonneg (mul_nonneg (by norm_num) hs) hc.le
  have hcr : c * r = 3 * s := by dsimp only [r]; field_simp
  have hloc (t : ℝ) (ht : r ≤ t) : max (α t) (3 * s) = α t := by
    apply max_eq_left
    calc
      3 * s = c * r := hcr.symm
      _ ≤ α r := hlin r ⟨hr, hrT⟩
      _ ≤ α t := hm ht
  refine ⟨hloc, ?_⟩
  let d : ℝ → ℝ := fun t => |max (α t) (3 * s) - α t|
  have hi (u v : ℝ) : IntervalIntegrable d volume u v :=
    (((hm.max monotone_const).intervalIntegrable).sub hm.intervalIntegrable).abs
  have htail : (∫ t in r..(1 : ℝ), d t) = 0 := by
    calc
      _ = ∫ _t in r..(1 : ℝ), (0 : ℝ) := intervalIntegral.integral_congr
        (fun t ht => by
          have hrt : r ≤ t := (show t ∈ Icc r 1 by
            simpa only [uIcc_of_le (show r ≤ 1 from hr1)] using ht).1
          simp only [d, hloc t hrt, sub_self, abs_zero])
      _ = 0 := intervalIntegral.integral_zero
  have hsmall : (∫ t in (0 : ℝ)..r, d t) ≤ (3 * s) * r := by
    have H := intervalIntegral.integral_mono_on hr (hi 0 r) intervalIntegrable_const
      (show ∀ t ∈ Icc (0 : ℝ) r, d t ≤ 3 * s from fun t _ => by
        dsimp only [d]
        rw [abs_of_nonneg (sub_nonneg.mpr (le_max_left _ _))]
        exact sub_le_iff_le_add.mpr (max_le (by linarith) (by linarith [ha t])))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using H
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 r) (hi r 1)
  rw [htail, add_zero] at hsplit
  change (∫ t in Icc (0 : ℝ) 1, d t) ≤ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← hsplit]
  exact hsmall.trans_eq (by dsimp only [r]; ring)

private theorem floor_modulus_sqrt (β : ℝ) {D : ℝ} (hD : 0 < D)
    (hD1 : D ≤ 1) (hsmall : 2 * scalarTimeMassConstant β * D ≤ 1) :
    scalarOverlapModulus β D (Real.sqrt D) ≤
      (12 * scalarTimeMassConstant β + 2 * scalarTimeMassConstantK β 3 + 12) *
        Real.sqrt D := by
  have hA := scalarTimeMassConstant_nonneg β
  have hs := Real.sqrt_pos.mpr hD
  have hsq := Real.sq_sqrt hD.le
  have hs1 : Real.sqrt D ≤ 1 := (Real.sqrt_le_one).mpr hD1
  have hDs : D ≤ Real.sqrt D := by nlinarith
  have he := Real.abs_exp_sub_one_le (x := 2 * (scalarTimeMassConstant β * D))
    (by rw [abs_of_nonneg (by positivity)]; nlinarith)
  have he' : Real.exp (2 * (scalarTimeMassConstant β * D)) - 1 ≤
      4 * scalarTimeMassConstant β * Real.sqrt D := by
    rw [abs_of_nonneg (show 0 ≤ 2 * (scalarTimeMassConstant β * D) by positivity)] at he
    have H := mul_le_mul_of_nonneg_left hDs (show 0 ≤ 4 * scalarTimeMassConstant β by
      positivity)
    exact (le_abs_self _).trans (he.trans (by nlinarith))
  have hdiv : D / Real.sqrt D = Real.sqrt D := by
    apply (div_eq_iff hs.ne').mpr
    nlinarith
  unfold scalarOverlapModulus
  rw [mul_div_assoc, hdiv]
  nlinarith

private theorem floor_remainder_cubic (β : ℝ) (α γ : StieltjesFunction ℝ)
    (ha : ∀ t, α t ∈ Icc (0 : ℝ) 1) (ha1 : α 1 = 1)
    (hg : ∀ t, γ t ∈ Icc (0 : ℝ) 1) (hg1 : γ 1 = 1)
    (hlin : (β ^ 2 / 2) *
      (∫ t in Icc (0 : ℝ) 1, (γ t - α t) * (scalarCDFOverlap β α t - t)) = 0)
    {B s : ℝ} (hB : 0 < B) (hs : 0 ≤ s)
    (hD : cdfDistance γ α ≤ B * s ^ 2)
    (hD1 : cdfDistance γ α ≤ 1)
    (hsmall : 2 * scalarTimeMassConstant β * cdfDistance γ α ≤ 1) :
    scalarCDFParisi β γ - scalarCDFParisi β α ≤
      ((β ^ 2 / 2) *
        (12 * scalarTimeMassConstant β + 2 * scalarTimeMassConstantK β 3 + 12) *
        B * Real.sqrt B) * s ^ 3 := by
  let D : ℝ := cdfDistance γ α
  let K : ℝ := 12 * scalarTimeMassConstant β + 2 * scalarTimeMassConstantK β 3 + 12
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity [scalarTimeMassConstant_nonneg β, scalarTimeMassConstantK_nonneg β 3]
  have hD0 : 0 ≤ D := cdfDistance_nonneg γ α
  by_cases hz : D = 0
  · have H := scalarCDFParisi_mass_remainder β α γ ha ha1 hg hg1 zero_lt_one
    rw [hlin, sub_zero] at H
    change |scalarCDFParisi β γ - scalarCDFParisi β α| ≤ (β ^ 2 / 2) * D * _ at H
    rw [hz, mul_zero, zero_mul] at H
    exact ((le_abs_self _).trans H).trans (by positivity)
  · have hDp : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hz)
    have H := scalarCDFParisi_mass_remainder β α γ ha ha1 hg hg1 (Real.sqrt_pos.mpr hDp)
    rw [hlin, sub_zero] at H
    have hm := floor_modulus_sqrt β hDp hD1 hsmall
    have hsqrt : Real.sqrt D ≤ Real.sqrt B * s := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨mul_nonneg (Real.sqrt_nonneg B) hs, ?_⟩
      nlinarith [Real.sq_sqrt hB.le]
    calc
      scalarCDFParisi β γ - scalarCDFParisi β α ≤
          (β ^ 2 / 2) * D * scalarOverlapModulus β D (Real.sqrt D) :=
        (le_abs_self _).trans H
      _ ≤ (β ^ 2 / 2) * D * (K * Real.sqrt D) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ (β ^ 2 / 2) * (B * s ^ 2) * (K * (Real.sqrt B * s)) := by
        gcongr
      _ = ((β ^ 2 / 2) * K * B * Real.sqrt B) * s ^ 3 := by ring

theorem floorTrial_of_scalar_facts {β : ℝ} (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0 : ℝ) 1) = 1)
    {α : ℝ → ℝ} (hαcdf : α = cdf (μ : Measure ℝ))
    (hmin : scalarCDFParisi β α = finiteParisiInf β)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : (μ : Measure ℝ).support = Icc 0 q)
    {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hlin : ∀ t ∈ Icc (0 : ℝ) T, c * t ≤ α t)
    (hm : Monotone α) (ha : ∀ t, α t ∈ Icc (0 : ℝ) 1)
    (hrc : ∀ t, ContinuousWithinAt α (Ici t) t) (ha1 : α 1 = 1) :
    FloorTrial β α 3 := by
  let a : StieltjesFunction ℝ := ⟨α, hm, hrc⟩
  let B : ℝ := 9 / c
  let K : ℝ := 12 * scalarTimeMassConstant β + 2 * scalarTimeMassConstantK β 3 + 12
  let P : ℝ := (β ^ 2 / 2) * K * B * Real.sqrt B
  let C : ℝ := 1 + 3 / c + B + P
  let u : ℝ := min T (min q 1)
  let H : ℝ := B * (2 * scalarTimeMassConstant β + 1) + 1
  let s₀ : ℝ := min (c * u / 3) (min (1 / 3) (1 / H))
  have hA := scalarTimeMassConstant_nonneg β
  have hB : 0 < B := div_pos (by norm_num) hc
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity [scalarTimeMassConstant_nonneg β, scalarTimeMassConstantK_nonneg β 3]
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hu : 0 < u := lt_min hT (lt_min hq.1 zero_lt_one)
  have hH : 0 < H := by dsimp only [H]; positivity
  have hs₀ : 0 < s₀ := lt_min (div_pos (mul_pos hc hu) (by norm_num))
    (lt_min (by norm_num) (one_div_pos.mpr hH))
  have hL : 0 ≤ 3 / c := by positivity
  have hCB : B ≤ C := by dsimp only [C]; linarith
  have hCP : P ≤ C := by dsimp only [C]; linarith
  have hCL : 3 / c ≤ C := by dsimp only [C]; linarith
  refine ⟨C, s₀, hC, hs₀, ?_⟩
  intro s hs
  have hs3 : s ≤ 1 / 3 := hs.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 : s ≤ 1 := by linarith
  have hsH : s ≤ 1 / H := hs.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsu : s ≤ c * u / 3 := hs.2.trans (min_le_left _ _)
  have hru : 3 * s / c ≤ u := (div_le_iff₀ hc).mpr (by linarith)
  have hrT : 3 * s / c ≤ T := hru.trans (min_le_left _ _)
  have hrq : 3 * s / c ≤ q := hru.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : 3 * s / c ≤ 1 := hru.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hloc, hD⟩ := floor_localization hm (fun t => (ha t).1) hc hs.1.le hlin hrT hr1
  let g : StieltjesFunction ℝ :=
    ⟨fun t => max (α t) (3 * s), hm.max monotone_const,
      fun t => (hrc t).max continuousWithinAt_const⟩
  have hg : ∀ t, g t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨(ha t).1.trans (le_max_left _ _), max_le (ha t).2 (by linarith)⟩
  have hg1 : g 1 = 1 := by change max (α 1) (3 * s) = 1; rw [ha1, max_eq_left (by linarith)]
  have hlinear : (β ^ 2 / 2) *
      (∫ t in Icc (0 : ℝ) 1, (g t - a t) * (scalarCDFOverlap β a t - t)) = 0 := by
    by_cases hβ : β = 0
    · simp only [hβ, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, zero_mul]
    · have hi : (∫ t in Icc (0 : ℝ) 1,
          (g t - a t) * (scalarCDFOverlap β a t - t)) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        by_cases htq : t ≤ q
        · have hcontact : scalarCDFOverlap β a t = t := by
            change scalarCDFOverlap β α t = t
            rw [hαcdf]
            apply scalarCDFParisi_overlap_on_support hβ μ hμ (hαcdf ▸ hmin)
            rw [hsupp]
            exact ⟨ht.1, htq⟩
          simp only [hcontact, sub_self, mul_zero, Pi.zero_apply]
        · have hgt : g t = a t := hloc t (hrq.trans (le_of_not_ge htq))
          simp only [hgt, sub_self, zero_mul, Pi.zero_apply]
      rw [hi, mul_zero]
  have hD0 : 0 ≤ cdfDistance g a := cdfDistance_nonneg g a
  have hDs : cdfDistance g a ≤ B * s := by
    calc
      _ ≤ B * s ^ 2 := hD
      _ ≤ B * s := mul_le_mul_of_nonneg_left
        (by nlinarith [mul_nonneg hs.1.le (sub_nonneg.mpr hs1)] : s ^ 2 ≤ s) hB.le
  have hHs : s * H ≤ 1 := (le_div_iff₀ hH).mp hsH
  have hmass : (2 * scalarTimeMassConstant β + 1) * cdfDistance g a ≤ 1 := by
    have Hb := mul_le_mul_of_nonneg_left hDs
      (show 0 ≤ 2 * scalarTimeMassConstant β + 1 by positivity)
    dsimp only [H] at hHs
    nlinarith
  have hD1 : cdfDistance g a ≤ 1 := by
    nlinarith [mul_nonneg hA hD0]
  have hsmall : 2 * scalarTimeMassConstant β * cdfDistance g a ≤ 1 := by
    nlinarith
  have hcost := floor_remainder_cubic β a g ha ha1 hg hg1 hlinear hB hs.1.le hD hD1 hsmall
  refine ⟨?_, ?_, ?_⟩
  · change scalarCDFParisi β g - finiteParisiInf β ≤ C * s ^ (3 : ℝ)
    rw [← hmin, Real.rpow_ofNat]
    exact hcost.trans (mul_le_mul_of_nonneg_right hCP (pow_nonneg hs.1.le 3))
  · intro t ht
    apply hloc t
    have Hloc := mul_le_mul_of_nonneg_right hCL hs.1.le
    calc
      3 * s / c = (3 / c) * s := by ring
      _ ≤ C * s := Hloc
      _ ≤ t := ht
  · exact hD.trans (mul_le_mul_of_nonneg_right hCB (sq_nonneg s))

theorem ScalarData.floorTrial {β : ℝ} (D : ScalarData β) :
    FloorTrial β (cdf (D.μ : Measure ℝ)) 3 := by
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  exact floorTrial_of_scalar_facts D.μ D.mass_one rfl D.minimizer D.q_mem D.support
    hc hT hlin (cdf (D.μ : Measure ℝ)).mono
    (fun t => ⟨cdf_nonneg _ t, cdf_le_one _ t⟩)
    (cdf (D.μ : Measure ℝ)).right_continuous (supported_probability_cdf_one D.μ D.mass_one)

end SKBarriers2
