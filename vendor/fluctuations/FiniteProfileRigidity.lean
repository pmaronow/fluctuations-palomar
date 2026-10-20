module

public import Mathlib
public import LowerLedger

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Set MeasureTheory Filter
open scoped Topology

theorem affine_second_derivative_gap_identity
    {a b A C : ℝ} (hab : a < b) (g gp : ℝ → ℝ)
    (hgc : ContinuousOn g (Icc a b)) (hgpc : ContinuousOn gp (Icc a b))
    (hg : ∀ t ∈ Ico a b, HasDerivWithinAt g (gp t) (Ici t) t)
    (hgp : ∀ t ∈ Ico a b, HasDerivWithinAt gp (A * t - C) (Ici t) t)
    (hga : g a = 0) (hgb : g b = 0) :
    gp a + gp b = A / 6 * (b - a) ^ 2 := by
  let p : ℝ → ℝ := fun t => gp a + A / 2 * (t ^ 2 - a ^ 2) - C * (t - a)
  have hpd (t : ℝ) : HasDerivAt p (A * t - C) t := by
    dsimp [p]
    convert ((hasDerivAt_const t (gp a)).add
      ((((hasDerivAt_id t).pow 2).sub_const (a ^ 2)).const_mul (A / 2))).sub
      (((hasDerivAt_id t).sub_const a).const_mul C) using 1 <;>
      (try ext y) <;> dsimp <;> ring
  have hpeq : ∀ t ∈ Icc a b, gp t = p t := by
    apply eq_of_has_deriv_right_eq hgp
      (fun t _ => (hpd t).hasDerivWithinAt) hgpc
      (fun t _ => (hpd t).continuousAt.continuousWithinAt)
    simp [p]
  let P : ℝ → ℝ := fun t =>
    g a + gp a * (t - a) + A / 6 * (t ^ 3 - a ^ 3) -
      A / 2 * a ^ 2 * (t - a) - C / 2 * (t - a) ^ 2
  have hPd (t : ℝ) : HasDerivAt P (p t) t := by
    dsimp [P, p]
    convert ((((hasDerivAt_const t (g a)).add
      (((hasDerivAt_id t).sub_const a).const_mul (gp a))).add
      ((((hasDerivAt_id t).pow 3).sub_const (a ^ 3)).const_mul (A / 6))).sub
      (((hasDerivAt_id t).sub_const a).const_mul (A / 2 * a ^ 2))).sub
      ((((hasDerivAt_id t).sub_const a).pow 2).const_mul (C / 2)) using 1 <;>
      (try ext y) <;> dsimp <;> ring
  have hPeq : ∀ t ∈ Icc a b, g t = P t := by
    apply eq_of_has_deriv_right_eq hg
      (fun t ht => by
        rw [hpeq t ⟨ht.1, ht.2.le⟩]
        exact (hPd t).hasDerivWithinAt)
      hgc (fun t _ => (hPd t).continuousAt.continuousWithinAt)
    simp [P]
  have hb := hPeq b ⟨hab.le, le_rfl⟩
  have hpb := hpeq b ⟨hab.le, le_rfl⟩
  dsimp [P] at hb
  dsimp [p] at hpb
  rw [hga, hgb] at hb
  have hw : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  apply (mul_right_cancel₀ hw)
  nlinarith [hb]

theorem no_gap_of_affine_second_derivative
    {a b A C : ℝ} (hab : a < b) (hA : 0 < A) (g gp : ℝ → ℝ)
    (hgc : ContinuousOn g (Icc a b)) (hgpc : ContinuousOn gp (Icc a b))
    (hg : ∀ t ∈ Ico a b, HasDerivWithinAt g (gp t) (Ici t) t)
    (hgp : ∀ t ∈ Ico a b, HasDerivWithinAt gp (A * t - C) (Ici t) t)
    (hga : g a = 0) (hgb : g b = 0)
    (hslopea : gp a ≤ 0) (hslopeb : gp b ≤ 0) : False := by
  have hid := affine_second_derivative_gap_identity hab g gp hgc hgpc hg hgp hga hgb
  have hpositive : 0 < A / 6 * (b - a) ^ 2 := by positivity
  linarith

theorem affine_derivative_endpoint_identity
    {a b A C : ℝ} (hab : a ≤ b) (gp : ℝ → ℝ)
    (hcont : ContinuousOn gp (Icc a b))
    (hgp : ∀ t ∈ Ico a b, HasDerivWithinAt gp (A * t - C) (Ici t) t) :
    gp b = gp a + A / 2 * (b ^ 2 - a ^ 2) - C * (b - a) := by
  let p : ℝ → ℝ := fun t => gp a + A / 2 * (t ^ 2 - a ^ 2) - C * (t - a)
  have hd (t : ℝ) : HasDerivAt p (A * t - C) t := by
    dsimp [p]
    convert ((hasDerivAt_const t (gp a)).add
      ((((hasDerivAt_id t).pow 2).sub_const (a ^ 2)).const_mul (A / 2))).sub
      (((hasDerivAt_id t).sub_const a).const_mul C) using 1 <;>
      (try ext y) <;> dsimp <;> ring
  exact eq_of_has_deriv_right_eq hgp
    (fun t _ => (hd t).hasDerivWithinAt) hcont
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (by simp [p]) b ⟨hab, le_rfl⟩

theorem no_positive_initial_gap
    {l A : ℝ} (hl : 0 < l) (hA : 0 < A) (g gp : ℝ → ℝ)
    (hgc : ContinuousOn g (Icc 0 l)) (hgpc : ContinuousOn gp (Icc 0 l))
    (hg : ∀ t ∈ Ico 0 l, HasDerivWithinAt g (gp t) (Ici t) t)
    (hgp : ∀ t ∈ Ico 0 l, HasDerivWithinAt gp (A * t) (Ici t) t)
    (hg0 : g 0 = 0) (hgl : g l = 0) (hgpl : gp l = 0) : False := by
  have hgp' : ∀ t ∈ Ico 0 l, HasDerivWithinAt gp (A * t - 0) (Ici t) t := by
    simpa only [sub_zero] using hgp
  have hsum := affine_second_derivative_gap_identity (C := 0) hl g gp
    hgc hgpc hg hgp' hg0 hgl
  have hend := affine_derivative_endpoint_identity (C := 0) hl.le gp hgpc hgp'
  simp only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, zero_mul, hgpl] at hsum hend
  have hpos : 0 < A * l ^ 2 := mul_pos hA (sq_pos_of_pos hl)
  linarith

theorem intervalIntegral_neg_of_negative_ae
    {a b : ℝ} (hab : a < b) (F : ℝ → ℝ)
    (hi : IntervalIntegrable F volume a b)
    (hnegative : ∀ᵐ t ∂volume.restrict (Ioo a b), F t < 0) :
    (∫ t in a..b, F t) < 0 := by
  have hn : ∀ᵐ t ∂volume.restrict (Ioc a b), F t < 0 := by
    rwa [← restrict_Ioo_eq_restrict_Ioc]
  have hnall := (ae_restrict_iff' measurableSet_Ioc).mp hn
  have hsupp : (Function.support (fun t => -F t) ∩ Ioc a b) =ᵐ[volume] Ioc a b := by
    filter_upwards [hnall] with t ht
    by_cases htab : t ∈ Ioc a b
    · have hne : F t ≠ 0 := (ht htab).ne
      simp [Function.mem_support, htab, hne]
    · simp [htab]
  have hnonnegative : 0 ≤ᵐ[volume.restrict (uIoc a b)] (fun t => -F t) := by
    rw [uIoc_of_le hab.le]
    exact hn.mono (fun t ht => (neg_pos.mpr ht).le)
  have hpos : 0 < ∫ t in a..b, -F t := by
    apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hnonnegative hi.neg).mpr
    refine ⟨hab, ?_⟩
    rw [measure_congr hsupp]
    simp [Real.volume_Ioc, hab, ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)]
  rw [intervalIntegral.integral_neg] at hpos
  linarith

theorem nonnegative_potential_excludes_negative_initial_density
    {a b : ℝ} (hab : a < b) (H F : ℝ → ℝ)
    (hH : ∀ t ∈ Icc a b, 0 ≤ H t) (hHa : H a = 0)
    (hi : IntervalIntegrable F volume a b)
    (hprimitive : H b - H a = ∫ t in a..b, F t)
    (hnegative : ∀ᵐ t ∂volume.restrict (Ioo a b), F t < 0) : False := by
  have hneg := intervalIntegral_neg_of_negative_ae hab F hi hnegative
  have hHb := hH b ⟨hab.le, le_rfl⟩
  rw [hHa] at hprimitive
  linarith

theorem positive_endpoint_slope_right
    {a b d : ℝ} (hab : a < b) (hd : 0 < d) (g : ℝ → ℝ)
    (hg : HasDerivAt g d a) (hga : g a = 0) :
    ∃ z ∈ Ioc a b, ∀ t ∈ Ioo a z, 0 < g t := by
  have ht : Tendsto (slope g a) (𝓝[>] a) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show a ∉ Ioi a by simp)).mp
      hg.hasDerivWithinAt
  obtain ⟨z, hz, hzsub⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab).mp
      (ht.eventually (eventually_gt_nhds hd))
  refine ⟨z, hz, ?_⟩
  intro t htab
  have hpositive := hzsub htab
  change 0 < slope g a t at hpositive
  rw [slope_def_field, hga, sub_zero] at hpositive
  exact (div_pos_iff_of_pos_right (sub_pos.mpr htab.1)).mp hpositive

theorem positive_endpoint_slope_left
    {a b d : ℝ} (hab : a < b) (hd : 0 < d) (g : ℝ → ℝ)
    (hg : HasDerivAt g d b) (hgb : g b = 0) :
    ∃ z ∈ Ico a b, ∀ t ∈ Ioo z b, g t < 0 := by
  have ht : Tendsto (slope g b) (𝓝[<] b) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show b ∉ Iio b by simp)).mp
      hg.hasDerivWithinAt
  obtain ⟨z, hz, hzsub⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hab).mp
      (ht.eventually (eventually_gt_nhds hd))
  refine ⟨z, hz, ?_⟩
  intro t htab
  have hpositive := hzsub htab
  change 0 < slope g b t at hpositive
  rw [slope_def_field, hgb, sub_zero] at hpositive
  have hden : t - b < 0 := sub_neg.mpr htab.2
  have hmul := (lt_div_iff_of_neg hden).mp hpositive
  simpa using hmul

theorem closure_forces_above_radius
    {a z b t v h : ℝ} (g : ℝ → ℝ)
    (haz : a < z) (ht : t ∈ Ioo a z) (hv : v ∈ Icc a b) (hh : 0 < h)
    (hga : g a = 0) (hpositive : ∀ y ∈ Ioo a z, 0 < g y)
    (hclosure : g v = h * (v - t)) : t < v := by
  by_cases hvz : z ≤ v
  · exact ht.2.trans_le hvz
  · have hvza : v < z := not_le.mp hvz
    by_cases hva : v = a
    · rw [hva, hga] at hclosure
      have hnegative : h * (a - t) < 0 := mul_neg_of_pos_of_neg hh (sub_neg.mpr ht.1)
      linarith
    · have hvg : 0 < g v := hpositive v ⟨lt_of_le_of_ne hv.1 (Ne.symm hva), hvza⟩
      rw [hclosure] at hvg
      exact sub_pos.mp ((mul_pos_iff_of_pos_left hh).mp hvg)

theorem closure_forces_below_radius
    {a z b t v h : ℝ} (g : ℝ → ℝ)
    (hzb : z < b) (ht : t ∈ Ioo z b) (hv : v ∈ Icc a b) (hh : 0 < h)
    (hgb : g b = 0) (hnegative : ∀ y ∈ Ioo z b, g y < 0)
    (hclosure : g v = h * (v - t)) : v < t := by
  by_cases hvz : v ≤ z
  · exact hvz.trans_lt ht.1
  · have hvza : z < v := not_le.mp hvz
    by_cases hvb : v = b
    · rw [hvb, hgb] at hclosure
      have hpositive : 0 < h * (b - t) := mul_pos hh (sub_pos.mpr ht.2)
      linarith
    · have hvg : g v < 0 := hnegative v ⟨hvza, lt_of_le_of_ne hv.2 hvb⟩
      rw [hclosure] at hvg
      have hneg : v - t < 0 := by
        by_contra hn
        have hnonneg : 0 ≤ h * (v - t) := mul_nonneg hh.le (not_lt.mp hn)
        linarith
      exact sub_neg.mp hneg

theorem virtual_potential_left_slope_nonpos
    {a b d : ℝ} (hab : a < b) (g H F spin strength : ℝ → ℝ)
    (hg : HasDerivAt g d a) (hga : g a = 0)
    (hH : ∀ t ∈ Icc a b, 0 ≤ H t) (hHa : H a = 0)
    (hi : IntervalIntegrable F volume a b)
    (hprimitive : ∀ z ∈ Icc a b, H z - H a = ∫ t in a..z, F t)
    (hproperties : ∀ᵐ t ∂volume.restrict (Ioo a b),
      spin t ∈ Icc a b ∧ 0 < strength t ∧
      g (spin t) = strength t * (spin t - t) ∧ (t < spin t → F t < 0)) : d ≤ 0 := by
  by_contra hn
  obtain ⟨z, hz, hgz⟩ := positive_endpoint_slope_right hab (not_le.mp hn) g hg hga
  have hprops : ∀ᵐ t ∂volume.restrict (Ioo a z),
      spin t ∈ Icc a b ∧ 0 < strength t ∧
      g (spin t) = strength t * (spin t - t) ∧ (t < spin t → F t < 0) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hz.2) hproperties
  have hnegative : ∀ᵐ t ∂volume.restrict (Ioo a z), F t < 0 := by
    filter_upwards [hprops, ae_restrict_mem measurableSet_Ioo] with t ht htz
    exact ht.2.2.2 (closure_forces_above_radius g hz.1 htz ht.1 ht.2.1 hga hgz ht.2.2.1)
  have hiz : IntervalIntegrable F volume a z := hi.mono_set (by
    rw [uIcc_of_le hz.1.le, uIcc_of_le hab.le]
    exact Icc_subset_Icc le_rfl hz.2)
  exact nonnegative_potential_excludes_negative_initial_density hz.1 H F
    (fun t ht => hH t ⟨ht.1, ht.2.trans hz.2⟩) hHa hiz
    (hprimitive z ⟨hz.1.le, hz.2⟩) hnegative

theorem virtual_potential_right_slope_nonpos
    {a b d : ℝ} (hab : a < b) (g H F spin strength : ℝ → ℝ)
    (hg : HasDerivAt g d b) (hgb : g b = 0)
    (hH : ∀ t ∈ Icc a b, 0 ≤ H t) (hHb : H b = 0)
    (hi : IntervalIntegrable F volume a b)
    (hprimitive : ∀ z ∈ Icc a b, H b - H z = ∫ t in z..b, F t)
    (hproperties : ∀ᵐ t ∂volume.restrict (Ioo a b),
      spin t ∈ Icc a b ∧ 0 < strength t ∧
      g (spin t) = strength t * (spin t - t) ∧ (spin t < t → 0 < F t)) : d ≤ 0 := by
  by_contra hn
  obtain ⟨z, hz, hgz⟩ := positive_endpoint_slope_left hab (not_le.mp hn) g hg hgb
  have hprops : ∀ᵐ t ∂volume.restrict (Ioo z b),
      spin t ∈ Icc a b ∧ 0 < strength t ∧
      g (spin t) = strength t * (spin t - t) ∧ (spin t < t → 0 < F t) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_left hz.1) hproperties
  have hpositive : ∀ᵐ t ∂volume.restrict (Ioo z b), 0 < F t := by
    filter_upwards [hprops, ae_restrict_mem measurableSet_Ioo] with t ht htz
    exact ht.2.2.2 (closure_forces_below_radius g hz.2 htz ht.1 ht.2.1 hgb hgz ht.2.2.1)
  have hiz : IntervalIntegrable F volume z b := hi.mono_set (by
    rw [uIcc_of_le hz.2.le, uIcc_of_le hab.le]
    exact Icc_subset_Icc hz.1 le_rfl)
  have hneg := intervalIntegral_neg_of_negative_ae hz.2 (fun t => -F t) hiz.neg
    (hpositive.mono (fun t ht => neg_neg_of_pos ht))
  rw [intervalIntegral.integral_neg] at hneg
  have hprim := hprimitive z ⟨hz.1, hz.2.le⟩
  have hHz := hH z ⟨hz.1, hz.2.le⟩
  rw [hHb] at hprim
  linarith

theorem stationarity_density_sign
    {t v p h j : ℝ} (ht : 0 < t) (hv : 0 ≤ v)
    (hp : p ∈ Icc (0 : ℝ) 1) (hh : 0 < h) (hj : 0 < j) :
    (j * h * ((2 - p) * t - 2 * (1 - p) * v - p * v ^ 2 / t) =
      j * h * (t - v) * (2 - p + p * v / t)) ∧
    (t < v → j * h * ((2 - p) * t - 2 * (1 - p) * v - p * v ^ 2 / t) < 0) ∧
    (v < t → 0 < j * h * ((2 - p) * t - 2 * (1 - p) * v - p * v ^ 2 / t)) := by
  have hid : j * h * ((2 - p) * t - 2 * (1 - p) * v - p * v ^ 2 / t) =
      j * h * (t - v) * (2 - p + p * v / t) := by
    field_simp [ht.ne']
    ring
  have hfactor : 0 < 2 - p + p * v / t := by
    have hnonneg : 0 ≤ p * v / t := div_nonneg (mul_nonneg hp.1 hv) ht.le
    linarith [hp.2]
  refine ⟨hid, ?_, ?_⟩
  · intro htv
    rw [hid]
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (mul_pos hj hh) (sub_neg.mpr htv)) hfactor
  · intro hvt
    rw [hid]
    exact mul_pos (mul_pos (mul_pos hj hh) (sub_pos.mpr hvt)) hfactor

theorem no_gap_of_bounded_strength_virtual_potential
    {a b A C : ℝ} (hab : a < b) (hA : 0 < A)
    (g gp H F spin strength : ℝ → ℝ)
    (hgc : ContinuousOn g (Icc a b)) (hgpc : ContinuousOn gp (Icc a b))
    (hg : ∀ t ∈ Ico a b, HasDerivWithinAt g (gp t) (Ici t) t)
    (hgp : ∀ t ∈ Ico a b, HasDerivWithinAt gp (A * t - C) (Ici t) t)
    (hgda : HasDerivAt g (gp a) a) (hgdb : HasDerivAt g (gp b) b)
    (hga : g a = 0) (hgb : g b = 0)
    (hH : ∀ t ∈ Icc a b, 0 ≤ H t) (hHa : H a = 0) (hHb : H b = 0)
    (hi : IntervalIntegrable F volume a b)
    (hprimitivea : ∀ z ∈ Icc a b, H z - H a = ∫ t in a..z, F t)
    (hprimitiveb : ∀ z ∈ Icc a b, H b - H z = ∫ t in z..b, F t)
    (hproperties : ∀ᵐ t ∂volume.restrict (Ioo a b),
      spin t ∈ Icc a b ∧ 0 < strength t ∧
      g (spin t) = strength t * (spin t - t) ∧
      (t < spin t → F t < 0) ∧ (spin t < t → 0 < F t)) : False := by
  have hslopea := virtual_potential_left_slope_nonpos hab g H F spin strength
    hgda hga hH hHa hi hprimitivea
    (hproperties.mono (fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩))
  have hslopeb := virtual_potential_right_slope_nonpos hab g H F spin strength
    hgdb hgb hH hHb hi hprimitiveb
    (hproperties.mono (fun t ht => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.2⟩))
  exact no_gap_of_affine_second_derivative hab hA g gp hgc hgpc hg hgp
    hga hgb hslopea hslopeb

theorem no_gap_of_scalar_sign_virtual_potential
    {a b A C : ℝ} (hab : a < b) (hA : 0 < A) (g gp H F : ℝ → ℝ)
    (hgc : ContinuousOn g (Icc a b)) (hgpc : ContinuousOn gp (Icc a b))
    (hg : ∀ t ∈ Ico a b, HasDerivWithinAt g (gp t) (Ici t) t)
    (hgp : ∀ t ∈ Ico a b, HasDerivWithinAt gp (A * t - C) (Ici t) t)
    (hgda : HasDerivAt g (gp a) a) (hgdb : HasDerivAt g (gp b) b)
    (hga : g a = 0) (hgb : g b = 0)
    (hH : ∀ t ∈ Icc a b, 0 ≤ H t) (hHa : H a = 0) (hHb : H b = 0)
    (hi : IntervalIntegrable F volume a b)
    (hprimitivea : ∀ z ∈ Icc a b, H z - H a = ∫ t in a..z, F t)
    (hprimitiveb : ∀ z ∈ Icc a b, H b - H z = ∫ t in z..b, F t)
    (hsign : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (0 < g t → F t < 0) ∧ (g t < 0 → 0 < F t)) : False := by
  have hslopea : gp a ≤ 0 := by
    by_contra hn
    obtain ⟨z, hz, hgz⟩ := positive_endpoint_slope_right hab (not_le.mp hn) g hgda hga
    have hprops := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo_right hz.2) hsign
    have hnegative : ∀ᵐ t ∂volume.restrict (Ioo a z), F t < 0 := by
      filter_upwards [hprops, ae_restrict_mem measurableSet_Ioo] with t ht htz
      exact ht.1 (hgz t htz)
    have hiz : IntervalIntegrable F volume a z := hi.mono_set (by
      rw [uIcc_of_le hz.1.le, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl hz.2)
    exact nonnegative_potential_excludes_negative_initial_density hz.1 H F
      (fun t ht => hH t ⟨ht.1, ht.2.trans hz.2⟩) hHa hiz
      (hprimitivea z ⟨hz.1.le, hz.2⟩) hnegative
  have hslopeb : gp b ≤ 0 := by
    by_contra hn
    obtain ⟨z, hz, hgz⟩ := positive_endpoint_slope_left hab (not_le.mp hn) g hgdb hgb
    have hprops := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo_left hz.1) hsign
    have hpositive : ∀ᵐ t ∂volume.restrict (Ioo z b), 0 < F t := by
      filter_upwards [hprops, ae_restrict_mem measurableSet_Ioo] with t ht htz
      exact ht.2 (hgz t htz)
    have hiz : IntervalIntegrable F volume z b := hi.mono_set (by
      rw [uIcc_of_le hz.2.le, uIcc_of_le hab.le]
      exact Icc_subset_Icc hz.1 le_rfl)
    have hneg := intervalIntegral_neg_of_negative_ae hz.2 (fun t => -F t) hiz.neg
      (hpositive.mono (fun t ht => neg_neg_of_pos ht))
    rw [intervalIntegral.integral_neg] at hneg
    have hprim := hprimitiveb z ⟨hz.1, hz.2.le⟩
    have hHz := hH z ⟨hz.1, hz.2.le⟩
    rw [hHb] at hprim
    linarith
  exact no_gap_of_affine_second_derivative hab hA g gp hgc hgpc hg hgp
    hga hgb hslopea hslopeb

theorem quantile_tendsto_of_linear_cdf
    {kappa v : ℝ} (hkappa : 0 < kappa) (hv : 0 < v)
    (U : ℕ → ℝ → ℝ) (q : ℕ → ℝ)
    (hmono : ∀ n, Monotone (U n))
    (hU : ∀ t : ℝ, 0 < t → Tendsto (fun n => U n t) atTop (𝓝 (kappa * t)))
    (hinverse : ∀ᶠ n in atTop, U n (q n) = v) :
    Tendsto q atTop (𝓝 (v / kappa)) := by
  have htarget : 0 < v / kappa := div_pos hv hkappa
  have hvalue : kappa * (v / kappa) = v := by field_simp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let t := (max 0 a + v / kappa) / 2
    have hmax : max 0 a < v / kappa := max_lt htarget ha
    have htpos : 0 < t := by dsimp [t]; linarith [le_max_left 0 a]
    have hat : a < t := by dsimp [t]; linarith [le_max_right 0 a]
    have htq : t < v / kappa := by dsimp [t]; linarith
    have hlt : kappa * t < v := by nlinarith
    filter_upwards [hinverse, (hU t htpos).eventually (eventually_lt_nhds hlt)] with n hn hnt
    have htqn : t ≤ q n := by
      by_contra hnot
      have horder := hmono n (not_le.mp hnot).le
      rw [hn] at horder
      linarith
    exact hat.trans_le htqn
  · intro a ha
    let t := (a + v / kappa) / 2
    have htpos : 0 < t := by dsimp [t]; linarith
    have hqt : v / kappa < t := by dsimp [t]; linarith
    have hta : t < a := by dsimp [t]; linarith
    have hgt : v < kappa * t := by nlinarith
    filter_upwards [hinverse, (hU t htpos).eventually (eventually_gt_nhds hgt)] with n hn hnt
    have hqnt : q n ≤ t := by
      by_contra hnot
      have horder := hmono n (not_le.mp hnot).le
      rw [hn] at horder
      linarith
    exact hqnt.trans_lt hta

theorem inverse_shell_bounds_eventually
    {kappa : ℝ} (hkappa : 0 < kappa) (q : ℕ → ℝ → ℝ)
    (hmono : ∀ n, MonotoneOn (q n) (Icc (1 / 2 : ℝ) 1))
    (hlower : Tendsto (fun n => q n (1 / 2)) atTop (𝓝 ((1 / 2 : ℝ) / kappa)))
    (hupper : Tendsto (fun n => q n 1) atTop (𝓝 (1 / kappa))) :
    ∀ᶠ n in atTop, ∀ v ∈ Icc (1 / 2 : ℝ) 1,
      1 / (4 * kappa) ≤ q n v ∧ q n v ≤ 2 / kappa := by
  have hlo : 1 / (4 * kappa) < (1 / 2 : ℝ) / kappa := by
    field_simp [hkappa.ne']
    linarith
  have hup : 1 / kappa < 2 / kappa := by
    exact div_lt_div_of_pos_right (by norm_num) hkappa
  filter_upwards [hlower.eventually (eventually_gt_nhds hlo),
    hupper.eventually (eventually_lt_nhds hup)] with n hnlo hnup v hv
  constructor
  · exact hnlo.le.trans (hmono n (by norm_num) hv hv.1)
  · exact (hmono n hv (by norm_num) hv.2).trans hnup.le

theorem linear_cdf_inverse_shell_bounds
    {kappa : ℝ} (hkappa : 0 < kappa)
    (U q : ℕ → ℝ → ℝ)
    (hUmono : ∀ n, Monotone (U n))
    (hqmono : ∀ n, MonotoneOn (q n) (Icc (1 / 2 : ℝ) 1))
    (hU : ∀ t : ℝ, 0 < t → Tendsto (fun n => U n t) atTop (𝓝 (kappa * t)))
    (hinverselo : ∀ᶠ n in atTop, U n (q n (1 / 2)) = (1 / 2 : ℝ))
    (hinverseup : ∀ᶠ n in atTop, U n (q n 1) = 1) :
    ∀ᶠ n in atTop, ∀ v ∈ Icc (1 / 2 : ℝ) 1,
      1 / (4 * kappa) ≤ q n v ∧ q n v ≤ 2 / kappa := by
  apply inverse_shell_bounds_eventually hkappa q hqmono
  · exact quantile_tendsto_of_linear_cdf hkappa (by norm_num)
      U (fun n => q n (1 / 2)) hUmono hU hinverselo
  · exact quantile_tendsto_of_linear_cdf hkappa (by norm_num)
      U (fun n => q n 1) hUmono hU hinverseup

theorem child_error_chain_growth
    {n : ℕ} (hn : 0 < (n : ℝ)) (N : ℕ) (delta : ℝ) (E : ℕ → ℝ)
    (hstep : ∀ j < N, (n : ℝ) ^ (delta / 4) * E j ≤ E (j + 1)) :
    ∀ j ≤ N, (n : ℝ) ^ ((j : ℝ) * delta / 4) * E 0 ≤ E j := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hjN : j < N := by omega
    have hgrowth := mul_le_mul_of_nonneg_left (ih (by omega))
      (Real.rpow_nonneg hn.le (delta / 4))
    have ht := hgrowth.trans (hstep j hjN)
    convert ht using 1
    rw [← mul_assoc, ← Real.rpow_add hn]
    congr 1
    congr 1
    push_cast
    ring

theorem eventually_no_bounded_child_error_chain
    (N : ℕ) (m delta c C : ℝ) (hc : 0 < c)
    (hdepth : (1 / 3 : ℝ) - 2 * m < (N : ℝ) * delta / 4) :
    ∀ᶠ n : ℕ in atTop, ∀ E : ℕ → ℝ,
      c * (n : ℝ) ^ (-(5 : ℝ) / 6 + 2 * m) ≤ E 0 →
      E N ≤ C * (n : ℝ) ^ (-(1 : ℝ) / 2) →
      (∀ j < N, (n : ℝ) ^ (delta / 4) * E j ≤ E (j + 1)) → False := by
  have hp := eventually_coefficient_rpow_le (c := C) (d := c / 2)
    (q := -(1 : ℝ) / 2)
    (r := -(5 : ℝ) / 6 + 2 * m + (N : ℝ) * delta / 4)
    (by positivity) (by linarith)
  filter_upwards [hp, eventually_gt_atTop (0 : ℕ)] with n hn hnpos E h0 hN hstep
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hgrow := child_error_chain_growth hnreal N delta E hstep N le_rfl
  have hscaled := mul_le_mul_of_nonneg_left h0
    (Real.rpow_nonneg hnreal.le ((N : ℝ) * delta / 4))
  have hmain : c * (n : ℝ) ^ (-(5 : ℝ) / 6 + 2 * m + (N : ℝ) * delta / 4) ≤ E N := by
    calc
      c * (n : ℝ) ^ (-(5 : ℝ) / 6 + 2 * m + (N : ℝ) * delta / 4) =
        (n : ℝ) ^ ((N : ℝ) * delta / 4) *
          (c * (n : ℝ) ^ (-(5 : ℝ) / 6 + 2 * m)) := by
        rw [Real.rpow_add hnreal]
        ring
      _ ≤ (n : ℝ) ^ ((N : ℝ) * delta / 4) * E 0 := hscaled
      _ ≤ E N := hgrow
  have hpos : 0 < c * (n : ℝ) ^
      (-(5 : ℝ) / 6 + 2 * m + (N : ℝ) * delta / 4) :=
    mul_pos hc (Real.rpow_pos_of_pos hnreal _)
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
