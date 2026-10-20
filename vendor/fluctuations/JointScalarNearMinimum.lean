module

public import ScalarMacroStability
public import SampledQuantileScalarBridge
public import MacroQuantileCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Measure.Subtype.measureSpace

theorem intervalIntegrable_mul_bounded {f g : ℝ → ℝ} {A B : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hfB : ∀ u ∈ Icc (0:ℝ) 1, |f u| ≤ A)
    (hgB : ∀ u ∈ Icc (0:ℝ) 1, |g u| ≤ B) :
    IntervalIntegrable (fun u => f u*g u) volume 0 1 := by
  apply (intervalIntegrable_const (c := A*B)).mono_fun
    (hf.aestronglyMeasurable_restrict_uIoc.mul hg.aestronglyMeasurable_restrict_uIoc)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  have hu' : u ∈ Icc (0:ℝ) 1 := by
    rw [uIoc_of_le zero_le_one] at hu
    exact ⟨hu.1.le,hu.2⟩
  simpa only [Pi.mul_apply,Real.norm_eq_abs,abs_mul] using
    (mul_le_mul (hfB u hu') (hgB u hu') (abs_nonneg _) (by
      exact (abs_nonneg _).trans (hfB u hu'))).trans (le_abs_self (A*B))

theorem unit_quantile_square_difference_integrable (r z : ℝ → ℝ)
    (hr : MonotoneOn r (Icc (0:ℝ) 1)) (hz : MonotoneOn z (Icc (0:ℝ) 1))
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1)
    (hzb : ∀ u ∈ Icc (0:ℝ) 1, z u ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun u => (r u-z u)^2) volume 0 1 := by
  have hi : IntervalIntegrable (fun u => r u-z u) volume 0 1 :=
    (show MonotoneOn r (uIcc (0:ℝ) 1) by simpa using hr).intervalIntegrable.sub
    (show MonotoneOn z (uIcc (0:ℝ) 1) by simpa using hz).intervalIntegrable
  have hb : ∀ u ∈ Icc (0:ℝ) 1, |r u-z u| ≤ 1 := by
    intro u hu
    exact abs_le.mpr ⟨by linarith [(hrb u hu).1,(hzb u hu).2],
      by linarith [(hrb u hu).2,(hzb u hu).1]⟩
  simpa only [pow_two] using intervalIntegrable_mul_bounded hi hi hb hb

theorem abs_le_young_square {x a : ℝ} (ha : 0 < a) :
    |x| ≤ a+x^2/(4*a) := by
  rw [← sub_le_iff_le_add']
  apply (le_div_iff₀ (by positivity : 0 < 4*a)).mpr
  have hs := sq_nonneg (|x|-2*a)
  nlinarith [sq_abs x]

theorem unit_quantile_l1_le_square (r z : ℝ → ℝ)
    (hr : MonotoneOn r (Icc (0:ℝ) 1)) (hz : MonotoneOn z (Icc (0:ℝ) 1))
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1)
    (hzb : ∀ u ∈ Icc (0:ℝ) 1, z u ∈ Icc (0:ℝ) 1)
    {a : ℝ} (ha : 0 < a) :
    (∫u in (0:ℝ)..1,|r u-z u|) ≤ a+(∫u in (0:ℝ)..1,(r u-z u)^2)/(4*a) := by
  have hir : IntervalIntegrable r volume 0 1 :=
    (show MonotoneOn r (uIcc (0:ℝ) 1) by simpa using hr).intervalIntegrable
  have hiz : IntervalIntegrable z volume 0 1 :=
    (show MonotoneOn z (uIcc (0:ℝ) 1) by simpa using hz).intervalIntegrable
  have his := unit_quantile_square_difference_integrable r z hr hz hrb hzb
  have h := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (hir.sub hiz).abs
    ((intervalIntegrable_const (c := a)).add (his.div_const (4*a)))
    (fun u _ => abs_le_young_square (x := r u-z u) ha)
  simpa only [intervalIntegral.integral_add intervalIntegrable_const (his.div_const (4*a)),
    intervalIntegral.integral_const,sub_zero,one_smul,intervalIntegral.integral_div] using h

theorem quantile_cdf_lower_of_value_le (q : ℝ → ℝ)
    (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hqb : ∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1)
    {u d : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hqd : q u ≤ d) :
    u ≤ (quantileMassProfile q hqb).val d := by
  rw [quantileMassProfile_cdf q hq hqb]
  rw [← uniformOrderMass_atMost hu]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro v hv
  exact (hq v.property hu hv).trans hqd

theorem scalar_near_quantiles_fixed_band {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β:ℝ)^2) {a : ℝ} (ha : 0 < a) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ (n : ℕ), 0 < n → ∀ q : ℝ → ℝ,
      MonotoneOn q (Icc (0:ℝ) 1) →
      (∀ u ∈ Icc (0:ℝ) 1, q u ∈ Icc (0:ℝ) 1) →
      physicalScalarQuantileValue n ((β:ℝ)^2) q ≤ normalizedScalarParisiReference β+ε →
      ∀ u ∈ Ioo (0:ℝ) 1, a ≤ u → c*u ≤ q u ∧ q u ≤ C*u := by
  obtain ⟨d,ε,hd,hε,hmass⟩ := scalar_near_minimizers_uniform_origin hβ hT ha
  refine ⟨d,1/a,ε,hd,one_div_pos.mpr ha,hε,?_⟩
  intro n hn q hq hqb hv u hu hau
  have hv' : scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ))
      (quantileMassProfile q hqb) ≤ normalizedScalarParisiReference β+ε := by
    rwa [scalar_physical_quantile_value n hn _ q hq hqb]
  have hs := hmass (quantileMassProfile q hqb) (quantileMassProfile_mem q hqb) hv'
  have hqd : d < q u := by
    by_contra h
    have hl := quantile_cdf_lower_of_value_le q hq hqb ⟨hu.1.le,hu.2.le⟩ (not_lt.mp h)
    linarith
  refine ⟨(mul_le_of_le_one_right hd.le hu.2.le).trans hqd.le,?_⟩
  have hone : (1:ℝ) ≤ 1/a*u := by
    rw [div_mul_eq_mul_div,one_mul,le_div_iff₀ ha]
    simpa only [one_mul] using hau
  exact (hqb u ⟨hu.1.le,hu.2.le⟩).2.trans hone

theorem joint_quantile_coercivity {β : ℝ≥0} (hβ : 0 < β)
    (n : ℕ) (hn : 0 < n) {c : ℝ} (hc : 0 < c) (e r z : ℝ → ℝ)
    (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c ((β:ℝ)^2-c))
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1)) (hz : MonotoneOn z (Icc (0:ℝ) 1))
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1)
    (hzb : ∀ u ∈ Icc (0:ℝ) 1, z u ∈ Icc (0:ℝ) 1) :
    let T := (β:ℝ)^2
    physicalScalarQuantileValue n T (mixedQuantile T e r z) +
      c^2/(4*T)*(∫u in (0:ℝ)..1,(r u-z u)^2) ≤ physicalJointQuantileValue n T e r z ∧
    normalizedScalarParisiReference β ≤
      physicalScalarQuantileValue n T (mixedQuantile T e r z) := by
  dsimp only
  let T := (β:ℝ)^2
  have hT : 0 < T := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  have heb' (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : e u ∈ Icc (0:ℝ) T :=
    ⟨hc.le.trans (heb u hu).1,(heb u hu).2.trans (sub_le_self T hc.le)⟩
  have hbn (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : 0 ≤ T-e u := sub_nonneg.mpr (heb' u hu).2
  have hbm : MonotoneOn (fun u => T-e u) (Icc (0:ℝ) 1) :=
    fun _ hu _ hv huv => sub_le_sub_left (he hu hv huv) T
  have hq := mixedQuantile_monotoneOn hT.le e r z her hbm hz hbn (fun u hu => (hzb u hu).1)
  have hqb (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : mixedQuantile T e r z u ∈ Icc (0:ℝ) 1 :=
    mixedQuantile_unit_bounds hT (heb' u hu) (hrb u hu) (hzb u hu)
  have hiq : IntervalIntegrable (fun u => mixedQuantile T e r z u^2) volume 0 1 := by
    simpa only [sub_zero] using unit_quantile_square_difference_integrable
      (mixedQuantile T e r z) (fun _ => 0) hq (fun _ _ _ _ _ => le_rfl) hqb
      (fun _ _ => ⟨le_rfl,zero_le_one⟩)
  have hie : IntervalIntegrable e volume 0 1 :=
    (show AntitoneOn e (uIcc (0:ℝ) 1) by simpa using he).intervalIntegrable
  have hib : IntervalIntegrable (fun u => T-e u) volume 0 1 := intervalIntegrable_const.sub hie
  have heB (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : |e u| ≤ T := by
    rw [abs_of_nonneg (heb' u hu).1]; exact (heb' u hu).2
  have hbB (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : |T-e u| ≤ T := by
    rw [abs_of_nonneg (hbn u hu)]; exact sub_le_self _ (heb' u hu).1
  have hic : IntervalIntegrable (fun u => e u*(T-e u)/T) volume 0 1 :=
    (intervalIntegrable_mul_bounded hie hib heB hbB).div_const T
  have hcB (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : |e u*(T-e u)/T| ≤ T := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (heb' u hu).1 (hbn u hu)) hT.le)]
    apply (div_le_iff₀ hT).mpr
    nlinarith [(heb' u hu).1,(heb' u hu).2,sq_nonneg (e u)]
  have hid := unit_quantile_square_difference_integrable r z hr hz hrb hzb
  have hdB (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : |(r u-z u)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [(hrb u hu).1,(hrb u hu).2,(hzb u hu).1,(hzb u hu).2,
      mul_nonneg (hrb u hu).1 (hzb u hu).1]
  have hiw := intervalIntegrable_mul_bounded hic hid hcB hdB
  refine ⟨physical_joint_coercive n hT hc.le e r z (fun u hu => (heb u hu).1)
    (fun u hu => by have := (heb u hu).2; dsimp [T] at *; linarith) hiq hiw hid,?_⟩
  rw [← scalar_physical_quantile_value n hn hT _ hq hqb]
  exact normalizedScalarParisiReference_le_value hβ _

theorem joint_near_minimum_radius_value {β : ℝ≥0} (hβ : 0 < β)
    (n : ℕ) (hn : 0 < n) {c a E : ℝ} (hc : 0 < c) (ha : 0 < a)
    (e r z : ℝ → ℝ) (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c ((β:ℝ)^2-c))
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1)) (hz : MonotoneOn z (Icc (0:ℝ) 1))
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1)
    (hzb : ∀ u ∈ Icc (0:ℝ) 1, z u ∈ Icc (0:ℝ) 1)
    (hv : physicalJointQuantileValue n ((β:ℝ)^2) e r z ≤ normalizedScalarParisiReference β+E) :
    physicalScalarQuantileValue n ((β:ℝ)^2) r ≤ normalizedScalarParisiReference β+
      E+(β:ℝ)^2*(a+((4*(β:ℝ)^2*E)/c^2)/(4*a)) := by
  let T := (β:ℝ)^2
  have hT : 0 < T := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  let q := mixedQuantile T e r z
  obtain ⟨hco,hlo⟩ := joint_quantile_coercivity hβ n hn hc e r z he heb her hr hz hrb hzb
  have heb' (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : e u ∈ Icc (0:ℝ) T :=
    ⟨hc.le.trans (heb u hu).1,(heb u hu).2.trans (sub_le_self T hc.le)⟩
  have hq : MonotoneOn q (Icc (0:ℝ) 1) := mixedQuantile_monotoneOn hT.le e r z her
    (fun _ hu _ hv huv => sub_le_sub_left (he hu hv huv) T) hz
    (fun u hu => sub_nonneg.mpr (heb' u hu).2) (fun u hu => (hzb u hu).1)
  have hqb (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : q u ∈ Icc (0:ℝ) 1 :=
    mixedQuantile_unit_bounds hT (heb' u hu) (hrb u hu) (hzb u hu)
  have hir : IntervalIntegrable r volume 0 1 :=
    (show MonotoneOn r (uIcc (0:ℝ) 1) by simpa using hr).intervalIntegrable
  have hiz : IntervalIntegrable z volume 0 1 :=
    (show MonotoneOn z (uIcc (0:ℝ) 1) by simpa using hz).intervalIntegrable
  have hiq : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by simpa using hq).intervalIntegrable
  have hdist : (∫u in (0:ℝ)..1,|r u-q u|) ≤ ∫u in (0:ℝ)..1,|r u-z u| := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (hir.sub hiq).abs (hir.sub hiz).abs
    intro u hu
    simpa only [q,mixedQuantile,abs_sub_comm] using
      mixedQuantile_radius_distance_le hT (heb' u ⟨hu.1.le,hu.2.le⟩)
  have hL := unit_quantile_l1_le_square r z hr hz hrb hzb ha
  have hI : (∫u in (0:ℝ)..1,(r u-z u)^2) ≤ 4*T*E/c^2 := by
    have hc2 : 0 < c^2 := sq_pos_of_pos hc
    have hcoef : 0 < c^2/(4*T) := by positivity
    have h := (le_div_iff₀ hcoef).mpr (by linarith :
      (∫u in (0:ℝ)..1,(r u-z u)^2)*(c^2/(4*T)) ≤ E)
    convert h using 1
    field_simp
  have hnon : 0 ≤ ∫u in (0:ℝ)..1,(r u-z u)^2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
  have hqv : physicalScalarQuantileValue n T q ≤ physicalJointQuantileValue n T e r z := by
    have hcoeff : 0 ≤ c^2/(4*T) := by positivity
    have hprod := mul_nonneg hcoeff hnon
    linarith
  have hp := physical_scalar_quantile_value_l1 n hn hT.le r q hr hq hrb hqb
  have hpr : physicalScalarQuantileValue n T r-physicalScalarQuantileValue n T q ≤
      T*(a+(4*T*E/c^2)/(4*a)) := by
    exact (le_abs_self _).trans (hp.trans (mul_le_mul_of_nonneg_left
      (hdist.trans (hL.trans (add_le_add_right (div_le_div_of_nonneg_right hI
        (show (0:ℝ) ≤ 4*a by positivity)) a))) hT.le))
  dsimp [T,q] at *
  linarith

theorem joint_near_minimizers_fixed_band {β : ℝ≥0} (hβ : 0 < β)
    (hT1 : 1 < (β:ℝ)^2) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∃ cR CR ε : ℝ, 0 < cR ∧ 0 < CR ∧ 0 < ε ∧
      ∀ (n : ℕ), 0 < n → ∀ e r z : ℝ → ℝ,
      AntitoneOn e (Icc (0:ℝ) 1) →
      (∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c ((β:ℝ)^2-c)) →
      MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1) →
      MonotoneOn r (Icc (0:ℝ) 1) → MonotoneOn z (Icc (0:ℝ) 1) →
      (∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1) →
      (∀ u ∈ Icc (0:ℝ) 1, z u ∈ Icc (0:ℝ) 1) →
      physicalJointQuantileValue n ((β:ℝ)^2) e r z ≤ normalizedScalarParisiReference β+ε →
      ∀ u ∈ Ioo (0:ℝ) 1, x ≤ u → cR*u ≤ r u ∧ r u ≤ CR*u := by
  obtain ⟨cR,CR,ρ,hcR,hCR,hρ,hband⟩ := scalar_near_quantiles_fixed_band hβ hT1 hx
  let T := (β:ℝ)^2
  have hT : 0 < T := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  let a := ρ/(4*T)
  have ha : 0 < a := by dsimp [a]; positivity
  let ε := min (ρ/4) (ρ*c^2*a/(4*T^2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨cR,CR,ε,hcR,hCR,hε,?_⟩
  intro n hn e r z he heb her hr hz hrb hzb hv
  apply hband n hn r hr hrb
  have hvalue := joint_near_minimum_radius_value hβ n hn hc ha e r z he heb her hr hz hrb hzb hv
  have hε1 : ε ≤ ρ/4 := min_le_left _ _
  have hε2 : ε ≤ ρ*c^2*a/(4*T^2) := min_le_right _ _
  have hε2' : ε*(4*T^2) ≤ ρ*c^2*a := (le_div_iff₀ (by positivity)).mp hε2
  have hterm : T*((4*T*ε/c^2)/(4*a)) ≤ ρ/4 := by
    have heq : T*((4*T*ε/c^2)/(4*a)) = T^2*ε/(c^2*a) := by
      field_simp
    rw [heq]
    apply (div_le_iff₀ (by positivity : 0 < c^2*a)).mpr
    nlinarith
  have hTa : T*a=ρ/4 := by dsimp [a]; field_simp
  have hgap : ε+T*(a+((4*T*ε)/c^2)/(4*a)) ≤ ρ := by
    rw [mul_add,hTa]
    linarith
  change physicalScalarQuantileValue n T r ≤ normalizedScalarParisiReference β+ρ
  change physicalScalarQuantileValue n T r ≤ normalizedScalarParisiReference β+
    ε+T*(a+((4*T*ε)/c^2)/(4*a)) at hvalue
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
