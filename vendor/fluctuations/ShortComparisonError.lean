module

public import FullMassComparisonMinimum
public import CompensatedPressureStability
public import SKFluctuationsOAI.Probability.SKFluctuations.ComparisonMinimumMassCenter

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem pathCompensatedPressure_cost_le_strength
    (n : ℕ) (hn : 0 < n) (b h e r : ℝ → ℝ) {lam : ℝ}
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (helam : ∀ u ∈ Icc (0 : ℝ) 1, e u ≤ lam)
    (hr : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0)
    (hbc : MonotoneOn (fun u => b u - e u) (Icc (0 : ℝ) 1))
    (hhc : MonotoneOn (fun u => h u + e u * r u) (Icc (0 : ℝ) 1))
    (hbc0 : 0 ≤ b 0 - e 0) (hhc0 : 0 ≤ h 0 + e 0 * r 0)
    (hp : MonotoneOn (fun u => e u * (r u) ^ 2) (Icc (0 : ℝ) 1))
    (x : OrderedFeatureIndex n → ℝ) :
    0 ≤ pathCompensatedPressure n b h e r x - realOrderedSKPathPressure n b h x ∧
      pathCompensatedPressure n b h e r x - realOrderedSKPathPressure n b h x ≤ lam := by
  have hlam : 0 ≤ lam := (he 0 (by norm_num)).trans (helam 0 (by norm_num))
  have her : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u * r u ∧ e u * r u ≤ lam := by
    intro u hu
    exact ⟨mul_nonneg (he u hu) (hr u hu).1,
      (mul_le_mul_of_nonneg_left (hr u hu).2 (he u hu)).trans (by simpa using helam u hu)⟩
  have hpenalty := intervalIntegral_abs_le_unit_bound
    (f := fun u => e u * (r u) ^ 2) (C := lam) (fun u hu => by
      rw [abs_of_nonneg (mul_nonneg (he u hu) (sq_nonneg _))]
      have hsq : (r u)^2 ≤ 1 := by nlinarith [(hr u hu).1, (hr u hu).2]
      exact (mul_le_mul_of_nonneg_left hsq (he u hu)).trans (by simpa using helam u hu))
  have hdist := realOrderedSKPathPressure_uniform_comparison n hn
    (fun u => b u - e u) (fun u => h u + e u * r u) b h
    hbc hhc hb hh hbc0 hhc0 hb0 hh0
    (fun u hu => by
      simpa only [sub_sub_cancel_left, abs_neg, abs_of_nonneg (he u hu)]
        using (helam u hu))
    (fun u hu => by
      simpa only [add_sub_cancel_left, abs_of_nonneg (her u hu).1]
        using (her u hu).2) x
  constructor
  · exact sub_nonneg.mpr (pathCompensatedPressure_lower n hn b h e r
      he hb hh hb0 hh0 hbc hhc hbc0 hhc0 hp x)
  · unfold pathCompensatedPressure
    have hpressure := (le_abs_self _).trans hdist
    have hint := (le_abs_self _).trans hpenalty
    linarith

theorem pathCompensatedPressure_initial_strength
    (n : ℕ) (hn : 0 < n) (b h e r : ℝ → ℝ) {lam error : ℝ}
    (he : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ e u)
    (helam : ∀ u ∈ Icc (0 : ℝ) 1, e u ≤ lam)
    (hr : ∀ u ∈ Icc (0 : ℝ) 1, r u ∈ Icc (0 : ℝ) 1)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0)
    (hbc : MonotoneOn (fun u => b u - e u) (Icc (0 : ℝ) 1))
    (hhc : MonotoneOn (fun u => h u + e u * r u) (Icc (0 : ℝ) 1))
    (hbc0 : 0 ≤ b 0 - e 0) (hhc0 : 0 ≤ h 0 + e 0 * r 0)
    (hp : MonotoneOn (fun u => e u * (r u) ^ 2) (Icc (0 : ℝ) 1))
    (hlam : lam ≤ error) (x : OrderedFeatureIndex n → ℝ) :
    pathCompensatedPressure n b h e r x ≤ realOrderedSKPathPressure n b h x + error := by
  have hc := (pathCompensatedPressure_cost_le_strength n hn b h e r
    he helam hr hb hh hb0 hh0 hbc hhc hbc0 hhc0 hp x).2
  linarith

theorem constrainedQuantile_gap_lower {r0 u0 capFloor : ℝ} {k M : ℝ → ℝ}
    (hr : r0 ≤ 1) (hc : 0 < capFloor) (hk : ContinuousOn k (Icc r0 1))
    (hkc : ∀ t ∈ Icc r0 1, capFloor ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1) (hMpos : 0 < M 1)
    (alpha : inverseIntegralConstraints r0 u0 k M)
    (u v : Icc u0 1) (huv : u ≤ v) :
    (v.val-u.val) / M 1 ≤
      (constrainedQuantile hr hc hk hkc hm hM alpha v).val-
        (constrainedQuantile hr hc hk hkc hm hM alpha u).val := by
  let ru := constrainedQuantile hr hc hk hkc hm hM alpha u
  let rv := constrainedQuantile hr hc hk hkc hm hM alpha v
  have hruv : ru.val ≤ rv.val := (inverseConstraintOrderIso hr hc hk hkc hm hM alpha).symm.monotone huv
  have hd := (inverseIntegralConstraints_lipschitz hm hM alpha.property).dist_le_mul
    ru.val ru.property rv.val rv.property
  change dist (alpha.val.val ru) (alpha.val.val rv) ≤ M 1*dist ru.val rv.val at hd
  rw [constrainedQuantile_spec, constrainedQuantile_spec] at hd
  simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show u.val ≤ v.val from huv)),
    abs_of_nonpos (sub_nonpos.mpr hruv), neg_sub] at hd
  exact (div_le_iff₀ hMpos).mpr (by simpa only [mul_comm] using hd)

theorem constrainedChangedField_mass_gap {r0 u0 capFloor : ℝ} {k M : ℝ → ℝ}
    (hr : r0 ≤ 1) (hu : u0 ≤ 1) (hc : 0 < capFloor)
    (hk : ContinuousOn k (Icc r0 1)) (hkc : ∀ t ∈ Icc r0 1, capFloor ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1) (hMpos : 0 < M 1)
    (alpha : inverseIntegralConstraints r0 u0 k M)
    (e h0 : ℝ → ℝ) (hec : Continuous e) (hbare : MonotoneOn h0 (Icc u0 1))
    (u v : Icc u0 1) (huv : u ≤ v) {kappa emin : ℝ}
    (hkappa : 0 ≤ kappa) (hemin : 0 ≤ emin)
    (hebound : emin ≤ e (constrainedQuantile hr hc hk hkc hm hM alpha v))
    (hediff : ∀ t ∈ Icc
      (constrainedQuantile hr hc hk hkc hm hM alpha u).val
      (constrainedQuantile hr hc hk hkc hm hM alpha v).val, DifferentiableAt ℝ e t)
    (hepos : ∀ t ∈ Icc
      (constrainedQuantile hr hc hk hkc hm hM alpha u).val
      (constrainedQuantile hr hc hk hkc hm hM alpha v).val, 0 < e t)
    (heanti : AntitoneOn e (Icc
      (constrainedQuantile hr hc hk hkc hm hM alpha u).val
      (constrainedQuantile hr hc hk hkc hm hM alpha v).val))
    (hslope : ∀ t ∈ Icc
      (constrainedQuantile hr hc hk hkc hm hM alpha u).val
      (constrainedQuantile hr hc hk hkc hm hM alpha v).val, kappa ≤ 1-comparisonLogSlope e t) :
    let h := fun z => h0 z+omittedExtension hu
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => e r*r)
        (hec.mul continuous_id) alpha) z
    kappa*emin*((v.val-u.val)/M 1) ≤ h v.val-h u.val := by
  dsimp only
  let ru := constrainedQuantile hr hc hk hkc hm hM alpha u
  let rv := constrainedQuantile hr hc hk hkc hm hM alpha v
  have hruv : ru.val ≤ rv.val := (inverseConstraintOrderIso hr hc hk hkc hm hM alpha).symm.monotone huv
  have hrad := changedField_radius_growth hr hu hc hk hkc hm hM alpha e h0 hec
    ru.property rv.property hruv hbare hediff hepos heanti hkappa hslope
  dsimp only at hrad
  rw [constrainedQuantile_spec, constrainedQuantile_spec] at hrad
  have hgap := constrainedQuantile_gap_lower hr hc hk hkc hm hM hMpos alpha u v huv
  have h0gap : 0 ≤ (v.val-u.val)/M 1 := div_nonneg (sub_nonneg.mpr (show u.val ≤ v.val from huv)) hMpos.le
  calc
    kappa*emin*((v.val-u.val)/M 1) ≤ kappa*emin*(rv.val-ru.val) :=
      mul_le_mul_of_nonneg_left hgap (mul_nonneg hkappa hemin)
    _ ≤ kappa*e rv*(rv.val-ru.val) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hebound hkappa) (sub_nonneg.mpr hruv)
    _ ≤ _ := hrad

end OAI.SKFluctuations
