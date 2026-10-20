module

public import ForwardQuantileFeasibility

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def forwardOmittedOrderIso {r0 u0 : ℝ} (hr : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Icc u0 1)) (hs : StrictMonoOn q (Icc u0 1))
    (hb : MapsTo q (Icc u0 1) (Icc r0 1)) (h0 : q u0 = r0) (h1 : q 1 = 1) :
    Icc u0 1 ≃o Icc r0 1 :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofStrictMono (fun u : Icc u0 1 => (⟨q u, hb u.property⟩ : Icc r0 1))
      (fun u v huv => hs u.property v.property huv)) (by
      intro v
      have hv : v.val ∈ Icc (q u0) (q 1) := by simpa only [h0, h1] using v.property
      obtain ⟨u, hum, he⟩ := intermediate_value_Icc hu.2 hq hv
      exact ⟨⟨u, hum⟩, Subtype.ext he⟩)

def forwardOmittedInverseProfile {r0 u0 : ℝ} (hr : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
    (q : ℝ → ℝ) (hq : ContinuousOn q (Icc u0 1)) (hs : StrictMonoOn q (Icc u0 1))
    (hb : MapsTo q (Icc u0 1) (Icc r0 1)) (h0 : q u0 = r0) (h1 : q 1 = 1) :
    boundedMassProfiles :=
  ⟨fun r => ((forwardOmittedOrderIso hr hu q hq hs hb h0 h1).symm (projIcc r0 1 hr r)).val, by
    constructor
    · intro r
      have hm := ((forwardOmittedOrderIso hr hu q hq hs hb h0 h1).symm (projIcc r0 1 hr r)).property
      exact ⟨hu.1.trans hm.1, hm.2⟩
    · intro r s hrs
      exact (forwardOmittedOrderIso hr hu q hq hs hb h0 h1).symm.monotone (monotone_projIcc hr hrs)⟩

section
variable {r0 u0 : ℝ} (hr : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1) {q : ℝ → ℝ}
variable (hq : ContinuousOn q (Icc u0 1)) (hs : StrictMonoOn q (Icc u0 1))
variable (hb : MapsTo q (Icc u0 1) (Icc r0 1)) (h0 : q u0 = r0) (h1 : q 1 = 1)

theorem forwardOmittedInverseProfile_range (r : ℝ) :
    (forwardOmittedInverseProfile hr hu q hq hs hb h0 h1).val r ∈ Icc u0 1 :=
  ((forwardOmittedOrderIso hr hu q hq hs hb h0 h1).symm (projIcc r0 1 hr r)).property

theorem forwardOmittedInverseProfile_spec {r : ℝ} (hrm : r ∈ Icc r0 1) :
    q ((forwardOmittedInverseProfile hr hu q hq hs hb h0 h1).val r) = r := by
  have he := congrArg Subtype.val ((forwardOmittedOrderIso hr hu q hq hs hb h0 h1).apply_symm_apply
    (projIcc r0 1 hr r))
  change q ((forwardOmittedOrderIso hr hu q hq hs hb h0 h1).symm (projIcc r0 1 hr r)).val =
    (projIcc r0 1 hr r).val at he
  simpa only [forwardOmittedInverseProfile, projIcc_of_mem hr hrm] using he

theorem forwardOmittedInverseProfile_inverse {u : ℝ} (hum : u ∈ Icc u0 1) :
    (forwardOmittedInverseProfile hr hu q hq hs hb h0 h1).val (q u) = u := by
  apply hs.injOn (forwardOmittedInverseProfile_range hr hu hq hs hb h0 h1 (q u)) hum
  exact forwardOmittedInverseProfile_spec hr hu hq hs hb h0 h1 (hb hum)

theorem forwardOmittedInverseProfile_left :
    (forwardOmittedInverseProfile hr hu q hq hs hb h0 h1).val r0 = u0 := by
  simpa only [h0] using forwardOmittedInverseProfile_inverse hr hu hq hs hb h0 h1
    (u := u0) ⟨le_rfl, hu.2⟩

theorem forwardOmittedInverseProfile_one :
    (forwardOmittedInverseProfile hr hu q hq hs hb h0 h1).val 1 = 1 := by
  simpa only [h1] using forwardOmittedInverseProfile_inverse hr hu hq hs hb h0 h1
    (u := 1) ⟨hu.2, le_rfl⟩

theorem forwardOmittedInverseProfile_lipschitz {lower : ℝ} (hlower : 0 < lower)
    (hgap : ∀ u ∈ Icc u0 1, ∀ v ∈ Icc u0 1, u ≤ v → lower*(v-u) ≤ q v-q u) :
    LipschitzOnWith ⟨lower⁻¹, inv_nonneg.mpr hlower.le⟩
      (forwardOmittedInverseProfile hr hu q hq hs hb h0 h1).val (Icc r0 1) := by
  let a := forwardOmittedInverseProfile hr hu q hq hs hb h0 h1
  have hbound {x y : ℝ} (hx : x ∈ Icc r0 1) (hy : y ∈ Icc r0 1) (hxy : x ≤ y) :
      a.val y-a.val x ≤ lower⁻¹*(y-x) := by
    have hh := hgap (a.val x) (forwardOmittedInverseProfile_range hr hu hq hs hb h0 h1 x)
      (a.val y) (forwardOmittedInverseProfile_range hr hu hq hs hb h0 h1 y) (a.property.2 hxy)
    rw [forwardOmittedInverseProfile_spec hr hu hq hs hb h0 h1 hx,
      forwardOmittedInverseProfile_spec hr hu hq hs hb h0 h1 hy] at hh
    exact (le_inv_mul_iff₀ hlower).mpr hh
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change |a.val x-a.val y| ≤ lower⁻¹*|x-y|
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (a.property.2 hxy)), neg_sub] using hbound hx hy hxy
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (a.property.2 hyx))] using hbound hy hx hyx

theorem forwardOmittedInverseProfile_feasible {C : ℝ≥0}
    (hql : LipschitzOnWith C q (Icc u0 1)) {lower : ℝ} (hlower : 0 < lower)
    (hgap : ∀ u ∈ Icc u0 1, ∀ v ∈ Icc u0 1, u ≤ v → lower*(v-u) ≤ q v-q u)
    {k M : ℝ → ℝ} (hk : ContinuousOn k (Icc r0 1)) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM1 : 0 ≤ M 1)
    (hkp : ∀ r ∈ Icc r0 1, 0 < k r) (hMp : ∀ u ∈ Icc u0 1, 0 < M u)
    (hder : ∀ᵐ u ∂volume, u ∈ Icc u0 1 →
      (M u)⁻¹ ≤ deriv q u ∧ deriv q u ≤ (k (q u))⁻¹) :
    forwardOmittedInverseProfile hr hu q hq hs hb h0 h1 ∈ inverseIntegralConstraints r0 u0 k M := by
  let a := forwardOmittedInverseProfile hr hu q hq hs hb h0 h1
  have har (r : ℝ) : a.val r ∈ Icc u0 1 := forwardOmittedInverseProfile_range hr hu hq hs hb h0 h1 r
  have hal := forwardOmittedInverseProfile_lipschitz hr hu hq hs hb h0 h1 hlower hgap
  rw [← inverseDifferentialConstraints_eq r0 u0 hr k M hk hM hm hM1]
  refine ⟨forwardOmittedInverseProfile_left hr hu hq hs hb h0 h1,
    forwardOmittedInverseProfile_one hr hu hq hs hb h0 h1,
    ⟨lower⁻¹, inv_nonneg.mpr hlower.le⟩, hal, ?_⟩
  have hac : AbsolutelyContinuousOnInterval q u0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le hu.2] using hql
  have hdiff : ∀ᵐ u ∂volume, u ∈ Icc u0 1 → DifferentiableAt ℝ q u := by
    simpa only [uIcc_of_le hu.2] using hac.ae_differentiableAt
  have hboth : ∀ᵐ u ∂volume, u ∈ Icc u0 1 → DifferentiableAt ℝ q u ∧
      (M u)⁻¹ ≤ deriv q u ∧ deriv q u ≤ (k (q u))⁻¹ := by
    filter_upwards [hdiff, hder] with u hd he hum
    exact ⟨hd hum, he hum⟩
  have hpull := ae_inverse_pullback hql (fun r (_ : r ∈ Icc r0 1) => har r)
    (fun r hrm => forwardOmittedInverseProfile_spec hr hu hq hs hb h0 h1 hrm) hboth
  filter_upwards [hpull, volume.ae_ne r0, volume.ae_ne (1 : ℝ)] with r hp hr0 hr1 hrm
  have hri : r ∈ Ioo r0 1 :=
    ⟨lt_of_le_of_ne hrm.1 (Ne.symm hr0), lt_of_le_of_ne hrm.2 hr1⟩
  have haq : q (a.val r) = r := forwardOmittedInverseProfile_spec hr hu hq hs hb h0 h1 hrm
  have hbounds := (hp hrm).2
  have hmp := hMp (a.val r) (har r)
  have hkp' := hkp r hrm
  have hdp : 0 < deriv q (a.val r) := lt_of_lt_of_le (inv_pos.mpr hmp) hbounds.1
  have haCont : ContinuousAt a.val r := hal.continuousOn.continuousAt (Icc_mem_nhds hri.1 hri.2)
  have hinv : ∀ᶠ y in 𝓝 r, q (a.val y) = y := by
    filter_upwards [Icc_mem_nhds hri.1 hri.2] with y hy
    exact forwardOmittedInverseProfile_spec hr hu hq hs hb h0 h1 hy
  have hd := ((hp hrm).1.hasDerivAt.of_local_left_inverse haCont hdp.ne' hinv).deriv
  change deriv a.val r = (deriv q (a.val r))⁻¹ at hd
  rw [hd, haq] at *
  constructor
  · simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr hkp') hdp).mpr hbounds.2
  · simpa only [inv_inv] using (inv_le_inv₀ hdp (inv_pos.mpr hmp)).mpr hbounds.1
end

theorem exists_omitted_inverse_profile_of_forward_slope
    {r0 u0 : ℝ} (hr : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
    {q : ℝ → ℝ} {C : ℝ≥0} (hql : LipschitzOnWith C q (Icc u0 1))
    (hqb : MapsTo q (Icc u0 1) (Icc r0 1)) (hq0 : q u0 = r0) (hq1 : q 1 = 1)
    {k M : ℝ → ℝ} (hk : ContinuousOn k (Icc r0 1)) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0 : ℝ) 1))
    (hkp : ∀ r ∈ Icc r0 1, 0 < k r) (hMp : ∀ u ∈ Icc u0 1, 0 < M u)
    (hder : ∀ᵐ u ∂volume, u ∈ Icc u0 1 →
      (M u)⁻¹ ≤ deriv q u ∧ deriv q u ≤ (k (q u))⁻¹) :
    ∃ α : inverseIntegralConstraints r0 u0 k M, ∀ u ∈ Icc u0 1, α.val.val (q u) = u := by
  have hM1 : 0 < M 1 := hMp 1 ⟨hu.2, le_rfl⟩
  have hlow : ∀ᵐ u ∂volume, u ∈ Icc u0 1 → (M 1)⁻¹ ≤ deriv q u := by
    filter_upwards [hder] with u hd hum
    exact ((inv_le_inv₀ hM1 (hMp u hum)).mpr
      (hm ⟨hu.1.trans hum.1, hum.2⟩ (by norm_num) hum.2)).trans (hd hum).1
  have hgap := (lipschitz_ae_deriv_lower_iff hu.2 hql continuousOn_const).mp hlow
  have hgap' : ∀ u ∈ Icc u0 1, ∀ v ∈ Icc u0 1, u ≤ v →
      (M 1)⁻¹*(v-u) ≤ q v-q u := by
    intro u hum v hvm huv
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hgap u hum v hvm huv
  have hqs : StrictMonoOn q (Icc u0 1) := by
    intro u hum v hvm huv
    have hh := hgap' u hum v hvm huv.le
    have hp := mul_pos (inv_pos.mpr hM1) (sub_pos.mpr huv)
    linarith
  have hqp := hql.continuousOn
  have ha := forwardOmittedInverseProfile_feasible hr hu hqp hqs hqb hq0 hq1
    hql (inv_pos.mpr hM1) hgap' hk hM hm hM1.le hkp hMp hder
  exact ⟨⟨forwardOmittedInverseProfile hr hu q hqp hqs hqb hq0 hq1, ha⟩,
    fun u hum => forwardOmittedInverseProfile_inverse hr hu hqp hqs hqb hq0 hq1 hum⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
