module

public import SKFluctuationsOAI.Probability.SKFluctuations.InverseConstraintQuantile

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def forwardUnitOrderIso (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc (0:ℝ) 1))
    (hs : StrictMonoOn q (Icc (0:ℝ) 1))
    (hb : MapsTo q (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
    (h0 : q 0=0) (h1 : q 1=1) : Icc (0:ℝ) 1 ≃o Icc (0:ℝ) 1 :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofStrictMono (fun u : Icc (0:ℝ) 1 => (⟨q u,hb u.property⟩ : Icc (0:ℝ) 1))
      (fun u v huv => hs u.property v.property huv)) (by
    intro v
    have hv : v.val ∈ Icc (q 0) (q 1) := by simpa only [h0,h1] using v.property
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc zero_le_one hq hv
    exact ⟨⟨u,hu⟩,Subtype.ext he⟩)

def forwardInverseProfile (q : ℝ → ℝ)
    (hq : ContinuousOn q (Icc (0:ℝ) 1))
    (hs : StrictMonoOn q (Icc (0:ℝ) 1))
    (hb : MapsTo q (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
    (h0 : q 0=0) (h1 : q 1=1) : boundedMassProfiles :=
  ⟨fun r => ((forwardUnitOrderIso q hq hs hb h0 h1).symm (projIcc 0 1 zero_le_one r)).val,by
    constructor
    · intro r
      exact ((forwardUnitOrderIso q hq hs hb h0 h1).symm (projIcc 0 1 zero_le_one r)).property
    · intro r s hrs
      exact (forwardUnitOrderIso q hq hs hb h0 h1).symm.monotone (monotone_projIcc zero_le_one hrs)⟩

section
variable {q : ℝ → ℝ}
variable (hq : ContinuousOn q (Icc (0:ℝ) 1))
variable (hs : StrictMonoOn q (Icc (0:ℝ) 1))
variable (hb : MapsTo q (Icc (0:ℝ) 1) (Icc (0:ℝ) 1))
variable (h0 : q 0=0) (h1 : q 1=1)

theorem forwardInverseProfile_spec {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    q ((forwardInverseProfile q hq hs hb h0 h1).val r)=r := by
  have he := congrArg Subtype.val ((forwardUnitOrderIso q hq hs hb h0 h1).apply_symm_apply
    (projIcc 0 1 zero_le_one r))
  change q ((forwardUnitOrderIso q hq hs hb h0 h1).symm (projIcc 0 1 zero_le_one r)).val=
    (projIcc 0 1 zero_le_one r).val at he
  simpa only [forwardInverseProfile,projIcc_of_mem zero_le_one hr] using he

theorem forwardInverseProfile_inverse {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (forwardInverseProfile q hq hs hb h0 h1).val (q u)=u := by
  apply hs.injOn ((forwardInverseProfile q hq hs hb h0 h1).property.1 (q u)) hu
  exact forwardInverseProfile_spec hq hs hb h0 h1 (hb hu)

theorem forwardInverseProfile_zero :
    (forwardInverseProfile q hq hs hb h0 h1).val 0=0 := by
  simpa only [h0] using forwardInverseProfile_inverse hq hs hb h0 h1 (u := 0) (by norm_num)

theorem forwardInverseProfile_one :
    (forwardInverseProfile q hq hs hb h0 h1).val 1=1 := by
  simpa only [h1] using forwardInverseProfile_inverse hq hs hb h0 h1 (u := 1) (by norm_num)

theorem forwardInverseProfile_lipschitz {lower : ℝ} (hlower : 0<lower)
    (hgap : ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,u≤v → lower*(v-u)≤q v-q u) :
    LipschitzOnWith ⟨lower⁻¹,inv_nonneg.mpr hlower.le⟩
      (forwardInverseProfile q hq hs hb h0 h1).val (Icc (0:ℝ) 1) := by
  let a := forwardInverseProfile q hq hs hb h0 h1
  have hbound {x y : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) (hxy : x≤y) :
      a.val y-a.val x ≤ lower⁻¹*(y-x) := by
    have hh := hgap (a.val x) (a.property.1 x) (a.val y) (a.property.1 y) (a.property.2 hxy)
    rw [forwardInverseProfile_spec hq hs hb h0 h1 hx,
      forwardInverseProfile_spec hq hs hb h0 h1 hy] at hh
    exact (le_inv_mul_iff₀ hlower).mpr hh
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change |a.val x-a.val y|≤lower⁻¹*|x-y|
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (a.property.2 hxy)),neg_sub] using hbound hx hy hxy
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (a.property.2 hyx))] using hbound hy hx hyx

theorem forwardInverseProfile_feasible {C : ℝ≥0} (hql : LipschitzOnWith C q (Icc (0:ℝ) 1))
    {lower : ℝ} (hlower : 0<lower)
    (hgap : ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,u≤v → lower*(v-u)≤q v-q u)
    {k M : ℝ → ℝ} (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM1 : 0≤M 1)
    (hkp : ∀ r∈Icc (0:ℝ) 1,0<k r)
    (hMp : ∀ u∈Icc (0:ℝ) 1,0<M u)
    (hder : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 →
      (M u)⁻¹≤deriv q u ∧ deriv q u≤(k (q u))⁻¹) :
    forwardInverseProfile q hq hs hb h0 h1 ∈ inverseIntegralConstraints 0 0 k M := by
  let a := forwardInverseProfile q hq hs hb h0 h1
  have hal := forwardInverseProfile_lipschitz hq hs hb h0 h1 hlower hgap
  rw [←inverseDifferentialConstraints_eq 0 0 zero_le_one k M hk hM hm hM1]
  refine ⟨forwardInverseProfile_zero hq hs hb h0 h1,
    forwardInverseProfile_one hq hs hb h0 h1,⟨lower⁻¹,inv_nonneg.mpr hlower.le⟩,hal,?_⟩
  have hac : AbsolutelyContinuousOnInterval q 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le zero_le_one] using hql
  have hdiff : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → DifferentiableAt ℝ q u := by
    simpa only [uIcc_of_le zero_le_one] using hac.ae_differentiableAt
  have hboth : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → DifferentiableAt ℝ q u ∧
      (M u)⁻¹≤deriv q u ∧ deriv q u≤(k (q u))⁻¹ := by
    filter_upwards [hdiff,hder] with u hd he hu
    exact ⟨hd hu,he hu⟩
  have hpull := ae_inverse_pullback hql (fun r (_ : r∈Icc (0:ℝ) 1) => a.property.1 r)
    (fun r hr => forwardInverseProfile_spec hq hs hb h0 h1 hr) hboth
  filter_upwards [hpull,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with r hp hr0 hr1 hr
  have hri : r∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0),lt_of_le_of_ne hr.2 hr1⟩
  have haq : q (a.val r)=r := forwardInverseProfile_spec hq hs hb h0 h1 hr
  have hbounds := (hp hr).2
  have hmp := hMp (a.val r) (a.property.1 r)
  have hkp' := hkp r hr
  have hdp : 0<deriv q (a.val r) := lt_of_lt_of_le (inv_pos.mpr hmp) hbounds.1
  have haCont : ContinuousAt a.val r := hal.continuousOn.continuousAt (Icc_mem_nhds hri.1 hri.2)
  have hinv : ∀ᶠ y in 𝓝 r,q (a.val y)=y := by
    filter_upwards [Icc_mem_nhds hri.1 hri.2] with y hy
    exact forwardInverseProfile_spec hq hs hb h0 h1 hy
  have hd := ((hp hr).1.hasDerivAt.of_local_left_inverse haCont hdp.ne' hinv).deriv
  change deriv a.val r=(deriv q (a.val r))⁻¹ at hd
  rw [hd]
  rw [haq] at hbounds
  constructor
  · have hi := (inv_le_inv₀ (inv_pos.mpr hkp') hdp).mpr hbounds.2
    simpa only [inv_inv] using hi
  · have hi := (inv_le_inv₀ hdp (inv_pos.mpr hmp)).mpr hbounds.1
    simpa only [inv_inv] using hi

end

theorem exists_inverse_profile_of_forward_slope {q : ℝ→ℝ} {C : ℝ≥0}
    (hql : LipschitzOnWith C q (Icc (0:ℝ) 1))
    (hqb : MapsTo q (Icc (0:ℝ) 1) (Icc (0:ℝ) 1)) (hq0 : q 0=0) (hq1 : q 1=1)
    {k M : ℝ→ℝ} (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0:ℝ) 1))
    (hkp : ∀r∈Icc (0:ℝ) 1,0<k r) (hMp : ∀u∈Icc (0:ℝ) 1,0<M u)
    (hder : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → (M u)⁻¹≤deriv q u ∧ deriv q u≤(k (q u))⁻¹) :
    ∃α : inverseIntegralConstraints 0 0 k M,∀u∈Icc (0:ℝ) 1,α.val.val (q u)=u := by
  have hM1 : 0<M 1 := hMp 1 (by norm_num)
  have hlow : ∀ᵐ u∂volume,u∈Icc (0:ℝ) 1 → (M 1)⁻¹≤deriv q u := by
    filter_upwards [hder] with u hd hu
    exact ((inv_le_inv₀ hM1 (hMp u hu)).mpr (hm hu (by norm_num) hu.2)).trans (hd hu).1
  have hgap := (lipschitz_ae_deriv_lower_iff zero_le_one hql continuousOn_const).mp hlow
  have hgap' : ∀u∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,u≤v → (M 1)⁻¹*(v-u)≤q v-q u := by
    intro u hu v hv huv
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hgap u hu v hv huv
  have hqs : StrictMonoOn q (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    have hh := hgap' u hu v hv huv.le
    have hp := mul_pos (inv_pos.mpr hM1) (sub_pos.mpr huv)
    linarith
  have hqp := hql.continuousOn
  have ha := forwardInverseProfile_feasible hqp hqs hqb hq0 hq1 hql (inv_pos.mpr hM1) hgap'
    hk hM hm hM1.le hkp hMp hder
  exact ⟨⟨forwardInverseProfile q hqp hqs hqb hq0 hq1,ha⟩,
    fun u hu=>forwardInverseProfile_inverse hqp hqs hqb hq0 hq1 hu⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
