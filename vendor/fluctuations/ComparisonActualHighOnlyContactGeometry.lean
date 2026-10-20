module

public import ComparisonActualHighOnlyPotential
public import ComparisonContactDerivative
public import ComparisonCapIntervals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def radiusS (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ→ℝ :=
  fun r=>orderedPathS n a.bf a.hf (a.alpha.val.val r)
def radiusB (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ→ℝ :=
  fun r=>orderedPathB n a.bf a.hf (a.alpha.val.val r)

theorem radius_mass_mem
    (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) : a.alpha.val.val r∈Icc (0:ℝ) 1 := by
  have H:=inverseConstraint_mass_mem zero_le_one a.data.hc a.data.hk a.data.hkc a.alpha hr
  exact ⟨a.data.hs.1.trans H.1,H.2⟩

theorem radius_moments
    (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn a.radiusS (Icc (0:ℝ) 1) ∧
    MonotoneOn a.radiusB (Icc (0:ℝ) 1) ∧
    ∀r∈Icc (0:ℝ) 1,a.radiusS r∈Icc (0:ℝ) 1 ∧
      (a.radiusS r)^2 ≤ a.radiusB r ∧ a.radiusB r ≤ 1 := by
  have hbounds (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
      orderedPathS n a.bf a.hf u∈Icc (0:ℝ) 1 ∧
        (orderedPathS n a.bf a.hf u)^2 ≤ orderedPathB n a.bf a.hf u ∧
          orderedPathB n a.bf a.hf u ≤ 1 := by
    by_cases hz:u=0
    · subst u
      simp only [orderedPathS,orderedPathB,orderedPathPair_zero]
      norm_num
    · have H:=orderedPath_SK_bounds n a.data.hn a.bf a.hf a.bf_monotone a.hf_monotone
        ⟨lt_of_le_of_ne hu.1 (Ne.symm hz),hu.2⟩
      exact ⟨⟨H.1,H.2.1⟩,H.2.2⟩
  have hmono (u v : ℝ) (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (huv : u ≤ v) :
      orderedPathS n a.bf a.hf u ≤ orderedPathS n a.bf a.hf v ∧
        orderedPathB n a.bf a.hf u ≤ orderedPathB n a.bf a.hf v := by
    by_cases hz:u=0
    · subst u
      simp only [orderedPathS,orderedPathB,orderedPathPair_zero]
      exact ⟨(hbounds v hv).1.1,(sq_nonneg _).trans (hbounds v hv).2.1⟩
    · have hp:0 < u:=lt_of_le_of_ne hu.1 (Ne.symm hz)
      have H:=orderedPath_SK_monotone n a.data.hn a.bf a.hf a.bf_monotone a.hf_monotone
      exact ⟨H.1 ⟨hp,hu.2⟩ ⟨hp.trans_le huv,hv.2⟩ huv,
        H.2 ⟨hp,hu.2⟩ ⟨hp.trans_le huv,hv.2⟩ huv⟩
  refine ⟨?_,?_,?_⟩
  · intro r hr t ht hrt
    exact (hmono _ _ (a.radius_mass_mem hr) (a.radius_mass_mem ht) (a.alpha.val.property.2 hrt)).1
  · intro r hr t ht hrt
    exact (hmono _ _ (a.radius_mass_mem hr) (a.radius_mass_mem ht) (a.alpha.val.property.2 hrt)).2
  · intro r hr
    exact hbounds _ (a.radius_mass_mem hr)

theorem Potential.contact_ae_deriv_le
    {a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N)
    (hnd : 1/a.data.N≤a.data.d) :
    ∀ᵐ r,r∈Icc (0:ℝ) 1→P.H r=0→deriv a.radiusS r≤9*Real.log a.data.N := by
  let w := a.data
  let p := comparisonLogSlope (laplaceComparisonStrength w.d a.lam)
  let κ := (1/3)/Real.log w.N
  have hlogp : 0<Real.log w.N := by linarith
  have hκ : 0<κ := div_pos (by norm_num) hlogp
  have hpm : MonotoneOn p (Ioc (0:ℝ) 1) := by
    intro r hr t ht hrt
    dsimp only [p]
    rw [laplaceComparisonStrength_logSlope w.hd.ne' (a.hlam).ne',
      laplaceComparisonStrength_logSlope w.hd.ne' (a.hlam).ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt a.hlam.le) (pow_nonneg w.hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : p r∈Icc (0:ℝ) (1-κ) := by
    refine ⟨(laplaceComparisonStrength_logSlope_mem w.hd.ne' (a.hlam).ne' r).1,?_⟩
    have hh := laplaceComparisonStrength_uniform_slope hN hlog w.hd hnd
      (a.hlam) a.hld ⟨hr.1.le,hr.2⟩
    dsimp only [κ,p]
    linarith
  have hmom := a.radius_moments
  have hcontact := comparison_contact_ae_deriv_le hκ hpm hpb hmom.1
    (hmom.2.1.mono Ioc_subset_Icc_self)
    (fun r hr=>(hmom.2.2 r ⟨hr.1.le,hr.2⟩).1.1)
    (fun r hr=>(hmom.2.2 r ⟨hr.1.le,hr.2⟩).2.1)
  have hconstant : 3/κ=9*Real.log w.N := by dsimp only [κ];field_simp;ring
  filter_upwards [P.hzero,hcontact,volume.ae_ne (0:ℝ)] with r hz hc hrmin hr hH
  have hrpos : 0<r := lt_of_le_of_ne hr.1 hrmin.symm
  have hbr : comparisonBracket (p r) r (a.radiusS r) (a.radiusB r)=0 := by
    have hg0 := (hz hr hH).1
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos w.d
      (a.hlam) r).ne'] at hg0
    have hh : (laplaceComparisonStrength w.d a.lam) r*comparisonBracket (p r) r (a.radiusS r) (a.radiusB r)=0 := by
      simpa only [p,radiusS,radiusB,comparisonBracket] using hg0
    exact (mul_eq_zero.mp hh).resolve_left (laplaceComparisonStrength_pos w.d
      (a.hlam) r).ne'
  simpa only [hconstant] using hc ⟨lt_of_le_of_ne hr.1 hrmin.symm,hr.2⟩ hbr

theorem Potential.cap_density_on_interval
    {a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {l r : ℝ} (hl : (0:ℝ)≤l) (hr : r≤1)
    (hnegative : ∀t∈Ioo l r,P.H t<0) :
    ∀ᵐ t,t∈Icc l r→deriv a.alpha.val.val t=a.data.M (a.alpha.val.val t) := by
  filter_upwards [P.hbang,volume.ae_ne l,volume.ae_ne r] with t ht htl htr hti
  exact ht ⟨hl.trans hti.1,hti.2.trans hr⟩
    (hnegative t ⟨lt_of_le_of_ne hti.1 htl.symm,lt_of_le_of_ne hti.2 htr⟩)

def cavityCapTravel (a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ℝ :=
  (comparisonConstraintLength a.data.N a.data.E a.data.d/a.data.N^delta)*
    Real.log ((1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E)

theorem Potential.cap_interval_travel
    {a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {l r : ℝ} (hl : (0:ℝ)≤l) (hlr : l≤r) (hr : r≤1)
    (hnegative : ∀t∈Ioo l r,P.H t<0) :
    (∫u in a.alpha.val.val l..a.alpha.val.val r,1/a.data.M u)=r-l ∧
    r-l≤a.cavityCapTravel ∧
    ∀v>0,v≤a.alpha.val.val l+comparisonSmallMass a.data.N a.data.E→
      r-l≤(a.alpha.val.val r-a.alpha.val.val l)*a.data.E/(a.data.N^delta*a.data.d^3*v^2) := by
  let w := a.data
  have hsub : Icc l r⊆Icc (0:ℝ) 1 := Icc_subset_Icc hl hr
  have hα := (inverseIntegralConstraints_lipschitz w.hm w.hM a.alpha.property).mono hsub
  have hm := (inverseConstraint_strictMonoOn w.hc w.hk w.hkc a.alpha.property).mono hsub
  have hden := P.cap_density_on_interval hl hr hnegative
  have hαr (t : ℝ) (ht : t∈Icc l r) : a.alpha.val.val t∈Icc (0:ℝ) 1 :=
    ⟨(a.radius_mass_mem (hsub ht)).1,(a.radius_mass_mem (hsub ht)).2⟩
  have hM (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : 0<w.M u :=
    (comparisonCap_first_term (δ:=delta) w.hN w.hU w.hL w.hE w.hd.le hu.1).1
  have heq := cap_travel_identity hlr hα hm (fun t ht=>hM _ (hαr t ht)) hden
  have ht := cap_travel_le_total hlr hα hm hαr
    (comparisonCap_continuous w.N delta (comparisonSmallMass w.N w.E)
      (comparisonConstraintLength w.N w.E w.d) w.E w.d).continuousOn hM hden
  have hW : (∫u in (0:ℝ)..1,1/w.M u)≤a.cavityCapTravel := by
    simpa only [cavityCapTravel,ActualHighOnlyComparisonData.M,w,zero_add] using comparisonCap_log_travel (δ:=delta)
      w.hN w.hU w.hL w.hE w.hd.le (a:=0) (b:=1) le_rfl zero_le_one
  refine ⟨heq,ht.trans hW,?_⟩
  intro v hv hva
  rw [←heq]
  exact comparisonCap_band_travel (δ:=delta) w.hN w.hU w.hL w.hE w.hd hv hva
    (hαr l ⟨le_rfl,hlr⟩).1 (hm.monotoneOn ⟨le_rfl,hlr⟩ ⟨hlr,le_rfl⟩ hlr)

end ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_contact_derivative
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀ P : a.Potential,∀ᵐ r,r∈Icc (0:ℝ) 1→P.H r=0→
        deriv a.radiusS r≤9*Real.log a.data.N := by
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_comparisonLowerScale_depth hC0 hm,hlog,
    eventually_ge_atTop (1:ℕ)] with n hdepth hnlog hn1
  intro a P
  have hs : comparisonLowerScale n a.data.E a.data.d≤a.data.d := by
    unfold comparisonLowerScale
    exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
  exact P.contact_ae_deriv_le (by exact_mod_cast hn1) hnlog
    ((hdepth a.data.E a.data.d a.data.hE a.data.hd a.hlower).trans hs)

theorem eventually_actual_high_only_cap_travel_small
    {m delta cl cu Az C0 Ct D Bclock epsilon : ℝ}
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ a : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
        a.cavityCapTravel≤epsilon*a.xs ∧
        ∀ (P : a.Potential) (l r : ℝ), (0:ℝ) ≤ l → l ≤ r → r ≤ 1 →
          (∀ t ∈ Ioo l r, P.H t < 0) → r-l ≤ epsilon*a.xs := by
  filter_upwards [eventually_comparisonTravel_small (C:=C0) (D:=D)
    hC0 hroom hepsilon] with n hn
  intro a
  have hc : a.cavityCapTravel≤epsilon*a.xs := by
    exact (hn a.data.E a.data.d a.data.hE a.data.hd a.hdD a.hupper a.hlower).trans
      (mul_le_mul_of_nonneg_left a.hscale hepsilon.le)
  refine ⟨hc,?_⟩
  intro P l r hl hlr hr hnegative
  exact (P.cap_interval_travel hl hlr hr hnegative).2.1.trans hc

end OAI.SKFluctuations.LaplaceWindowFormalization
