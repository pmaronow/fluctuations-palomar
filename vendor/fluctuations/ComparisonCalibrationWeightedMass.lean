module

public import ComparisonCalibrationFloorMass
public import ComparisonScalarWeightedCapTravel
public import ComparisonWholeCapEndpoints

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 4000000

theorem comparison_ac_density_hasDerivAt
    {H f : ℝ→ℝ} {a b : ℝ} (hab : a≤b)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hd : ∀ᵐ r,r∈Icc a b→HasDerivAt H (f r) r)
    (hf : ContinuousOn f (Ioo a b)) {r : ℝ} (hr : r∈Ioo a b) :
    HasDerivAt H (f r) r := by
  have he : deriv H =ᵐ[volume.restrict (uIoc a b)] f := by
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_uIoc] with t ht hti
    rw [uIoc_of_le hab] at hti
    exact (ht ⟨hti.1.le,hti.2⟩).deriv
  have hi := hH.intervalIntegrable_deriv.congr_ae he
  have hprimitive t (ht : t∈Icc a b) : H t=H a+∫s in a..t,f s := by
    have hsub : uIcc a t⊆uIcc a b := by
      rw [uIcc_of_le ht.1,uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hac := hH.mono hsub
    have heq : (∫s in a..t,deriv H s)=∫s in a..t,f s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with s hs hsi
      rw [uIoc_of_le ht.1] at hsi
      exact (hs ⟨hsi.1.le,hsi.2.trans ht.2⟩).deriv
    rw [hac.integral_deriv_eq_sub] at heq
    linarith
  have hri : IntervalIntegrable f volume a r :=
    hi.mono (by rw [uIcc_of_le hr.1.le,uIcc_of_le hab];exact Icc_subset_Icc le_rfl hr.2.le) le_rfl
  have hp := (intervalIntegral.integral_hasDerivAt_right hri
    (hf.stronglyMeasurableAtFilter isOpen_Ioo r hr)
    (hf.continuousAt (isOpen_Ioo.mem_nhds hr))).const_add (H a)
  apply hp.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
  exact hprimitive t ⟨ht.1.le,ht.2.le⟩

theorem comparison_negative_point_has_interior_zero_cap
    {H : ℝ→ℝ} {origin travel r : ℝ} (hH : Continuous H) (hT : 0≤travel)
    (hr : r∈Ioo (origin+travel) (1-travel)) (hneg : H r<0)
    (htravel : ∀a b,origin≤a→b≤1→a<b→(∀t∈Ioo a b,H t<0)→b-a≤travel) :
    ∃a b,origin<a ∧ a<r ∧ r<b ∧ b<1 ∧ H a=0 ∧ H b=0 ∧
      (∀t∈Ioo a b,H t<0) ∧ b-a≤travel := by
  let U := Ioo origin 1∩{t | H t<0}
  have hU : IsOpen U := isOpen_Ioo.inter (isOpen_lt hH continuous_const)
  have hrU : r∈U := ⟨⟨by linarith [hr.1],by linarith [hr.2]⟩,hneg⟩
  obtain ⟨hal,har,hrb,hbz,heq,haU,hbU⟩ :=
    WholeUnitSideKernel.wholeCap_component_endpoints hU
      (show U⊆Icc origin 1 from fun t ht=>⟨ht.1.1.le,ht.1.2.le⟩) hrU
  let a := sInf (ordConnectedComponent U r)
  let b := sSup (ordConnectedComponent U r)
  change origin≤a at hal
  change a<r at har
  change r<b at hrb
  change b≤1 at hbz
  have hn : ∀t∈Ioo a b,H t<0 := by
    intro t ht
    have hc : t∈ordConnectedComponent U r := heq.symm ▸ ht
    exact (ordConnectedComponent_subset hc).2
  have hab : a<b := har.trans hrb
  have hw := htravel a b hal hbz hab hn
  have ha : origin<a := by
    by_contra hh
    have hae : a=origin := le_antisymm (not_lt.mp hh) hal
    rw [hae] at hw har
    linarith [hr.1,hrb]
  have hb : b<1 := by
    by_contra hh
    have hbe : b=1 := le_antisymm hbz (not_lt.mp hh)
    rw [hbe] at hw hrb
    linarith [hr.2,har]
  have hclosed : IsClosed {t | H t≤0} := isClosed_le hH continuous_const
  have hc := closure_minimal (show Ioo a b⊆{t | H t≤0} from fun t ht=>(hn t ht).le) hclosed
  rw [closure_Ioo hab.ne] at hc
  have ha0 : H a≤0 := hc ⟨le_rfl,hab.le⟩
  have hb0 : H b≤0 := hc ⟨hab.le,le_rfl⟩
  have ha1 : 0≤H a := by
    by_contra hh
    exact haU ⟨⟨ha,har.trans hrb |>.trans hb⟩,lt_of_not_ge hh⟩
  have hb1 : 0≤H b := by
    by_contra hh
    exact hbU ⟨⟨ha.trans hab,hb⟩,lt_of_not_ge hh⟩
  exact ⟨a,b,ha,har,hrb,hb,le_antisymm ha0 ha1,le_antisymm hb0 hb1,hn,hw⟩

theorem comparison_negative_point_has_interior_zero_cap_on_working
    {H : ℝ→ℝ} {origin travel r : ℝ} (hwork : origin≤1)
    (hH : ContinuousOn H (Icc origin 1)) (hT : 0≤travel)
    (hr : r∈Ioo (origin+travel) (1-travel)) (hneg : H r<0)
    (htravel : ∀a b,origin≤a→b≤1→a<b→(∀t∈Ioo a b,H t<0)→b-a≤travel) :
    ∃a b,origin<a ∧ a<r ∧ r<b ∧ b<1 ∧ H a=0 ∧ H b=0 ∧
      (∀t∈Ioo a b,H t<0) ∧ b-a≤travel := by
  let F : C(Icc origin 1,ℝ) := ⟨fun r=>H r.val,continuousOn_iff_continuous_domRestrict.mp hH⟩
  let Hext := IccExtend hwork F
  have he t (ht : t∈Icc origin 1) : Hext t=H t := IccExtend_of_mem hwork F ht
  have hrcc : r∈Icc origin 1 := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have htr a b (ha : origin≤a) (hb : b≤1) (hab : a<b)
      (hn : ∀t∈Ioo a b,Hext t<0) : b-a≤travel := by
    apply htravel a b ha hb hab
    intro t ht
    rw [←he t ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩]
    exact hn t ht
  have hHe : Continuous Hext := F.continuous.Icc_extend' (h:=hwork)
  have hnegr : Hext r<0 := by rw [he r hrcc];exact hneg
  obtain ⟨a,b,ha,har,hrb,hb,hHa,hHb,hn,hw⟩ := comparison_negative_point_has_interior_zero_cap
    (H:=Hext) hHe hT hr hnegr htr
  have hac : a∈Icc origin 1 := ⟨ha.le,(har.trans hrb |>.trans hb).le⟩
  have hbc : b∈Icc origin 1 := ⟨(ha.trans har |>.trans hrb).le,hb.le⟩
  refine ⟨a,b,ha,har,hrb,hb,?_,?_,?_,hw⟩
  · simpa only [he a hac] using hHa
  · simpa only [he b hbc] using hHb
  · intro t ht
    simpa only [he t ⟨ha.le.trans ht.1.le,ht.2.le.trans hb.le⟩] using hn t ht

theorem comparison_calibration_shifted_cap_travel
    {N delta U L E d origin u0 c : ℝ} {k : ℝ→ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0<d)
    (hc : 0<c) (hk : ContinuousOn k (Icc origin 1)) (hkc : ∀r∈Icc origin 1,c≤k r)
    (alpha : inverseIntegralConstraints origin u0 k (comparisonCap N delta U L E d))
    (H : ℝ→ℝ)
    (hcap : ∀ᵐ r,r∈Icc origin 1→H r<0→deriv alpha.val.val r=
      comparisonCap N delta U L E d (alpha.val.val r))
    {a b : ℝ} (ha : origin≤a) (hb : b≤1) (hab : a<b)
    (hneg : ∀r∈Ioo a b,H r<0) :
    b-a≤(L/N^delta)*Real.log ((1+U)/U) := by
  have hm := comparisonCap_monotoneOn (δ:=delta) hN hU.le hL hE hd.le
  have hM := comparisonCap_nonneg (δ:=delta) hN hU.le hL hE hd.le zero_le_one
  have hsub : Icc a b⊆Icc origin 1 := Icc_subset_Icc ha hb
  have hden : ∀ᵐ r,r∈Icc a b→deriv alpha.val.val r=
      comparisonCap N delta U L E d (alpha.val.val r) := by
    filter_upwards [hcap,volume.ae_ne a,volume.ae_ne b] with r hr hra hrb hri
    exact hr (hsub hri) (hneg r ⟨lt_of_le_of_ne hri.1 hra.symm,lt_of_le_of_ne hri.2 hrb⟩)
  have hp u (hu : u∈Icc (0:ℝ) 1) : 0<comparisonCap N delta U L E d u :=
    (comparisonCap_first_term (δ:=delta) hN hU hL hE hd.le hu.1).1
  have hw := cap_travel_le_total hab.le
    ((inverseIntegralConstraints_lipschitz hm hM alpha.property).mono hsub)
    ((inverseConstraint_strictMonoOn hc hk hkc alpha.property).mono hsub)
    (fun r _=>alpha.val.property.1 r) (comparisonCap_continuous N delta U L E d).continuousOn hp hden
  have ht : (∫u in (0:ℝ)..1,1/comparisonCap N delta U L E d u)≤
      (L/N^delta)*Real.log ((1+U)/U) := by
    simpa only [zero_add] using comparisonCap_log_travel (δ:=delta) hN hU hL hE hd.le
      (a:=0) (b:=1) le_rfl zero_le_one
  exact hw.trans ht

theorem comparison_calibration_nonfloor_native_weighted_point
    {N delta E d lam x origin u0 c : ℝ} {k : ℝ→ℝ}
    (hN : 0<N) (hE : 0<E) (hd : 0<d) (hlam : 0<lam) (hld : lam≤d^2)
    (hx : 0<x) (hax : comparisonLowerScale N E d≤x) (hwork : origin≤1)
    (hc : 0<c) (hk : ContinuousOn k (Icc origin 1)) (hkc : ∀r∈Icc origin 1,c≤k r)
    (alpha : inverseIntegralConstraints origin u0 k
      (comparisonCap N delta (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d))
    (H S factor : ℝ→ℝ)
    (hH : AbsolutelyContinuousOnInterval H origin 1)
    (hD : ∀ᵐ r,r∈Icc origin 1→HasDerivAt H (factor r*(r-S (alpha.val.val r))) r)
    (hDc : ContinuousOn (fun r=>factor r*(r-S (alpha.val.val r))) (Ioo origin 1))
    (hfactor : ∀r∈Ioo origin 1,0<factor r)
    (hS : MonotoneOn (fun r=>S (alpha.val.val r)) (Icc origin 1))
    (hcontact : ∀ᵐ r,r∈Icc origin 1→H r=0→factor r*(r-S (alpha.val.val r))=0)
    (hcap : ∀ᵐ r,r∈Icc origin 1→H r<0→deriv alpha.val.val r=
      comparisonCap N delta (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (alpha.val.val r)) :
    let travel := (comparisonConstraintLength N E d/N^delta)*
      Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)
    ∀ᵐ r,r∈Ioo (origin+travel) (1-travel)→H r≤0→
      |laplaceComparisonStrength d lam r*(S (alpha.val.val r)-r)|≤
        (Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)/N^delta)*x^3 := by
  let U := comparisonSmallMass N E
  let L := comparisonConstraintLength N E d
  let travel := (L/N^delta)*Real.log ((1+U)/U)
  have hU := comparisonSmallMass_pos hN hE
  have hL := comparisonConstraintLength_pos hN hE hd
  have hT : 0≤travel := by
    have hh : 1≤(1+U)/U := (le_div_iff₀ hU).mpr (by linarith)
    exact mul_nonneg (div_nonneg hL.le (Real.rpow_pos_of_pos hN _).le) (Real.log_nonneg hh)
  have htravel a b (ha : origin≤a) (hb : b≤1) (hab : a<b)
      (hn : ∀r∈Ioo a b,H r<0) : b-a≤travel :=
    comparison_calibration_shifted_cap_travel hN hU hL hE hd hc hk hkc alpha H hcap ha hb hab hn
  filter_upwards [hcontact] with r hr hri hHr
  have hrcc : r∈Icc origin 1 := ⟨by linarith [hri.1],by linarith [hri.2]⟩
  by_cases hneg : H r<0
  · obtain ⟨a,b,ha,har,hrb,hb,hHa,hHb,hn,hw⟩ :=
      comparison_negative_point_has_interior_zero_cap_on_working hwork
        (by simpa only [uIcc_of_le hwork] using hH.continuousOn) hT hri hneg htravel
    have hai : a∈Ioo origin 1 := ⟨ha,har.trans hrb |>.trans hb⟩
    have hbi : b∈Ioo origin 1 := ⟨ha.trans har |>.trans hrb,hb⟩
    have hda := comparison_ac_density_hasDerivAt hwork hH hD hDc hai
    have hdb := comparison_ac_density_hasDerivAt hwork hH hD hDc hbi
    have hs := comparison_negative_cap_spin_endpoint_bounds H (fun r=>S (alpha.val.val r))
      (har.trans hrb) hHa hHb hn (hfactor a hai) (hfactor b hbi) hda hdb
    have hsub : Icc a b⊆Icc origin 1 := Icc_subset_Icc ha.le hb.le
    have hh := comparison_scalar_negative_cap_weighted_error hN hE hd hlam hld hx hax
      (fun r=>S (alpha.val.val r)) (hS.mono hsub) hs.1 hs.2 ⟨har.le,hrb.le⟩ hw
    rw [abs_mul,abs_of_nonneg (laplaceComparisonStrength_pos d hlam r).le]
    exact (div_le_iff₀ (pow_pos hx 3)).mp hh
  · have hz : H r=0 := le_antisymm hHr (not_lt.mp hneg)
    have hf : 0<factor r := hfactor r ⟨by linarith [hri.1],by linarith [hri.2]⟩
    have hs : S (alpha.val.val r)=r := by
      have hh := (mul_eq_zero.mp (hr hrcc hz)).resolve_left hf.ne'
      linarith
    rw [hs,sub_self,mul_zero,abs_zero]
    have hh : 1≤(1+U)/U := (le_div_iff₀ hU).mpr (by linarith)
    exact mul_nonneg (div_nonneg (Real.log_nonneg hh) (Real.rpow_pos_of_pos hN _).le) (pow_pos hx 3).le

section Shifted
variable {origin u0 c : ℝ} {k M : ℝ→ℝ}
    (hr : origin≤1) (hc : 0<c) (hk : ContinuousOn k (Icc origin 1))
    (hkc : ∀r∈Icc origin 1,c≤k r) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparison_calibration_constrained_radius_mass_spec
    (alpha : inverseIntegralConstraints origin u0 k M) {u : ℝ} (hu : u∈Icc u0 1) :
    alpha.val.val (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha u)=u ∧
      comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha u∈Icc origin 1 := by
  rw [comparisonCalibrationConstrainedRadius,IccExtend_of_mem _ _ hu]
  exact ⟨constrainedQuantile_spec hr hc hk hkc hm hM alpha ⟨u,hu⟩,
    (constrainedQuantile hr hc hk hkc hm hM alpha ⟨u,hu⟩).property⟩

theorem comparison_calibration_constrained_radius_monotone
    (alpha : inverseIntegralConstraints origin u0 k M) :
    Monotone (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha) := by
  apply Monotone.IccExtend (comparison_calibration_mass_origin_le_one alpha)
  intro u v huv
  exact (inverseConstraintOrderIso hr hc hk hkc hm hM alpha).symm.monotone huv

theorem comparison_calibration_mass_substitution_on_band
    (alpha : inverseIntegralConstraints origin u0 k M) {a z : ℝ}
    (ha : u0≤a) (haz : a≤z) (hz : z≤1) (F : ℝ→ℝ) :
    let R := comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha
    (∫u in a..z,F u)=∫r in Icc (R a) (R z),deriv alpha.val.val r*F (alpha.val.val r) := by
  dsimp only
  let R := comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha
  have hma : a∈Icc u0 1 := ⟨ha,haz.trans hz⟩
  have hmz : z∈Icc u0 1 := ⟨ha.trans haz,hz⟩
  have hRa := comparison_calibration_constrained_radius_mass_spec hr hc hk hkc hm hM alpha hma
  have hRz := comparison_calibration_constrained_radius_mass_spec hr hc hk hkc hm hM alpha hmz
  have habR : R a≤R z := comparison_calibration_constrained_radius_monotone hr hc hk hkc hm hM alpha haz
  have hsub : Icc (R a) (R z)⊆Icc origin 1 := Icc_subset_Icc hRa.2.1 hRz.2.2
  have hLip := (inverseIntegralConstraints_lipschitz hm hM alpha.property).mono hsub
  have hMono := (inverseConstraint_strictMonoOn hc hk hkc alpha.property).mono hsub
  have himage : alpha.val.val '' Icc (R a) (R z)=Icc a z := by
    rw [hLip.continuousOn.image_Icc_of_monotoneOn habR hMono.monotoneOn,hRa.1,hRz.1]
  rw [intervalIntegral.integral_of_le haz,←integral_Icc_eq_integral_Ioc,←himage,
    lipschitz_interval_integral_image habR hLip hMono.injOn]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards [] with r _
  rw [abs_of_nonneg alpha.val.property.2.deriv_nonneg]

theorem comparison_calibration_nonfloor_weighted_mass_le
    (alpha : inverseIntegralConstraints origin u0 k M) (H S e : ℝ→ℝ)
    {a z C : ℝ} (ha : u0≤a) (haz : a≤z) (hz : z≤1) (hC : 0≤C)
    (hweighted : ∀ᵐ r,r∈Icc
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha a)
      (comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha z) →
      H r≤0→|e r*(S (alpha.val.val r)-r)|≤C) :
    let R := comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha
    (∫u in a..z,(comparisonCalibrationFloor H R)ᶜ.indicator
      (fun u=>|e (R u)*(S u-R u)|) u)≤C*(z-a) := by
  dsimp only
  let R := comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha
  let F := (comparisonCalibrationFloor H R)ᶜ.indicator (fun u=>|e (R u)*(S u-R u)|)
  have hma : a∈Icc u0 1 := ⟨ha,haz.trans hz⟩
  have hmz : z∈Icc u0 1 := ⟨ha.trans haz,hz⟩
  have hRa := comparison_calibration_constrained_radius_mass_spec hr hc hk hkc hm hM alpha hma
  have hRz := comparison_calibration_constrained_radius_mass_spec hr hc hk hkc hm hM alpha hmz
  have habR : R a≤R z := comparison_calibration_constrained_radius_monotone hr hc hk hkc hm hM alpha haz
  have hsub : Icc (R a) (R z)⊆Icc origin 1 := Icc_subset_Icc hRa.2.1 hRz.2.2
  have hLipU : LipschitzOnWith ⟨M 1,hM⟩ alpha.val.val (uIcc (R a) (R z)) := by
    rw [uIcc_of_le habR]
    exact (inverseIntegralConstraints_lipschitz hm hM alpha.property).mono hsub
  have hi : IntegrableOn (deriv alpha.val.val) (Icc (R a) (R z)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le habR (by simp)).mp
      hLipU.absolutelyContinuousOnInterval.intervalIntegrable_deriv
  have hbound : (∫r in Icc (R a) (R z),deriv alpha.val.val r*F (alpha.val.val r))≤
      ∫r in Icc (R a) (R z),C*deriv alpha.val.val r := by
    apply integral_mono_of_nonneg (Eventually.of_forall fun r=>mul_nonneg
      alpha.val.property.2.deriv_nonneg (Set.indicator_nonneg (fun _ _=>abs_nonneg _) _)) (hi.const_mul C)
    filter_upwards [ae_restrict_of_ae hweighted,ae_restrict_mem measurableSet_Icc] with r hw hri
    have hR : R (alpha.val.val r)=r := comparison_calibration_constrained_radius_inverse hr hc hk hkc hm hM alpha (hsub hri)
    have hF : F (alpha.val.val r)≤C := by
      by_cases hpot : 0<H r
      · have hmem : alpha.val.val r∈comparisonCalibrationFloor H R := by
          change 0<H (R (alpha.val.val r));rw [hR];exact hpot
        simpa only [F,Set.indicator_of_notMem (show alpha.val.val r∉(comparisonCalibrationFloor H R)ᶜ from fun h=>h hmem)] using hC
      · have hmem : alpha.val.val r∈(comparisonCalibrationFloor H R)ᶜ := by
          change ¬0<H (R (alpha.val.val r));rw [hR];exact hpot
        simpa only [F,Set.indicator_of_mem hmem,hR] using hw hri (not_lt.mp hpot)
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left hF alpha.val.property.2.deriv_nonneg
  have hmass : (∫r in Icc (R a) (R z),C*deriv alpha.val.val r)=C*(z-a) := by
    rw [integral_const_mul,integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le habR,
      hLipU.absolutelyContinuousOnInterval.integral_deriv_eq_sub,hRa.1,hRz.1]
  rw [comparison_calibration_mass_substitution_on_band hr hc hk hkc hm hM alpha ha haz hz]
  exact hbound.trans_eq hmass

theorem comparison_calibration_weighted_mass_integrable
    (alpha : inverseIntegralConstraints origin u0 k M) (H S : ℝ→ℝ)
    (hH : Measurable H) (hS : Measurable S) (hSb : ∀u∈Icc u0 1,S u∈Icc (0:ℝ) 1)
    {a z d lam : ℝ} (horigin : 0≤origin) (hlam : 0<lam)
    (ha : u0≤a) (haz : a≤z) (hz : z≤1) :
    let R := comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha
    IntervalIntegrable ((comparisonCalibrationFloor H R)ᶜ.indicator
      (fun u=>|laplaceComparisonStrength d lam (R u)*(S u-R u)|)) volume a z := by
  dsimp only
  let R := comparisonCalibrationConstrainedRadius hr hc hk hkc hm hM alpha
  have hRm : Measurable R :=
    (comparison_calibration_constrained_radius_continuous hr hc hk hkc hm hM alpha).measurable
  have hfl : MeasurableSet (comparisonCalibrationFloor H R) :=
    measurableSet_lt measurable_const (hH.comp hRm)
  have hFm : Measurable ((comparisonCalibrationFloor H R)ᶜ.indicator
      (fun u=>|laplaceComparisonStrength d lam (R u)*(S u-R u)|)) :=
    ((((laplaceComparisonStrength_contDiff d lam).continuous.measurable.comp hRm).mul
      (hS.sub hRm)).abs).indicator hfl.compl
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le haz (by simp)]
  apply Integrable.of_bound hFm.aestronglyMeasurable lam
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have hui : u∈Icc u0 1 := ⟨ha.trans hu.1,hu.2.trans hz⟩
  have hR := (comparison_calibration_constrained_radius_mass_spec hr hc hk hkc hm hM alpha hui).2
  change R u∈Icc origin 1 at hR
  have hs := hSb u hui
  have hdiff : |S u-R u|≤1 := abs_le.mpr ⟨by linarith [hR.2,hs.1],by linarith [hR.1,hs.2]⟩
  by_cases hf : u∈(comparisonCalibrationFloor H R)ᶜ
  · rw [Set.indicator_of_mem hf,Real.norm_eq_abs,abs_abs,abs_mul,
      abs_of_nonneg (laplaceComparisonStrength_pos d hlam (R u)).le]
    exact (mul_le_mul_of_nonneg_left hdiff
      (laplaceComparisonStrength_pos d hlam (R u)).le).trans
      (by simpa only [mul_one] using laplaceComparisonStrength_le d hlam.le (R u))
  · rw [Set.indicator_of_notMem hf,norm_zero]
    exact hlam.le

end Shifted

theorem comparison_calibration_high_flat_weighted_mass
    {N delta E d lam x origin u0 c a z : ℝ} {k : ℝ→ℝ}
    (hN : 0<N) (hE : 0<E) (hd : 0<d) (hlam : 0<lam) (hld : lam≤d^2)
    (hx : 0<x) (hax : comparisonLowerScale N E d≤x) (hwork : origin≤1) (horigin : 0≤origin)
    (hc : 0<c) (hk : ContinuousOn k (Icc origin 1)) (hkc : ∀r∈Icc origin 1,c≤k r)
    (alpha : inverseIntegralConstraints origin u0 k
      (comparisonCap N delta (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d))
    (H S factor : ℝ→ℝ) (hHmeas : Measurable H) (hSmeas : Measurable S)
    (hSb : ∀u∈Icc u0 1,S u∈Icc (0:ℝ) 1)
    (hH : AbsolutelyContinuousOnInterval H origin 1)
    (hD : ∀ᵐ r,r∈Icc origin 1→HasDerivAt H (factor r*(r-S (alpha.val.val r))) r)
    (hDc : ContinuousOn (fun r=>factor r*(r-S (alpha.val.val r))) (Ioo origin 1))
    (hfactor : ∀r∈Ioo origin 1,0<factor r)
    (hS : MonotoneOn (fun r=>S (alpha.val.val r)) (Icc origin 1))
    (hcontact : ∀ᵐ r,r∈Icc origin 1→H r=0→factor r*(r-S (alpha.val.val r))=0)
    (hcap : ∀ᵐ r,r∈Icc origin 1→H r<0→deriv alpha.val.val r=
      comparisonCap N delta (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (alpha.val.val r))
    (ha : u0≤a) (haz : a≤z) (hz : z≤1)
    (hmargin : ∀hm hM,
      let R := comparisonCalibrationConstrainedRadius hwork hc hk hkc hm hM alpha
      let travel := (comparisonConstraintLength N E d/N^delta)*
        Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)
      origin+travel<R a ∧ R z<1-travel) :
    ∀hm hM,
      let R := comparisonCalibrationConstrainedRadius hwork hc hk hkc hm hM alpha
      let F := (comparisonCalibrationFloor H R)ᶜ.indicator
        (fun u=>|laplaceComparisonStrength d lam (R u)*(S u-R u)|)
      IntervalIntegrable F volume a z ∧
      (∫u in a..z,F u)≤
        (Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)/N^delta)*x^3*(z-a) := by
  intro hm hM
  dsimp only
  let R := comparisonCalibrationConstrainedRadius hwork hc hk hkc hm hM alpha
  let C := (Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E)/N^delta)*x^3
  have hU := comparisonSmallMass_pos hN hE
  have hlog : 0≤Real.log ((1+comparisonSmallMass N E)/comparisonSmallMass N E) :=
    Real.log_nonneg ((le_div_iff₀ hU).mpr (by linarith))
  have hC : 0≤C := mul_nonneg (div_nonneg hlog (Real.rpow_pos_of_pos hN _).le) (pow_pos hx 3).le
  have hp := comparison_calibration_nonfloor_native_weighted_point hN hE hd hlam hld hx hax hwork
    hc hk hkc alpha H S factor hH hD hDc hfactor hS hcontact hcap
  have hmargin' := hmargin hm hM
  have hw : ∀ᵐ r,r∈Icc (R a) (R z)→H r≤0→
      |laplaceComparisonStrength d lam r*(S (alpha.val.val r)-r)|≤C := by
    filter_upwards [hp] with r hr hri hHr
    exact hr ⟨hmargin'.1.trans_le hri.1,hri.2.trans_lt hmargin'.2⟩ hHr
  refine ⟨comparison_calibration_weighted_mass_integrable hwork hc hk hkc hm hM alpha H S
    hHmeas hSmeas hSb horigin hlam ha haz hz,?_⟩
  exact comparison_calibration_nonfloor_weighted_mass_le hwork hc hk hkc hm hM alpha H S
    (laplaceComparisonStrength d lam) ha haz hz hC hw

end OAI.SKFluctuations.LaplaceWindowFormalization
