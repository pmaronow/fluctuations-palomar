module

public import ComparisonActualHighOnlyLocalCapAssemblyAboveWall
public import ComparisonActualHighOnlyOrdinaryLocalMassBudget
public import ComparisonActualHighOnlyOuterComparableBroadMassBudget
public import ComparisonActualHighOnlyLocalThermalSignPartition
public import ComparisonActualHighOnlyOuterFloorThermalMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
attribute [local instance] Classical.propDecidable
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_outer_comparable_mass_of_explicit_budgets
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Qo Qb Kfloor : ℝ,1 ≤ Qo ∧ 1 ≤ Qb ∧ 0 < Kfloor ∧
      ∀ᶠn:ℕ in atTop,
      ∀a:ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
        a.data.s ≤ 1/4 → a.data.s ≤ a.xs → ∀_P:a.Potential,
        NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      ∀lo hi cut Lside O B : ℝ,
        lo∈Icc (0:ℝ) 1 → hi∈Icc (0:ℝ) 1 → lo ≤ hi → a.data.U ≤ lo → 32*a.data.s < lo → 8*a.massCoverBase<lo →
        2*cu*(Az+1)*a.xs≤lo →
        0 < cut → 2*cut < a.data.U → 0 ≤ Lside → Real.log (1/cut) ≤ Lside → 0 ≤ O → 0 ≤ B →
        (∀v∈Icc (lo/16) hi,0 < v → v ≤ 1 →
          a.canonicalOrdinaryMassBudgetAtDiameter ell Qo Lside cut v (a.canonicalLocalMassDiameter v) ≤ O) →
        (∀v∈Icc (lo/4) (2*hi),0 < v → v ≤ 1 → ∀width∈Icc v (4*v),width ≤ 1 →
          a.canonicalComparableBroadMassBudgetAtDiameter ell Qb Lside cut v width (a.canonicalOuterBroadMassDiameter v) ≤ B) →
      (∫u in lo..hi,orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2) ≤ 
        (2*O+4*B)*(Nat.ceil (Real.log (1/a.data.U)/Real.log 2)+1)+
          Kfloor*(a.xs+hi)^2*a.data.N^delta*a.data.U^2/(lo/cu) := by
  obtain ⟨Qo,hQo,HO⟩:=eventually_actual_high_only_local_ordinary_mass_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Qb,hQb,HB⟩:=eventually_actual_high_only_outer_comparable_broad_mass_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Kfloor,hKfloor,HF⟩:=eventually_actual_high_only_positive_radius_floor_thermal Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have HT:=(tendsto_add_atTop_nat 1).eventually (eventually_actual_high_only_cap_travel_small
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=1)
    hC0 (by linarith : 0<3*margin+delta) zero_lt_one)
  refine ⟨Qo,Qb,Kfloor,hQo,hQb,hKfloor,?_⟩
  filter_upwards [HO,HB,HF,HT] with n hnO hnB hnF hnT
  intro a hs hsxs P hclock lo hi cut Lside O B hlo hhi hlh hU hstart hwall houter
    hcut hcutU hLside hlogcut hO hB hOrd hBroad
  let m:=a.shiftedNativeModel
  let A:=m.massSlice lo hi
  have hloHigh : lo∈Icc a.data.s 1:=⟨by linarith [a.data.hs.1],hlo.2⟩
  have hhiHigh : hi∈Icc a.data.s 1:=⟨hloHigh.1.trans hlh,hhi.2⟩
  have hA : MeasurableSet A:=measurableSet_Ioo
  have hAD : A⊆Ioo (0:ℝ) 1:=by
    intro r hr
    exact ⟨(m.R_bounds lo).1.trans_lt hr.1,hr.2.trans_le (m.R_bounds hi).2⟩
  have hscale : ∀r∈A,lo ≤ a.alpha.val.val r ∧ a.alpha.val.val r ≤ hi:=by
    intro r hr
    exact (m.massSlice_profile_mem hloHigh hhiHigh hr).imp le_of_lt le_of_lt
  have hcap:=P.local_cap_contact_thermal_of_finite_budgets_above_wall A hA hAD hU hstart hwall hO hB hscale
    (by
      intro F j
      let v:=a.data.U*(2:ℝ)^(j.val:ℕ)
      have hv:=(comparison_mass_dyadic_scale a.data.hU j.val).1
      have hv1:=(comparison_mass_dyadic_scale a.data.hU j.val).2.2
      have hstartV : a.data.s < v/2:=by dsimp only [v];linarith [j.property.1]
      rw [P.ordinaryGroup_eq_retainedSupport (P.capFamily F) A (by norm_num : (1:ℝ) ≤ 16)
        j.val hv1 hstartV]
      have HP:=hnO a hs hsxs P hclock F A v Lside cut hv hv1 hstartV hLside hcut hlogcut
      exact HP.trans (hOrd v j.property hv hv1))
    (by
      intro F p
      let cap:=P.capFamily F p.val.1.val
      let f:=actualBroadCapSampler (P.capFamily F) p.val.1
      let i:=p.val.2
      let v:=f.scale i
      let l:=m.R (f.node i.val)
      let z:=m.R (f.node (i.val+1))
      have hg:=f.geometry i
      have hn:=f.nodes_mem i
      have hc:=f.contracts i
      have hw:=f.width_bounds i
      have hvs:=relevant_broad_slice_scale_bounds (P.capFamily F) A hscale p
      have hv : 0 < v:=(massCoverBase_pos (a:=a)).trans_le hg.1
      have hv1 : v ≤ 1:=hw.1.trans hw.2.2
      have hsV : a.data.s < v/2:=by dsimp only [v] at *;linarith [hvs.1]
      have hUv : a.data.U ≤ v:=(le_max_left _ _).trans hg.1
      have hnode : a.data.s < f.node i.val:=hsV.trans_le hg.2.2.1
      have hl0 : 0 < l:=by
        have H:=m.R_strictMonoOn ⟨le_rfl,a.data.hs1⟩ hn.1 hnode
        simpa only [m.R_left] using H
      have hlz : l < z:=m.R_strictMonoOn hn.1 hn.2 hg.2.2.2.2.2.2
      have hclL : cap.left ≤ l:=by
        have H:=m.R_monotone ((le_max_left _ _).trans hg.2.2.2.2.1)
        rw [m.R_inverse ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩] at H
        exact H
      have hzcap : z ≤ cap.right:=by
        have H:=m.R_monotone hg.2.2.2.2.2.1
        rw [m.R_inverse ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩] at H
        exact H
      have hlmass : v/2 ≤ a.alpha.val.val l:=by rw [m.R_spec hn.1];exact hg.2.2.1
      have hzmass : a.alpha.val.val z  ≤  min (4*v) 1:=by
        rw [m.R_spec hn.2]
        exact le_min hg.2.2.2.1 hn.2.2
      change (∫u in 0..1,(Ioo l z).indicator (fun _=>1) (m.R u)*m.thermal u) ≤ B
      rw [m.binary_thermal_pullback hl0 (hzcap.trans cap.hright) (Ioo l z)
        measurableSet_Ioo (Subset.refl _) _ (m.thermal_mask_integrable _ measurableSet_Ioo)]
      have hparent : 2*cu*(Az+1)*a.xs≤a.alpha.val.val cap.right:=by
        obtain ⟨r,hrA,hrs⟩:=p.property
        have hrparent:=hc.2.2.2.1 hrs
        exact houter.trans ((hscale r hrA).1.trans (a.alpha.val.property.2 hrparent.2.le))
      have HP:=hnB a hs hsxs P cap l z v Lside cut (P.capFamily_contacts F p.val.1.val)
        (by simpa only [one_mul] using (hnT a).1) hparent hl0 hlz hclL hzcap hv hv1 hsV hUv hlmass hzmass hc.2.2.2.2.2
        hLside hcut hcutU hlogcut
      exact HP.trans (hBroad v hvs hv hv1 _ ⟨hw.1,hw.2.1⟩ hw.2.2))
  have hloPos : 0<lo:=a.data.hU.trans_le hU
  have hrloPos : 0<lo/cu:=div_pos hloPos hcu
  have hcu1 : 1≤cu:=by
    have H:=(a.regular 1 ⟨a.hz.2,le_rfl⟩).2
    simpa only [a.alpha.property.2.1,mul_one] using H
  have hrlo1 : lo/cu≤1:=(div_le_one hcu).mpr (hlo.2.trans hcu1)
  have hthreshold : cu*Az*a.xs<lo:=by
    have H : 0<cu*(Az+2)*a.xs:=mul_pos (mul_pos hcu (by linarith)) a.hxs
    nlinarith
  have hlower : ∀r∈A,lo/cu≤r:=by
    intro r hr
    exact a.actual_mass_slab_radius_lower hcu hthreshold (Ioo_subset_Icc_self (hAD hr)) (hscale r hr).1
  have hfloor:=(hnF a hs hsxs P A hA hAD hi (fun r hr=>(hscale r hr).2)).2
    (lo/cu) hrloPos hrlo1 hlower
  have hsplit:=P.local_thermal_sign_partition A hA hAD
  have hid:=m.massSlice_thermal_integral hloHigh hhiHigh hlh
  rw [←hid,hsplit]
  exact add_le_add hcap hfloor

end OAI.SKFluctuations.LaplaceWindowFormalization
