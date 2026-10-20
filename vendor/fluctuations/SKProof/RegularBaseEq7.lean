module

public import SKProof.RegularEq7Inner
public import SKProof.RegularEq7Budget
public import SKProof.RegularEq7OuterSource
public import SKProof.RegularEq7Floor
public import SKProof.OriginalQGateAssembly
public import ComparisonOriginalQEq7DeterministicErrorCoreDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum OriginalQLocalSharpReductionDraft
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem regular_density_of_parts
    (P : Q.Potential) {C Binner Outer Prefix Floor Rinner : ℝ}
    (hC : 24 ≤ C)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hInnerFinite :
      ∀ F : Finset (ordConnectedSection P.negativeSet),
        Q.lam*(∑p : Eq7InnerCoverPiece
            (P.capFamily F) (min (C*Q.xs) 1),
          eq7InnerThermalPiece (P.capFamily F)
            (min (C*Q.xs) 1) p) ≤ Binner)
    (hOuterTail :
      (∫u in min (C*Q.xs) 1..1,
        (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ Outer)
    (hPrefix :
      (∫u in (0:ℝ)..Q.eq7InnerPrefixEnd,
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ Prefix)
    (hRadius :
      16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*
        (min (C*Q.xs) 1-Q.eq7InnerPrefixEnd) ≤ Rinner)
    (hFloor :
      (∫u in Q.eq7InnerPrefixEnd..1,
        P.positiveSet.indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤ Floor)
    (hBudget :
      Prefix+3*Binner+Rinner+Outer+Floor ≤
        Q.data.N^(10*delta)*Q.data.E) :
    Q.data.thetaZeroOriginalSweepDensity Q.lam Q.alpha ≤
      Q.data.N^(10*delta)*Q.data.E := by
  let h := min (C*Q.xs) 1
  let F := P.negativeSet ∪ P.contactSet
  let e := fun u => F.indicator (fun _ => (1:ℝ))
    (Q.shiftedNativeModel.R u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u
  let t := fun u => F.indicator (fun _ => (1:ℝ))
    (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u
  let T := ∫u in 0..1,
    (Q.shiftedNativeModel.massSlice Q.eq7InnerPrefixEnd h ∩ F).indicator
      (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
      Q.shiftedNativeModel.thermal u
  have hprefix : Q.eq7InnerPrefixEnd ≤ h :=
    eq7_regular_prefix_le_inner_cut_draft Q hC hUA
  have hhi : h ≤ 1 := min_le_right _ _
  have h0 : 0 < h := by
    have hC0 : 0 < C := by linarith only [hC]
    exact lt_min (mul_pos hC0 Q.hxs) zero_lt_one
  have hF : MeasurableSet F :=
    P.negativeSet_open.measurableSet.union P.contactSet_measurable
  have hpMass : Q.eq7InnerPrefixEnd ∈ Icc Q.data.s 1 :=
    ⟨Q.eq7_inner_s_le_prefix_end,Q.eq7_inner_prefix_end_le_one⟩
  have hhMass : h ∈ Icc Q.data.s 1 :=
    ⟨hpMass.1.trans hprefix,hhi⟩
  have hTmass : T = ∫u in Q.eq7InnerPrefixEnd..h,t u :=
    Q.shiftedNativeModel.massSlice_thermal_mask_integral
      hpMass hhMass hprefix F hF
  have hTweighted : Q.lam*T ≤ Binner :=
    P.eq7_inner_post_weighted_thermal_of_finite_piece_prices_draft
      hprefix hhi hInnerFinite
  have hInnerCmp := P.eq7_inner_cap_contact_error_le_thermal
    hpMass.1 hprefix hhi
  dsimp only at hInnerCmp
  change (∫u in Q.eq7InnerPrefixEnd..h,e u) ≤
    3*Q.lam*(∫u in Q.eq7InnerPrefixEnd..h,t u)+
      16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*
        (h-Q.eq7InnerPrefixEnd) at hInnerCmp
  rw [←hTmass] at hInnerCmp
  have hInner : (∫u in Q.eq7InnerPrefixEnd..h,e u) ≤
      3*Binner+Rinner := by
    have Hmul := mul_le_mul_of_nonneg_left hTweighted
      (by norm_num : (0:ℝ) ≤ 3)
    dsimp only [e,F,T] at hInnerCmp Hmul ⊢
    linarith only [hInnerCmp,Hmul,hRadius]
  have hiOuter : IntervalIntegrable e volume h 1 :=
    (Q.error_mask_intervalIntegrable F hF).mono_set (by
      rw [uIcc_of_le hhi,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc h0.le le_rfl)
  have hOuter : (∫u in h..1,e u) ≤ Outer := by
    simpa only [e,F,h] using hOuterTail
  have hiInner : IntervalIntegrable e volume Q.eq7InnerPrefixEnd h :=
    (Q.error_mask_intervalIntegrable F hF).mono_set (by
      rw [uIcc_of_le hprefix,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (Q.data.hs.1.le.trans hpMass.1) hhi)
  have haddNon := intervalIntegral.integral_add_adjacent_intervals
    hiInner hiOuter
  have hiPrefix := Q.error_intervalIntegrable.mono_set (by
    rw [uIcc_of_le (Q.data.hs.1.le.trans hpMass.1),
      uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hpMass.2)
  have hiPost := Q.error_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hpMass.2,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (Q.data.hs.1.le.trans hpMass.1) le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hiPrefix hiPost
  have hSign := P.eq7_error_sign_partition_on_band
    hpMass.1 hpMass.2 le_rfl
  rw [Q.data.theta_zero_density_eq_error_integral,←hadd,hSign,
    ←haddNon]
  dsimp only [e,F,h] at hInner hOuter hBudget ⊢
  linarith only [hPrefix,hInner,hOuter,hFloor,hBudget]

theorem regular_density_of_component_rates
    (P : Q.Potential)
    {C Kprefix Rcoeff Kinner Kouter Wouter Kfloor : ℝ}
    (hC : 24 ≤ C)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hInnerFinite :
      ∀ F : Finset (ordConnectedSection P.negativeSet),
        Q.lam*(∑p : Eq7InnerCoverPiece
            (P.capFamily F) (min (C*Q.xs) 1),
          eq7InnerThermalPiece (P.capFamily F)
            (min (C*Q.xs) 1) p) ≤
          Kinner*(Real.log Q.data.N)^6*
            Q.data.N^(3*delta)*Q.data.E)
    (hOuterTail :
      (∫u in min (C*Q.xs) 1..1,
        (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
        Kouter*(Real.log Q.data.N)^9*
          Q.data.N^(-delta/2)*Q.data.E+
        Wouter*(Real.log Q.data.N)^4*
          Q.data.N^(-3*m-2*delta)*Q.data.E)
    (hPrefix :
      (∫u in (0:ℝ)..Q.eq7InnerPrefixEnd,
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      Kprefix*Q.data.N^(2*delta)*Q.data.E)
    (hRadius :
      16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*
        (min (C*Q.xs) 1-Q.eq7InnerPrefixEnd) ≤
      Rcoeff*Q.data.N^(2*delta)*Q.data.E)
    (hFloor :
      (∫u in Q.eq7InnerPrefixEnd..1,
        P.positiveSet.indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      Kfloor*Q.data.N^delta*Q.data.E)
    (hScalar :
      (Kprefix+Rcoeff)*Q.data.N^(2*delta)*Q.data.E+
        3*Kinner*(Real.log Q.data.N)^6*
          Q.data.N^(3*delta)*Q.data.E+
        Kouter*(Real.log Q.data.N)^9*
          Q.data.N^(-delta/2)*Q.data.E+
        Wouter*(Real.log Q.data.N)^4*
          Q.data.N^(-3*m-2*delta)*Q.data.E+
        Kfloor*Q.data.N^delta*Q.data.E ≤
      Q.data.N^(10*delta)*Q.data.E) :
    Q.data.thetaZeroOriginalSweepDensity Q.lam Q.alpha ≤
      Q.data.N^(10*delta)*Q.data.E := by
  apply regular_density_of_parts P
    hC hUA hInnerFinite hOuterTail hPrefix hRadius hFloor
  linarith only [hScalar]

theorem eventually_regular_density
    {m cl cu C0 D Bclock : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m (m/10000) cl cu 2 C0 1 D Bclock,
        Q.data.E = wallHighError m (n+1) →
        Q.data.d = wallHighD m (n+1) →
        Q.data.s = wallHighMass m (n+1) →
        Q.xs = comparisonConditionalScale Q.data.N (m/10000) Q.data.E Q.lam →
        Q.data.N^(-(10:ℝ)) ≤ Q.lam →
        Q.xs < 1 → Q.z = min (2*Q.xs) 1 →
        Q.data.thetaZeroOriginalSweepDensity Q.lam Q.alpha ≤
          Q.data.N^(10*(m/10000))*Q.data.E := by
  let delta := m/10000
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hroom : delta < 3*m := by dsimp [delta]; linarith only [hm]
  let C := max 24 (max (2*cu*(2+1)) (max (2*cu/cl) (8*cu/cl+1)))
  let K := max 4 (4*cu/cl)
  have hC : 24 ≤ C := le_max_left _ _
  have hCouter : 2*cu*(2+1) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCU : 2*cu/cl ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCs : 8*cu/cl < C := lt_of_lt_of_le (by linarith)
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hK : 4 ≤ K := le_max_left _ _
  have hKcap : 4*cu/cl ≤ K := le_max_right _ _
  obtain ⟨ellInner, _hellInner, _horderInner, Kinner, hKinner, Hinner⟩ :=
    eventually_regular_inner_family (Az:=2) (Ct:=1) (D:=D) Bclock C
      hm hdelta hroom hcl hcu (by norm_num) hC0 (by norm_num) (by linarith only [hC])
  obtain ⟨Kprefix, hKprefix, Hprefix⟩ := eventually_regular_prefix
    (Az:=2) (Ct:=1) (D:=D) (Bclock:=Bclock)
    hm hdelta hroom hcl hcu (by norm_num) hC0 (by norm_num)
  have Hradius := eventually_regular_inner_radius
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=2) (C0:=C0)
    (Ct:=1) (D:=D) (Bclock:=Bclock) hC hdelta
  obtain ⟨ellOuter, hellOuter, horderOuter⟩ :=
    exists_comparison_reverse_moment_order
      (T:=delta+(1:ℝ)/3+20*m+1) (show 0 < delta/2 by positivity)
  obtain ⟨q, hq, Hsource⟩ := exists_regular_outer_local_source_at_cut
    ellOuter hellOuter Bclock (Az:=2) (Ct:=1) (D:=D) (C:=C) (K:=K) hm hcl hcu (by norm_num) hC0 (by norm_num)
      hC hCouter hCU hCs hK hKcap
  have Htail := eventually_original_q_outer_five_atom_two_rate_tail_corrected_c0
    m cl cu 2 C0 K hm hmmax hcl hcu (by norm_num) hC0 hK
      ellOuter hellOuter horderOuter q hq
  let Kouter := outerTailPriceConstant C0 cl cu 2 K q
  let Wouter := outerTailTravelConstant C0 cu
  have hKouter : 0 ≤ Kouter := outerTailPriceConstant_nonneg hC0 hcl (by norm_num) hK
  have hWouter : 0 ≤ Wouter := outerTailTravelConstant_nonneg hC0
  obtain ⟨Kfloor, hKfloor, Hfloor⟩ := eventually_regular_full_floor
    (D:=D) Bclock hm hdelta hroom hcl hcu hC0
  have Hbudget := eventually_four_quarter_scalar_budget_draft
    hm hdelta hKprefix.le (show 0 ≤ 64*C by linarith only [hC])
      hKinner hKouter hWouter hKfloor.le
  have Hsmall := ActualThetaZeroOverlapMinimum.eventually_small_mass_le_xs
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=2) (Ct:=1) (D:=D)
    (Bclock:=Bclock) hm hC0
  have Hcap := eventually_original_q_constraint_length_lower_draft
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=2) (Ct:=1) (D:=D)
    (Bclock:=Bclock) hm.le hC0
  have Hdepth := (tendsto_add_atTop_nat 1).eventually
    (eventually_comparisonLowerScale_depth hC0 hm)
  have HN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hlog := HN.eventually (Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1))
  filter_upwards [Hinner, Hprefix, Hradius, Hsource, Htail, Hfloor,
      Hbudget, Hsmall, Hcap, Hdepth, Hlog]
    with n hnInner hnPrefix hnRadius hnSource hnTail hnFloor hnBudget hnSmall hnCap hnDepth hnLog
  intro Q hE hd hs hcarrier hlamFloor hregular hz
  let P : Q.Potential := Classical.choice Q.exists_potential
  have hUA := hnSmall Q
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_pos n
  have hnd : 1/Q.data.N ≤ Q.data.d := by
    have HD := hnDepth Q.data.E Q.data.d Q.data.hE Q.data.hd Q.hlower
    have HS : comparisonLowerScale Q.data.N Q.data.E Q.data.d ≤ Q.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ Q.data.hd).mpr (by simpa only [pow_two] using Q.hupper)
    exact HD.trans HS
  have hlog : 1 ≤ Real.log Q.data.N := hnLog
  have hUN : 1/Q.data.N ≤ comparisonSmallMass Q.data.N Q.data.E := by
    have H := (hnCap Q).trans (min_le_left _ _)
    simpa only [Real.rpow_neg Q.data.hN.le, Real.rpow_one, one_div] using H
  have hU1 : comparisonSmallMass Q.data.N Q.data.E ≤ 1 :=
    Q.data.hsmall.trans Q.data.hd1
  let h := min (C*Q.xs) 1
  have h0 : 0 < h := lt_min (mul_pos (by linarith only [hC]) Q.hxs) zero_lt_one
  have h1 : h ≤ 1 := min_le_right _ _
  have houter : (∫ u in h..1,
      (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      Kouter*(Real.log Q.data.N)^9*Q.data.N^(-delta/2)*Q.data.E+
      Wouter*(Real.log Q.data.N)^4*Q.data.N^(-3*m-2*delta)*Q.data.E := by
    by_cases hterminal : h = 1
    · rw [hterminal, intervalIntegral.integral_same]
      have hL : 0 ≤ Real.log Q.data.N := zero_le_one.trans hlog
      positivity [Q.data.hN.le, Q.data.hE.le]
    · have hcut : min (C*Q.xs) 1 < 1 := lt_of_le_of_ne h1 hterminal
      obtain ⟨hgate, _hUgate, hstart⟩ := eq7_regular_outer_start_gates_draft Q
        hcl hcu (by norm_num) hCouter hCU hCs hUA hcut (le_refl h)
      have hcutlog : Real.log (1/h) ≤ Real.log Q.data.N := by
        have hCA : C*Q.xs < 1 := by
          by_contra H
          exact hterminal (min_eq_right (le_of_not_gt H))
        dsimp only [h]
        rw [min_eq_left hCA.le]
        exact floor_tail_log_cut_of_regular_carrier_draft hN (by linarith only [hC]) hUA
      have hi := (Q.error_mask_intervalIntegrable (P.negativeSet ∪ P.contactSet)
        (P.negativeSet_open.measurableSet.union P.contactSet_measurable)).mono_set (by
          rw [uIcc_of_le h1, uIcc_of_le zero_le_one]
          exact Icc_subset_Icc h0.le le_rfl)
      exact hnTail Q P hE hd hs hnd hlog hU1 hUN h0 h1 hcutlog hgate hstart hi
        (hnSource Q P hUA hnd hlog)
  apply regular_density_of_component_rates P hC hUA
    (hnInner Q P hcarrier hlamFloor) houter (hnPrefix Q hcarrier hUA)
    (hnRadius Q hUA hcarrier)
    (eq7_full_positive_floor_post_prefix P (hnFloor Q P hcarrier hregular hz))
  simpa only [ActualHighWallData.N, Nat.cast_add, Nat.cast_one, delta] using
    hnBudget Q.data.E Q.data.hE.le

private theorem eventually_regular_gate_producer_succ
    {m cl cu C0 D Bclock : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a : ActualHighWallData (n+1) (m/10000))
        (_hE : a.E = wallHighError m (n+1))
        (_hd : a.d = wallHighD m (n+1))
        (_hs : a.s = wallHighMass m (n+1))
        (_hdD : a.d ≤ D)
        (_hupper : Real.sqrt a.N*a.E ≤ a.d^2)
        (_hlower : a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
        (_hclock : a.T ≤ Bclock)
        (lam : ℝ)
        (hlam : lam ∈ Ioo (((n+1:ℕ):ℝ)^(-(10:ℝ))) (a.d^2)),
        ((n+1:ℕ):ℝ)^(10*(m/10000))*a.E < 2*lam →
        comparisonConditionalScale a.N (m/10000) a.E lam < 1 →
        ∀ alpha : a.Profile,
          GlobalSweepMinimum a lam hlam alpha →
          BaseRegular a cl cu lam alpha →
          a.thetaZeroOriginalSweepDensity lam alpha ≤
            ((n+1:ℕ):ℝ)^(10*(m/10000))*a.E := by
  filter_upwards [eventually_regular_density (D:=D) (Bclock:=Bclock)
    hm hmmax hcl hcu hC0] with n hn
  intro a hE hd hs hdD hupper hlower hclock lam hlam _hunresolved hregular alpha hminimum hbase
  have hlam0 : 0 < lam := (Real.rpow_pos_of_pos a.hN _).trans hlam.1
  obtain ⟨hsA, hrA⟩ := concrete_original_q_selected_origin_gates
    hm (Nat.succ_pos n) a hE hd hs hlam0 hlam.2.le
  obtain ⟨Q, hdata, hQlam, hQalpha, hQxs, hQz⟩ :=
    a.theta_zero_regular_scale_carrier (m:=m) (cl:=cl) (cu:=cu)
      (Az:=2) (C0:=C0) (Ct:=1) (D:=D) (Bclock:=Bclock)
      lam hlam0 hlam.2.le alpha hminimum (by positivity) hsA hrA
      hdD hupper hlower hclock (by norm_num) (by norm_num) hbase
  have hcarrier : Q.xs = comparisonConditionalScale Q.data.N (m/10000) Q.data.E Q.lam := by
    rw [hdata, hQlam]
    exact hQxs
  have hFloor : Q.data.N^(-(10:ℝ)) ≤ Q.lam := by
    rw [hdata, hQlam]
    exact hlam.1.le
  have hA : Q.xs < 1 := by rw [hQxs]; exact hregular
  have hz : Q.z = min (2*Q.xs) 1 := by rw [hQz, hQxs]
  have hQE : Q.data.E = wallHighError m (n+1) := by rw [hdata]; exact hE
  have hQd : Q.data.d = wallHighD m (n+1) := by rw [hdata]; exact hd
  have hQs : Q.data.s = wallHighMass m (n+1) := by rw [hdata]; exact hs
  have HQ := hn Q hQE hQd hQs hcarrier hFloor hA hz
  cases hdata
  cases hQlam
  cases hQalpha
  exact HQ

theorem eventually_regular_gate_producer
    {m cl cu C0 D Bclock : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (a : ActualHighWallData n (m/10000))
        (_hE : a.E = wallHighError m n)
        (_hd : a.d = wallHighD m n)
        (_hs : a.s = wallHighMass m n)
        (_hdD : a.d ≤ D)
        (_hupper : Real.sqrt a.N*a.E ≤ a.d^2)
        (_hlower : a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
        (_hclock : a.T ≤ Bclock)
        (lam : ℝ)
        (hlam : lam ∈ Ioo ((n:ℝ)^(-(10:ℝ))) (a.d^2)),
        (n:ℝ)^(10*(m/10000))*a.E < 2*lam →
        comparisonConditionalScale a.N (m/10000) a.E lam < 1 →
        ∀ alpha : a.Profile,
          GlobalSweepMinimum a lam hlam alpha →
          BaseRegular a cl cu lam alpha →
          a.thetaZeroOriginalSweepDensity lam alpha ≤
            (n:ℝ)^(10*(m/10000))*a.E := by
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (eventually_regular_gate_producer_succ (D:=D) (Bclock:=Bclock) hm hmmax hcl hcu hC0)
  filter_upwards [eventually_ge_atTop (N+1)] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  exact hN k (by omega)

theorem eventually_regularGate
    {m cl cu C0 D Bclock : ℝ}
    (hm : 0 < m) (hmmax : m < 1/300)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0) :
    ∀ᶠ n : ℕ in atTop, ∀ a : ActualHighWallData n (m/10000),
      a.E = wallHighError m n → a.d = wallHighD m n → a.s = wallHighMass m n →
      a.d ≤ D → Real.sqrt a.N*a.E ≤ a.d^2 →
      a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E → a.T ≤ Bclock →
      ∀ (lam : ℝ) (hlam : lam ∈ Ioo ((n:ℝ)^(-(10:ℝ))) (a.d^2)),
        (n:ℝ)^(10*(m/10000))*a.E < 2*lam →
        comparisonConditionalScale a.N (m/10000) a.E lam < 1 →
        ∀ alpha : a.Profile, GlobalSweepMinimum a lam hlam alpha →
          BaseRegular a cl cu lam alpha →
          a.thetaZeroOriginalSweepDensity lam alpha ≤ (n:ℝ)^(10*(m/10000))*a.E := by
  exact eventually_regular_gate_producer hm hmmax hcl hcu hC0

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
