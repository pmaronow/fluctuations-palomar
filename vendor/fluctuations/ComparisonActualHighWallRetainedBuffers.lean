module

public import ComparisonActualHighWallCompletedBuffers
public import ComparisonActualHighWallRetainedRaw
public import ComparisonNativeStarMinimumRetainedBuffers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 15000000
attribute [local instance] Classical.propDecidable

theorem eventually_actual_high_wall_retained_buffer_polynomial
    (p : ℕ) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D c1 saving K Cprof Fcap Ddepth Rmacro : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmargin : delta < 3*m) (hsaving : saving < (3*m-delta)/8-c1)
    (hK : 1 ≤ K) (hCprof : 0 ≤ Cprof) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hDepth : 0 ≤ Ddepth) (hRmacro : 0 < Rmacro)
    (hFmass : 1+2*cu ≤ Fcap) (hFradius : 1+1/Rmacro ≤ Fcap) :
    ∃Craw : ℝ,0 < Craw ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀(lo hi : PositiveMass),M.data.s ≤ lo.val → lo.val < hi.val → hi.val ≤ 1 →
      let a := M.data.wallRadius M.alpha lo.val
      let b := M.data.wallRadius M.alpha hi.val
      let A := M.data.M hi.val
      let eta := (1/Real.sqrt (A*((n:ℝ)*laplaceComparisonStrength M.data.d (M.data.d^2) a*a^4)))*a
      M.xs ≤ a → M.data.rmin ≤ a/4 → M.z ≤ a/2 → 2*b ≤ 1 → b ≤ K*a →
      hi.val ≤ Cprof*a → Cprof*a ≤ 1 →
      hi.val-lo.val ≤ K*cu*a → (n:ℝ)^(-c1)*a ≤ hi.val-lo.val →
      ∀J : ℕ,1 ≤ J → Rmacro ≤ (2:ℝ)^J*a → (2:ℝ)^J*b ≤ 1 →
      (J:ℝ) ≤ Ddepth*Real.log (n:ℝ) →
      ∀v : ℝ,a ≤ v →
      ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
      ∃us : List PositiveMass,∃hus : ∀u∈us,u.val ≤ 1,lo∈us ∧ hi∈us ∧ (∀u∈extra,u∈us) ∧
        ∀ᶠj : ℕ in atTop,
          let as := finiteCutMasses us j
          let q := completedPathClock n M.bf M.hf
          let steps := sampleClockSteps q 0 as
          let radius := physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc
            M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha steps
            (sampleClockSteps_ordered q as (finiteCutMasses_ordered us hus j))
          ∃w : PhysicalBandWindow n steps M.xs,
            w.radius=radius ∧
            w.selected=physicalIntervalCells steps
              (physicalRetainedIndex steps lo.val).val (physicalRetainedIndex steps hi.val).val ∧
            w.a=a ∧ w.b=b ∧ w.mass=hi.val-lo.val ∧ w.A=A ∧ w.η=eta ∧
            w.D₀=eta*laplaceComparisonStrength M.data.d (M.data.d^2) a/(24*(K+1)*Real.log (n:ℝ)) ∧
            w.c₀=cl/2 ∧ w.C=cu ∧ w.R=Rmacro ∧ w.F=Fcap ∧ w.depth=J ∧
            physicalBufferCenteredNorm n steps (q 0)
              (physicalWindowWeight steps 0 w.selected) (2*(p+1):ℕ) ≤ (n:ℝ)^(-saving)*v := by
  obtain ⟨Craw,hCraw,hraw⟩ := eventually_actual_high_wall_original_boundary_raw
    p Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt
  let Rcap := (2*(Cprof+1)+(Cprof+1)^2)/((1/(Ct+1))*(1/C0)^3)
  have hsmall : ∀ᶠn : ℕ in atTop,Rcap*(n:ℝ)^(-(3*m-delta)) ≤ 1 := by
    have ht := ((tendsto_rpow_neg_atTop (by linarith : 0 < 3*m-delta)).comp
      tendsto_natCast_atTop_atTop).const_mul Rcap
    simp only [mul_zero] at ht
    exact (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))).mono (fun _ h=>h.le)
  have hlogevent : ∀ᶠn : ℕ in atTop,1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  refine ⟨Craw,hCraw,?_⟩
  filter_upwards [hraw,eventually_actual_high_wall_completed_buffer_polynomial p Bclock hm hdelta.le
    hC0 hCt hmargin hsaving hK hCprof hcl hcu.le hDepth,
    eventually_actual_high_wall_star_cap_saving Bclock hm hC0 hCt hCprof,
    hsmall,hlogevent,eventually_ge_atTop (1:ℕ)] with n hnraw hbuf hcap hsmalln hlog hn1
  intro M lo hi hlohigh hlohi hhi
  dsimp only
  intro hxa hwall hza hroom hba hhic hca hmassupper hmasslower J hJ hreach hdyad hJlog v hav extra hextra
  let a := M.data.wallRadius M.alpha lo.val
  let b := M.data.wallRadius M.alpha hi.val
  let A := M.data.M hi.val
  let den := (n:ℝ)*laplaceComparisonStrength M.data.d (M.data.d^2) a*a^4
  let eta := (1/Real.sqrt (A*den))*a
  let D0 := eta*laplaceComparisonStrength M.data.d (M.data.d^2) a/(24*(K+1)*Real.log (n:ℝ))
  have ha : 0 < a := M.hxs.trans_le hxa
  have hab : a ≤ b := M.data.wallRadius_monotone M.alpha hlohi.le
  have hb1 : b ≤ 1 := (M.data.wallRadius_bounds M.alpha hi.val).2
  have hA1 : 1 ≤ A := (Real.one_le_rpow (by exact_mod_cast hn1 : (1:ℝ) ≤ n) hdelta.le).trans
    (comparisonCap_ge_rpow M.data.hN M.data.hE M.data.hd hi.property.le)
  have hden : 0 < den := by dsimp only [den]; positivity [M.data.hN,
    laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) a]
  have hAcap : A ≤ M.data.M (Cprof*a) :=
    M.data.hm ⟨hi.property.le,hhi⟩ ⟨by positivity,hca⟩ hhic
  have hratio : A/den ≤ 1 :=
    ((div_le_div_of_nonneg_right hAcap hden.le).trans (hcap M a hxa (hab.trans hb1))).trans hsmalln
  have hetas := balanced_buffer_radius_le hA1 hden ha hratio
  have heta : 0 < eta := hetas.1
  have hetaa : eta ≤ a := hetas.2
  have hD0 : 0 < D0 := by dsimp only [D0]; positivity [laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) a]
  have hend : b+eta ≤ 1 := by linarith
  obtain ⟨us,hus,hlous,hret,hfinite⟩ := hnraw M lo (hlohi.le.trans hhi) (hi::extra)
    (by intro u hu;rcases List.mem_cons.mp hu with rfl|hu;exact hhi;exact hextra u hu)
  have hhius : hi∈us := hret hi (by simp)
  have hextraus : ∀u∈extra,u∈us := fun u hu=>hret u (List.mem_cons_of_mem hi hu)
  refine ⟨us,hus,hlous,hhius,hextraus,?_⟩
  let mesh := min (eta/2) (a/8)
  have hmeshpos : 0 < mesh := by dsimp only [mesh]; positivity
  have hmeshlimit : ∀ᶠj : ℕ in atTop,(((j+1:ℕ):ℝ)⁻¹)/(M.data.k 1) ≤ mesh := by
    have ht := uniformMasses_mesh_tendsto.div_const (M.data.k 1)
    simp only [zero_div] at ht
    exact (ht.eventually (gt_mem_nhds hmeshpos)).mono (fun _ h=>h.le)
  filter_upwards [hfinite,hmeshlimit] with j hj hmj
  dsimp only at hj ⊢
  let as := finiteCutMasses us j
  let q := completedPathClock n M.bf M.hf
  let steps := sampleClockSteps q 0 as
  let ho := finiteCutMasses_ordered us hus j
  let hs := sampleClockSteps_ordered q as ho
  let radius := physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc
    M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha steps hs
  have hmesh : ∀k : Fin (steps.length+1),radius k.succ-radius k.castSucc ≤ mesh := by
    intro k
    exact (physicalQuantileGrid_mesh M.data.hr M.data.hs1 M.data.hc M.data.hk
      M.data.hkc M.data.hm M.data.hM M.alpha steps hs
      (sampled_physicalMass_mesh q _ (finiteCutMasses_mesh us hus j)) k).trans hmj
  have hMp : ∀u∈Icc (0:ℝ) 1,0 ≤ M.data.M u := fun u hu=>
    comparisonCap_nonneg M.data.hN M.data.hU.le M.data.hL M.data.hE M.data.hd.le hu.1
  have hloeq : M.data.wallRadius M.alpha lo.val=
      (constrainedQuantile M.data.hr M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM
        M.alpha ⟨lo.val,hlohigh,hlohi.le.trans hhi⟩:ℝ) := by
    unfold ActualHighWallData.wallRadius comparisonCalibrationConstrainedRadius
    rw [IccExtend_of_mem _ _ ⟨hlohigh,hlohi.le.trans hhi⟩]
    rfl
  have hhieq : M.data.wallRadius M.alpha hi.val=
      (constrainedQuantile M.data.hr M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM
        M.alpha ⟨hi.val,hlohigh.trans hlohi.le,hhi⟩:ℝ) := by
    unfold ActualHighWallData.wallRadius comparisonCalibrationConstrainedRadius
    rw [IccExtend_of_mem _ _ ⟨hlohigh.trans hlohi.le,hhi⟩]
    rfl
  obtain ⟨w,hradius,hselected,hwa,hwb,hwmass,hwA,hweta,hwD,hwc,hwC,hwR,hwF,hwJ⟩ :=
    retainedConstrainedWindow n q as ho M.data.hr M.data.hs1 M.data.hs.1.le M.data.hc
      M.data.hk M.data.hkc M.data.hm hMp M.alpha lo hi
      (finiteCutMasses_nodes us j hlous) (finiteCutMasses_nodes us j hhius)
      hlohigh hhi hlohi M.xs eta D0 cl cu Rmacro Fcap mesh J hcl hcu.le hD0
      hRmacro hFmass hFradius hJ hmeshpos.le hmesh
      (by simpa only [a,hloeq] using hxa)
      heta (by simpa only [a,hloeq] using hetaa)
      (by simpa only [mesh,a,hloeq] using
        (min_le_right (eta/2) (a/8)).trans (by linarith : a/8 ≤ a/2))
      (by simpa only [a,hloeq] using
        (by linarith only [ha,hwall] : M.data.rmin < a/2))
      (by simpa only [b,hhieq] using hdyad)
      (by simpa only [a,hloeq] using hreach)
      (by
        intro r hr
        apply M.regular r
        constructor
        · have H : a/2 ≤ r := by
            simpa only [a,hloeq] using hr.1
          exact hza.trans H
        · exact hr.2.trans (by simpa only [b,hhieq] using hdyad))
  have hwa' : w.a=a := by simpa only [a,hloeq] using hwa
  have hwb' : w.b=b := by simpa only [b,hhieq] using hwb
  have hrawbound : physicalRawRatio n (p+1) steps 0 M.xs
      (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id ≤ Real.sqrt (2*Craw) := by
    have H := Real.le_sqrt (physicalRawRatio_one_le n (p+1) steps 0 M.xs
      (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id |>.trans' zero_le_one)
      (by positivity : 0 ≤ 2*Craw)
    exact H.mpr hj.1
  have hmoment := hbuf M as ho (finiteCutMasses_end us hus j) w mesh v hradius
    (by rw [hradius];exact hmesh)
    (by simpa only [hwa'] using hwall)
    (by rw [hweta];exact min_le_left _ _)
    (by rw [hwa'];exact min_le_right _ _) (by simpa only [hwa',hwb',hweta] using hend)
    (by simpa only [hwb',hwJ] using hdyad) (by simpa only [hwa',hwb'] using hba)
    (by simpa only [hwmass,hwC,hwa'] using hmassupper)
    (by simpa only [hwA,hwa'] using hAcap) (by rw [hwA];exact zero_lt_one.trans_le hA1)
    (by simp only [hweta,hwA,hwa',eta,den,A])
    (by simp only [hwD,hweta,hwa',D0]) (by rw [hwC]) (by rw [hwF]) (by rw [hwc])
    (by simpa only [hwJ] using hJlog) (by simpa only [hwa',hwmass] using hmasslower)
    hrawbound (by simpa only [hwa'] using hav)
  exact ⟨w,hradius,hselected,hwa',hwb',hwmass,hwA,hweta,hwD,hwc,hwC,hwR,hwF,hwJ,hmoment⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
