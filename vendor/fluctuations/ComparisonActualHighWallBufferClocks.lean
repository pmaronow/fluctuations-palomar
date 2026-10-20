module

public import ComparisonActualHighWallInnovation
public import ComparisonNativeStarWindowClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9000000
set_option linter.unnecessarySeqFocus false
namespace NativeStarBuffer
theorem shifted_sampled_radius_field_increment {n : ℕ}
    (steps : List (GaussianStep (FeatureIndex n)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (origin threshold : ℝ) (horigin : 0 ≤ origin) (hzero : r 0=origin) (hone : r (Fin.last (steps.length+1))=1)
    (field : GaussianStep (FeatureIndex n) → ℝ≥0)
    {N d lam mesh s t : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hmesh : ∀j:Fin (steps.length+1),r j.succ-r j.castSucc ≤ mesh)
    (hs : origin < s) (hpre : threshold < s) (ht : t ≤ 1) (hst : s ≤ t)
    (hprefix : ∀u∈Ioc threshold 1,
      physicalFieldDuration field (steps.take (radiusGridCut r u))=
        laplaceComparisonStrength d lam (radiusGridPoint r u)*radiusGridPoint r u) :
    laplaceComparisonStrength d lam (radiusGridPoint r t)*(t-s-mesh)/(3*Real.log N) ≤
      physicalFieldDuration field (steps.take (radiusGridCut r t))-
        physicalFieldDuration field (steps.take (radiusGridCut r s)) := by
  have hs1 : s ≤ 1 := hst.trans ht
  have hp:=radiusGridPoint_bounds r hr (by simpa only [hzero] using hs)
    (by simpa only [hone] using hs1) hmesh
  have hq:=radiusGridPoint_bounds r hr (by simpa only [hzero] using hs.trans_le hst)
    (by simpa only [hone] using ht) hmesh
  have hpm:=radiusGridPoint_mem r hr s
  have hqm:=radiusGridPoint_mem r hr t
  simp only [hzero,hone] at hpm hqm
  have hpq:=radiusGridPoint_monotone r hr hst
  have hgain:=Cavity.actual_comparison_radius_field_increment_lower hN hlog hd hnd hlam hld
    (horigin.trans hpm.1) hqm.2 hpq
  have hdistance : t-s-mesh ≤ radiusGridPoint r t-radiusGridPoint r s := by linarith
  rw [hprefix t ⟨hpre.trans_le hst,ht⟩,hprefix s ⟨hpre,hs1⟩]
  apply le_trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdistance (laplaceComparisonStrength_pos d hlam _).le) (by positivity))
  convert hgain using 1 <;> ring

theorem shifted_sampled_buffer_clocks {n : ℕ}
    (steps : List (GaussianStep (FeatureIndex n)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (origin threshold : ℝ) (horigin : 0 ≤ origin) (hzero : r 0=origin) (hone : r (Fin.last (steps.length+1))=1)
    (field : GaussianStep (FeatureIndex n) → ℝ≥0)
    {N d lam a b eta mesh T K : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (ha : 0 < a) (hwall : origin ≤ a/4) (hthreshold : threshold ≤ a/2) (heta : 0 < eta) (hetaA : eta ≤ a) (hK:1 ≤ K) (hbK:b ≤ K*a)
    (hmeshEta : mesh ≤ eta/2) (hmeshA : mesh ≤ a/8)
    (hend : b+eta ≤ 1) (hT : T ≤ 1)
    (hmesh : ∀j:Fin (steps.length+1),r j.succ-r j.castSucc ≤ mesh)
    (hprefix : ∀u∈Ioc threshold 1,
      physicalFieldDuration field (steps.take (radiusGridCut r u))=
        laplaceComparisonStrength d lam (radiusGridPoint r u)*radiusGridPoint r u) :
    (∀s∈Ioc a b,eta*laplaceComparisonStrength d lam a/(24*(K+1)*Real.log N) ≤
      physicalFieldDuration field (steps.take (radiusGridCut r (s+eta)))-
        physicalFieldDuration field (steps.take (radiusGridCut r s))) ∧
    (∀s∈Icc (2*a) T,eta*laplaceComparisonStrength d lam a/(24*(K+1)*Real.log N) ≤
      physicalFieldDuration field (steps.take (radiusGridCut r s))-
        physicalFieldDuration field (steps.take (radiusGridCut r (3*s/4)))) := by
  have hg:0 < laplaceComparisonStrength d lam a:=laplaceComparisonStrength_pos d hlam a
  have hlog0:0 < Real.log N:=zero_lt_one.trans_le hlog
  have hK1:0 < K+1:=by linarith
  have hmono:MonotoneOn (fun t=>laplaceComparisonStrength d lam t*t) (Icc (0:ℝ) 1):=
    (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).2
  constructor
  · intro s hs
    have hst:s+eta ≤ 1:=by linarith [hs.2]
    have hinc:=shifted_sampled_radius_field_increment steps r hr origin threshold horigin hzero hone field
      hN hlog hd hnd hlam hld (s:=s) (t:=s+eta) hmesh (by linarith only [hs.1,hwall,ha]) (by linarith only [hs.1,hthreshold,ha]) hst (by linarith) hprefix
    have hq:=radiusGridPoint_bounds r hr (s:=s+eta) (by rw [hzero];linarith [hs.1,hwall]) (by simpa only [hone] using hst) hmesh
    have hqmem:=radiusGridPoint_mem r hr (s+eta)
    simp only [hzero,hone] at hqmem
    have haq:a ≤ radiusGridPoint r (s+eta):=by linarith [hs.1]
    have ha1:a ≤ 1:=haq.trans hqmem.2
    have hmon:=hmono ⟨ha.le,ha1⟩ ⟨horigin.trans hqmem.1,hqmem.2⟩ haq
    have hgq:0 < laplaceComparisonStrength d lam (radiusGridPoint r (s+eta)):=laplaceComparisonStrength_pos d hlam _
    have hcap:radiusGridPoint r (s+eta) ≤ (K+1)*a:=by linarith [hq.2,hs.2]
    have hprod:=mul_le_mul_of_nonneg_left hcap hgq.le
    have hga:laplaceComparisonStrength d lam a ≤ (K+1)*laplaceComparisonStrength d lam (radiusGridPoint r (s+eta)):=by
      nlinarith
    have hgap:eta ≤ 4*(s+eta-s-mesh):=by linarith
    have hnum:=mul_le_mul_of_nonneg_left hgap hgq.le
    have hnum':eta*laplaceComparisonStrength d lam a ≤
        4*(K+1)*laplaceComparisonStrength d lam (radiusGridPoint r (s+eta))*(s+eta-s-mesh):=by
      have hh:=mul_le_mul_of_nonneg_left hga heta.le
      have hj:=mul_le_mul_of_nonneg_left hnum hK1.le
      nlinarith
    apply le_trans _ hinc
    apply (div_le_div_iff₀ (by positivity : 0 < 24*(K+1)*Real.log N)
      (by positivity : 0 < 3*Real.log N)).mpr
    have hh:=mul_le_mul_of_nonneg_right hnum' hlog0.le
    have hn:0 ≤ laplaceComparisonStrength d lam (radiusGridPoint r (s+eta))*(s+eta-s-mesh):=by
      apply mul_nonneg hgq.le
      linarith
    have hj:=mul_nonneg (mul_nonneg hK1.le hlog0.le) hn
    nlinarith
  · intro s hs
    have hspos:0 < s:=by linarith [hs.1]
    have hs1:s ≤ 1:=hs.2.trans hT
    have hinc:=shifted_sampled_radius_field_increment steps r hr origin threshold horigin hzero hone field
      hN hlog hd hnd hlam hld (s:=3*s/4) (t:=s) hmesh (by linarith only [hs.1,hwall,ha]) (by linarith only [hs.1,hthreshold,ha])
      hs1 (by linarith) hprefix
    have hq:=radiusGridPoint_bounds r hr (s:=s) (by rw [hzero];linarith only [hs.1,hwall,ha])
      (by simpa only [hone] using hs1) hmesh
    have hqmem:=radiusGridPoint_mem r hr s
    simp only [hzero,hone] at hqmem
    have haq:a ≤ radiusGridPoint r s:=by linarith [hs.1]
    have ha1:a ≤ 1:=haq.trans hqmem.2
    have hmon:=hmono ⟨ha.le,ha1⟩ ⟨horigin.trans hqmem.1,hqmem.2⟩ haq
    have hgq:0 < laplaceComparisonStrength d lam (radiusGridPoint r s):=laplaceComparisonStrength_pos d hlam _
    have hgap:radiusGridPoint r s ≤ 8*(s-3*s/4-mesh):=by linarith [hs.1,hq.2]
    have hnum:=mul_le_mul_of_nonneg_left hgap hgq.le
    have hga:=mul_le_mul_of_nonneg_left hetaA hg.le
    have hnum':eta*laplaceComparisonStrength d lam a ≤
        8*laplaceComparisonStrength d lam (radiusGridPoint r s)*(s-3*s/4-mesh):=by nlinarith
    apply le_trans _ hinc
    apply (div_le_div_iff₀ (by positivity : 0 < 24*(K+1)*Real.log N)
      (by positivity : 0 < 3*Real.log N)).mpr
    have hh:=mul_le_mul_of_nonneg_right hnum' hlog0.le
    have hn:0 ≤ laplaceComparisonStrength d lam (radiusGridPoint r s)*(s-3*s/4-mesh):=by
      apply mul_nonneg hgq.le
      linarith [hs.1]
    have hj:=mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ K+1) (mul_nonneg hlog0.le hn)
    nlinarith

theorem actual_high_wall_completed_buffer_clocks
    {n : ℕ} {delta : ℝ} (M : ActualHighWallData n delta) (alpha : M.Profile)
    (hN : 1 ≤ M.N) (hlog : 1 ≤ Real.log M.N) (hnd : 1/M.N ≤ M.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {a z eta mesh T K : ℝ} (ha : 0 < a) (hwall : M.rmin ≤ a/4)
    (heta : 0 < eta) (hetaA : eta ≤ a) (hK : 1 ≤ K) (hzK : z ≤ K*a)
    (hmeshEta : mesh ≤ eta/2) (hmeshA : mesh ≤ a/8) (hend : z+eta ≤ 1) (hT : T ≤ 1)
    (hmesh : ∀j : Fin ((sampleClockSteps (completedPathClock n (M.bf alpha) (M.hf alpha)) 0 as).length+1),
      let steps := sampleClockSteps (completedPathClock n (M.bf alpha) (M.hf alpha)) 0 as
      let hs := sampleClockSteps_ordered (completedPathClock n (M.bf alpha) (M.hf alpha)) as ho
      let r := physicalQuantileGrid M.hr M.hs1 M.hc M.hk M.hkc M.hm M.hM alpha steps hs
      r j.succ-r j.castSucc ≤ mesh) :
    let steps := sampleClockSteps (completedPathClock n (M.bf alpha) (M.hf alpha)) 0 as
    let hs := sampleClockSteps_ordered (completedPathClock n (M.bf alpha) (M.hf alpha)) as ho
    let r := physicalQuantileGrid M.hr M.hs1 M.hc M.hk M.hkc M.hm M.hM alpha steps hs
    let field := fun st : GaussianStep (FeatureIndex n)=>st.2 (Sum.inl ⟨0,M.hn⟩)
    (∀s∈Ioc a z,eta*M.g a/(24*(K+1)*Real.log M.N) ≤
      physicalFieldDuration field (steps.take (radiusGridCut r (s+eta)))-
        physicalFieldDuration field (steps.take (radiusGridCut r s))) ∧
    (∀s∈Icc (2*a) T,eta*M.g a/(24*(K+1)*Real.log M.N) ≤
      physicalFieldDuration field (steps.take (radiusGridCut r s))-
        physicalFieldDuration field (steps.take (radiusGridCut r (3*s/4)))) := by
  dsimp only
  let q := completedPathClock n (M.bf alpha) (M.hf alpha)
  let steps := sampleClockSteps q 0 as
  let hs := sampleClockSteps_ordered q as ho
  let r := physicalQuantileGrid M.hr M.hs1 M.hc M.hk M.hkc M.hm M.hM alpha steps hs
  let field := fun st : GaussianStep (FeatureIndex n)=>st.2 (Sum.inl ⟨0,M.hn⟩)
  have hzero : r 0=M.rmin := physicalQuantileGrid_first M.hr M.hs1 M.hc M.hk M.hkc
    M.hm M.hM alpha steps hs M.hs.1.le
  have hone : r (Fin.last (steps.length+1))=1 := physicalQuantileGrid_last ..
  have hprefix : ∀u∈Ioc (a/2) 1,
      physicalFieldDuration field (steps.take (radiusGridCut r u))=M.g (radiusGridPoint r u)*radiusGridPoint r u := by
    intro u hu
    have hpoint := radiusGridPoint_bounds r (physicalQuantileGrid_mono ..) (s:=u)
      (by rw [hzero];linarith only [hu.1,hwall,ha])
      (by rw [hone];exact hu.2) hmesh
    let j : Fin (steps.length+2) := ⟨radiusGridCut r u,
      lt_of_le_of_lt (radiusGridCut_le r u) (by omega)⟩
    have hhigh : M.rmin < r j := by
      change M.rmin < radiusGridPoint r u
      linarith only [hpoint.1,hu.1,hmeshA,hwall,ha]
    have hmass := physicalQuantileGrid_coord_of_radius M.hr M.hs1 M.hc M.hk M.hkc
      M.hm M.hM alpha steps hs j hhigh
    have hri := physicalQuantileGrid_mem M.hr M.hs1 M.hc M.hk M.hkc M.hm M.hM alpha steps hs j
    have hum := inverseConstraint_mass_mem M.hr M.hc M.hk M.hkc alpha hri
    have hp := completed_sampled_field_prefix n M.hn (M.bf alpha) (M.hf alpha)
      (M.bf_monotone alpha) (M.hf_monotone alpha) as ho (radiusGridCut r u)
      (by simpa only [steps,sampleClockSteps_length] using radiusGridCut_le r u)
    change physicalFieldDuration field (steps.take (radiusGridCut r u))=_ at hp
    rw [hp]
    rw [show physicalCutMass 0 (sampleClockSteps (completedPathClock n (M.bf alpha) (M.hf alpha)) 0 as)
      (radiusGridCut r u)=alpha.val.val (r j) from hmass,
      M.high_field_clock alpha hum,M.root_field_zero alpha,NNReal.coe_zero,sub_zero,
      M.wallRadius_inverse alpha hri]
    rfl
  exact shifted_sampled_buffer_clocks steps r (physicalQuantileGrid_mono ..)
    M.rmin (a/2) M.hrbounds.1.le hzero hone field hN hlog M.hd hnd
    (sq_pos_of_pos M.hd) le_rfl ha hwall le_rfl heta hetaA hK hzK hmeshEta
    hmeshA hend hT hmesh hprefix

end NativeStarBuffer
end OAI.SKFluctuations
