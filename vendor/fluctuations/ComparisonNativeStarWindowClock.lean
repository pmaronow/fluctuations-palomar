module

public import ComparisonNativeStarContinuumSelection
public import ComparisonSignedCavityInnovationClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
namespace NativeStarBuffer

theorem actual_sampled_radius_field_increment {n : ℕ}
    (steps : List (GaussianStep (FeatureIndex n)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hzero : r 0=0) (hone : r (Fin.last (steps.length+1))=1)
    (field : GaussianStep (FeatureIndex n) → ℝ≥0)
    {N d lam mesh s t : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hmesh : ∀j:Fin (steps.length+1),r j.succ-r j.castSucc ≤ mesh)
    (hs : 0 < s) (ht : t ≤ 1) (hst : s ≤ t)
    (hprefix : ∀u∈Ioc (0:ℝ) 1,
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
    hpm.1 hqm.2 hpq
  have hdistance : t-s-mesh ≤ radiusGridPoint r t-radiusGridPoint r s := by linarith
  rw [hprefix t ⟨hs.trans_le hst,ht⟩,hprefix s ⟨hs,hs1⟩]
  apply le_trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdistance (laplaceComparisonStrength_pos d hlam _).le) (by positivity))
  convert hgain using 1 <;> ring

theorem actual_sampled_buffer_clocks {n : ℕ}
    (steps : List (GaussianStep (FeatureIndex n)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hzero : r 0=0) (hone : r (Fin.last (steps.length+1))=1)
    (field : GaussianStep (FeatureIndex n) → ℝ≥0)
    {N d lam a b eta mesh T K : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (ha : 0 < a) (heta : 0 < eta) (hetaA : eta ≤ a) (hK:1 ≤ K) (hbK:b ≤ K*a)
    (hmeshEta : mesh ≤ eta/2) (hmeshA : mesh ≤ a/8)
    (hend : b+eta ≤ 1) (hT : T ≤ 1)
    (hmesh : ∀j:Fin (steps.length+1),r j.succ-r j.castSucc ≤ mesh)
    (hprefix : ∀u∈Ioc (0:ℝ) 1,
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
    have hinc:=actual_sampled_radius_field_increment steps r hr hzero hone field
      hN hlog hd hnd hlam hld (s:=s) (t:=s+eta) hmesh (ha.trans hs.1) hst (by linarith) hprefix
    have hq:=radiusGridPoint_bounds r hr (s:=s+eta) (by rw [hzero];linarith [hs.1]) (by simpa only [hone] using hst) hmesh
    have hqmem:=radiusGridPoint_mem r hr (s+eta)
    simp only [hzero,hone] at hqmem
    have haq:a ≤ radiusGridPoint r (s+eta):=by linarith [hs.1]
    have ha1:a ≤ 1:=haq.trans hqmem.2
    have hmon:=hmono ⟨ha.le,ha1⟩ hqmem haq
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
    have hinc:=actual_sampled_radius_field_increment steps r hr hzero hone field
      hN hlog hd hnd hlam hld (s:=3*s/4) (t:=s) hmesh (by positivity : 0 < 3*s/4)
      hs1 (by linarith) hprefix
    have hq:=radiusGridPoint_bounds r hr (by simpa only [hzero] using hspos)
      (by simpa only [hone] using hs1) hmesh
    have hqmem:=radiusGridPoint_mem r hr s
    simp only [hzero,hone] at hqmem
    have haq:a ≤ radiusGridPoint r s:=by linarith [hs.1]
    have ha1:a ≤ 1:=haq.trans hqmem.2
    have hmon:=hmono ⟨ha.le,ha1⟩ hqmem haq
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

theorem completed_sampled_field_prefix (n:ℕ) (hn:0 < n) (b h:ℝ → ℝ≥0)
    (hb:MonotoneOn b (Icc (0:ℝ) 1)) (hh:MonotoneOn h (Icc (0:ℝ) 1))
    (as:List PositiveMass) (ho:MassOrdered 0 as) (j:ℕ) (hj:j ≤ as.length) :
    physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
      ((sampleClockSteps (completedPathClock n b h) 0 as).take j)=
      (h (physicalCutMass 0 (sampleClockSteps (completedPathClock n b h) 0 as) j):ℝ)-(h 0:ℝ) :=
  sampledFieldDuration_index n hn b h hb hh as ho j hj

theorem comparison_completed_radius_prefix
    {c:ℝ} {k M:ℝ → ℝ} (hc:0 < c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (α:inverseIntegralConstraints 0 0 k M) (n:ℕ) (hn:0 < n)
    (b:ℝ → ℝ≥0) (hb:MonotoneOn b (Icc (0:ℝ) 1))
    {d lam:ℝ} (hd:0 < d) (hlam:0 < lam)
    (as:List PositiveMass) (ho:MassOrdered 0 as) :
    let R:=comparisonSweepQuantile hc hk hkc hm hM α
    let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps:=sampleClockSteps (completedPathClock n b hf) 0 as
    let ha:=sampleClockSteps_ordered (completedPathClock n b hf) as ho
    let r:=physicalQuantileGrid zero_le_one zero_le_one hc hk hkc hm hM α steps ha
    ∀u∈Ioc (0:ℝ) 1,
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (radiusGridCut r u))=
        laplaceComparisonStrength d lam (radiusGridPoint r u)*radiusGridPoint r u := by
  let R:=comparisonSweepQuantile hc hk hkc hm hM α
  let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let steps:=sampleClockSteps (completedPathClock n b hf) 0 as
  let ha:=sampleClockSteps_ordered (completedPathClock n b hf) as ho
  let r:=physicalQuantileGrid zero_le_one zero_le_one hc hk hkc hm hM α steps ha
  change ∀u∈Ioc (0:ℝ) 1,_
  have hhf:MonotoneOn hf (Icc (0:ℝ) 1) := by
    apply toNNReal_monotoneOn
    intro u hu v hv huv
    have hRuv:=comparisonSweepQuantile_monotone hc hk hkc hm hM α huv
    have hRu:=comparisonSweepQuantile_bounds hc hk hkc hm hM α u
    have hRv:=comparisonSweepQuantile_bounds hc hk hkc hm hM α v
    exact ((laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).2) hRu hRv hRuv
  have h0:R 0=0:=by
    have hh:=comparisonSweepQuantile_inverse hc hk hkc hm hM α (r:=0) (by norm_num)
    simpa only [α.property.1] using hh
  intro u hu
  have hi:radiusGridCut r u ≤ as.length := by simpa only [steps,sampleClockSteps_length] using radiusGridCut_le r u
  have hh:=completed_sampled_field_prefix n hn b hf hb hhf as ho (radiusGridCut r u) hi
  let hj:Fin (steps.length+2):=⟨radiusGridCut r u,lt_of_le_of_lt (radiusGridCut_le r u) (by omega)⟩
  have hmassi:physicalCutMass 0 steps hj.val=α.val.val (r hj):=
    physicalQuantileGrid_coord zero_le_one zero_le_one hc hk hkc hm hM α steps ha hj
      (physicalCutMass_mem steps ha hj.val).1
  have hRj:R (physicalCutMass 0 steps hj.val)=r hj := by
    rw [hmassi]
    exact comparisonSweepQuantile_inverse hc hk hkc hm hM α
      (physicalQuantileGrid_mem zero_le_one zero_le_one hc hk hkc hm hM α steps ha hj)
  change physicalFieldDuration _ (steps.take (radiusGridCut r u))=_ at hh ⊢
  rw [hh]
  change ((laplaceComparisonStrength d lam (R (physicalCutMass 0 steps (radiusGridCut r u)))*
    R (physicalCutMass 0 steps (radiusGridCut r u))).toNNReal:ℝ)-
      ((laplaceComparisonStrength d lam (R 0)*R 0).toNNReal:ℝ)=_
  have hnonneg:0 ≤ laplaceComparisonStrength d lam (R (physicalCutMass 0 steps (radiusGridCut r u)))*
      R (physicalCutMass 0 steps (radiusGridCut r u)) :=
    mul_nonneg (laplaceComparisonStrength_pos d hlam _).le (comparisonSweepQuantile_bounds hc hk hkc hm hM α _).1
  rw [Real.toNNReal_of_nonneg hnonneg,h0,mul_zero,Real.toNNReal_zero,NNReal.coe_zero,sub_zero,NNReal.coe_mk]
  change laplaceComparisonStrength d lam (R (physicalCutMass 0 steps hj.val))*
    R (physicalCutMass 0 steps hj.val)=_
  rw [hRj]
  rfl

theorem comparison_completed_buffer_clocks
    {c:ℝ} {k M:ℝ → ℝ} (hc:0 < c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (α:inverseIntegralConstraints 0 0 k M) (n:ℕ) (hn:0 < n)
    (b:ℝ → ℝ≥0) (hb:MonotoneOn b (Icc (0:ℝ) 1))
    {N d lam a z eta mesh T K:ℝ} (hN:1 ≤ N) (hlog:1 ≤ Real.log N)
    (hd:0 < d) (hnd:1/N ≤ d) (hlam:0 < lam) (hld:lam ≤ d^2)
    (as:List PositiveMass) (ho:MassOrdered 0 as)
    (ha:0 < a) (heta:0 < eta) (hetaA:eta ≤ a) (hK:1 ≤ K) (hzK:z ≤ K*a)
    (hmeshEta:mesh ≤ eta/2) (hmeshA:mesh ≤ a/8) (hend:z+eta ≤ 1) (hT:T ≤ 1) :
    let R:=comparisonSweepQuantile hc hk hkc hm hM α
    let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let steps:=sampleClockSteps (completedPathClock n b hf) 0 as
    let hsteps:=sampleClockSteps_ordered (completedPathClock n b hf) as ho
    let r:=physicalQuantileGrid zero_le_one zero_le_one hc hk hkc hm hM α steps hsteps
    (∀j:Fin (steps.length+1),r j.succ-r j.castSucc ≤ mesh) →
    (∀s∈Ioc a z,eta*laplaceComparisonStrength d lam a/(24*(K+1)*Real.log N) ≤
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (radiusGridCut r (s+eta)))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (radiusGridCut r s))) ∧
    (∀s∈Icc (2*a) T,eta*laplaceComparisonStrength d lam a/(24*(K+1)*Real.log N) ≤
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (radiusGridCut r s))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩)) (steps.take (radiusGridCut r (3*s/4)))) := by
  dsimp only
  intro hmesh
  apply actual_sampled_buffer_clocks _ _ (physicalQuantileGrid_mono ..)
    (physicalQuantileGrid_first _ _ _ _ _ _ _ _ _ _ (by positivity)) (physicalQuantileGrid_last ..)
    _ hN hlog hd hnd hlam hld ha heta hetaA hK hzK hmeshEta hmeshA hend hT hmesh
  exact comparison_completed_radius_prefix hc hk hkc hm hM α n hn b hb hd hlam as ho

end NativeStarBuffer
end OAI.SKFluctuations
