module

public import SKProof.Port.ComparisonActualOriginalQPairedFarSchedule
public import ComparisonNativeInheritedCompletedBufferClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 15000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem original_full_field_radius_coe
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (M.sweepHf u:ℝ)=M.h u+(if M.data.s ≤ u then
      laplaceComparisonStrength M.data.d M.lam (M.sweepRadius u)*M.sweepRadius u else 0) := by
  rw [(M.clock_coe hu).2]
  by_cases hs : M.data.s ≤ u <;>
    simp only [sweepCoefficient, omittedStrengthCoefficient, hs, ↓reduceIte, zero_mul]

private theorem completed_quantile_radius
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let steps := sampleClockSteps (completedPathClock n M.sweepBf M.sweepHf) 0 as
    let ha := sampleClockSteps_ordered (completedPathClock n M.sweepBf M.sweepHf) as ho
    ∀ j : Fin (steps.length+2), M.sweepRadius (physicalCutMass 0 steps j.val) =
      physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc M.data.hk
        M.data.hkc M.data.hm M.data.hM M.alpha steps ha j := by
  dsimp only
  intro j
  let steps := sampleClockSteps (completedPathClock n M.sweepBf M.sweepHf) 0 as
  let ha := sampleClockSteps_ordered (completedPathClock n M.sweepBf M.sweepHf) as ho
  let mass := physicalCutMass 0 steps j.val
  have hc : M.sweepRadius mass = M.sweepRadius (max M.data.s mass) := by
    by_cases hs : M.data.s ≤ mass
    · rw [max_eq_right hs]
    · rw [max_eq_left (le_of_not_ge hs), M.sweepRadius_low (le_of_not_ge hs),
        M.sweepRadius_left]
  rw [hc]
  have Hspec := physicalQuantileGrid_spec M.data.hr M.data.hs1 M.data.hc M.data.hk
    M.data.hkc M.data.hm M.data.hM M.alpha steps ha j
  change M.alpha.val.val _ = max M.data.s mass at Hspec
  rw [←Hspec]
  exact M.sweepRadius_inverse (physicalQuantileGrid_mem M.data.hr M.data.hs1
    M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha steps ha j)

theorem original_full_completed_radius_prefix
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let steps:=sampleClockSteps (completedPathClock n M.sweepBf M.sweepHf) 0 as
    let ha:=sampleClockSteps_ordered (completedPathClock n M.sweepBf M.sweepHf) as ho
    let r:=physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc M.data.hk
      M.data.hkc M.data.hm M.data.hM M.alpha steps ha
    ∀u∈Ioc (0:ℝ) 1,
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r u))=
        (M.h (physicalCutMass 0 steps (radiusGridCut r u))-M.h 0)+
          (if M.data.s ≤ physicalCutMass 0 steps (radiusGridCut r u) then
            laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r u)*radiusGridPoint r u else 0) := by
  let steps := sampleClockSteps (completedPathClock n M.sweepBf M.sweepHf) 0 as
  let ha := sampleClockSteps_ordered (completedPathClock n M.sweepBf M.sweepHf) as ho
  let r := physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc M.data.hk
    M.data.hkc M.data.hm M.data.hM M.alpha steps ha
  dsimp only
  intro u _hu
  have hi : radiusGridCut r u ≤ as.length := by
    simpa only [steps, sampleClockSteps_length] using radiusGridCut_le r u
  have HP := completed_sampled_field_prefix n M.data.hn M.sweepBf M.sweepHf
    M.sweep_bf_monotone M.sweep_hf_monotone as ho (radiusGridCut r u) hi
  let j : Fin (steps.length+2) :=
    ⟨radiusGridCut r u, lt_of_le_of_lt (radiusGridCut_le r u) (by omega)⟩
  have hR : M.sweepRadius (physicalCutMass 0 steps (radiusGridCut r u)) = radiusGridPoint r u :=
    M.completed_quantile_radius as ho j
  have hmass := physicalCutMass_mem steps ha (radiusGridCut r u)
  change physicalFieldDuration _ (steps.take (radiusGridCut r u)) = _ at HP ⊢
  rw [HP, M.original_full_field_radius_coe hmass,
    M.original_full_field_radius_coe (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1),
    ite_eq_right (not_le.mpr M.data.hs.1), add_zero, hR]
  ring

private theorem positive_origin_sampled_radius_field_increment {n : ℕ}
    (steps : List (GaussianStep (FeatureIndex n)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (horigin : 0 ≤ r 0) (hone : r (Fin.last (steps.length+1))=1)
    (field : GaussianStep (FeatureIndex n) → ℝ≥0)
    {N d lam mesh s t : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hmesh : ∀j:Fin (steps.length+1),r j.succ-r j.castSucc ≤ mesh)
    (hs : r 0 < s) (ht : t ≤ 1) (hst : s ≤ t)
    (extra : ℝ→ℝ) (hextra : MonotoneOn extra (Ioc (0:ℝ) 1))
    (hprefix : ∀u∈Ioc (0:ℝ) 1,
      physicalFieldDuration field (steps.take (radiusGridCut r u))=
        extra u+laplaceComparisonStrength d lam (radiusGridPoint r u)*radiusGridPoint r u) :
    laplaceComparisonStrength d lam (radiusGridPoint r t)*(t-s-mesh)/(3*Real.log N) ≤
      physicalFieldDuration field (steps.take (radiusGridCut r t))-
        physicalFieldDuration field (steps.take (radiusGridCut r s)) := by
  have hs1 : s ≤ 1 := hst.trans ht
  have hp:=radiusGridPoint_bounds r hr hs
    (by simpa only [hone] using hs1) hmesh
  have hq:=radiusGridPoint_bounds r hr (hs.trans_le hst)
    (by simpa only [hone] using ht) hmesh
  have hpm:=radiusGridPoint_mem r hr s
  have hqm:=radiusGridPoint_mem r hr t
  rw [hone] at hpm hqm
  have hpm0 : 0 ≤ radiusGridPoint r s := horigin.trans hpm.1
  have hpq:=radiusGridPoint_monotone r hr hst
  have hgain:=Cavity.actual_comparison_radius_field_increment_lower hN hlog hd hnd hlam hld
    hpm0 hqm.2 hpq
  have hdistance : t-s-mesh ≤ radiusGridPoint r t-radiusGridPoint r s := by linarith
  have Hextra:=hextra ⟨horigin.trans_lt hs,hs1⟩ ⟨horigin.trans_lt (hs.trans_le hst),ht⟩ hst
  have Hbase : laplaceComparisonStrength d lam (radiusGridPoint r t)*(t-s-mesh)/(3*Real.log N)≤
      laplaceComparisonStrength d lam (radiusGridPoint r t)*radiusGridPoint r t-
        laplaceComparisonStrength d lam (radiusGridPoint r s)*radiusGridPoint r s:=by
    apply le_trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdistance (laplaceComparisonStrength_pos d hlam _).le) (by positivity))
    convert hgain using 1
    ring
  rw [hprefix t ⟨horigin.trans_lt (hs.trans_le hst),ht⟩,
    hprefix s ⟨horigin.trans_lt hs,hs1⟩]
  linarith only [Hbase,Hextra]

theorem original_full_completed_buffer_clocks
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ M.data.N) (hlog : 1 ≤ Real.log M.data.N) (hnd : 1/M.data.N ≤ M.data.d)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {a z eta mesh T K : ℝ} (ha : 0<a) (heta : 0<eta) (hetaA : eta ≤ a)
    (horigin : M.data.rmin ≤ a) (hK : 1 ≤ K) (hzK : z ≤ K*a)
    (hmeshEta : mesh ≤ eta/2) (hmeshA : mesh ≤ a/8)
    (hend : z+eta ≤ 1) (hT : T ≤ 1) :
    let steps:=sampleClockSteps (completedPathClock n M.sweepBf M.sweepHf) 0 as
    let hs:=sampleClockSteps_ordered (completedPathClock n M.sweepBf M.sweepHf) as ho
    let r:=physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc M.data.hk M.data.hkc
      M.data.hm M.data.hM M.alpha steps hs
    (∀j : Fin (steps.length+1),r j.succ-r j.castSucc ≤  mesh) →
    (∀s∈Ioc a z,eta*laplaceComparisonStrength M.data.d M.lam a/(24*(K+1)*Real.log M.data.N) ≤
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r (s+eta)))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r s))) ∧
    (∀s∈Icc (2*a) T,eta*laplaceComparisonStrength M.data.d M.lam a/(24*(K+1)*Real.log M.data.N) ≤
      physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r s))-
        physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,M.data.hn⟩)) (steps.take (radiusGridCut r (3*s/4)))) := by
  dsimp only
  intro hmesh
  let steps := sampleClockSteps (completedPathClock n M.sweepBf M.sweepHf) 0 as
  let hs := sampleClockSteps_ordered (completedPathClock n M.sweepBf M.sweepHf) as ho
  let r := physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc M.data.hk M.data.hkc
    M.data.hm M.data.hM M.alpha steps hs
  let field : GaussianStep (FeatureIndex n) → ℝ≥0 := fun st => st.2 (Sum.inl ⟨0,M.data.hn⟩)
  let originField := laplaceComparisonStrength M.data.d M.lam M.data.rmin * M.data.rmin
  let mass := fun u => physicalCutMass 0 steps (radiusGridCut r u)
  let extra := fun u => (M.h (mass u)-M.h 0) - (if M.data.s ≤ mass u then 0 else originField)
  have hmassmono : Monotone mass := fun _ _ huv =>
    physicalCutMass_monotone steps hs (radiusGridCut_monotone r huv)
  have horiginField : 0 ≤ originField :=
    mul_nonneg (laplaceComparisonStrength_pos M.data.d M.hlam _).le M.data.rmin_nonneg
  have hextra : MonotoneOn extra (Ioc (0:ℝ) 1) := by
    intro u _hu v _hv huv
    have hh := M.hh (physicalCutMass_mem steps hs _) (physicalCutMass_mem steps hs _) (hmassmono huv)
    change M.h (mass u) ≤ M.h (mass v) at hh
    dsimp only [extra]
    by_cases hsu : M.data.s ≤ mass u
    · rw [ite_eq_left hsu, ite_eq_left (hsu.trans (hmassmono huv))]
      linarith only [hh]
    · rw [ite_eq_right hsu]
      split_ifs <;> linarith only [hh, horiginField]
  have hprefix : ∀ u ∈ Ioc (0:ℝ) 1,
      physicalFieldDuration field (steps.take (radiusGridCut r u)) =
        extra u + laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r u)*radiusGridPoint r u := by
    intro u hu
    have HP := M.original_full_completed_radius_prefix as ho u hu
    change physicalFieldDuration field (steps.take (radiusGridCut r u)) =
      (M.h (mass u)-M.h 0) + (if M.data.s ≤ mass u then
        laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r u)*radiusGridPoint r u else 0) at HP
    rw [HP]
    dsimp only [extra]
    by_cases hsu : M.data.s ≤ mass u
    · simp only [ite_eq_left hsu]
      ring
    · have hR : radiusGridPoint r u = M.data.rmin :=
        (M.completed_quantile_radius as ho _).symm.trans (M.sweepRadius_low (le_of_not_ge hsu))
      simp only [ite_eq_right hsu, hR]
      dsimp only [originField]
      ring
  have hr : Monotone r := physicalQuantileGrid_mono ..
  have hfirst : r 0 = M.data.rmin := physicalQuantileGrid_first _ _ _ _ _ _ _ _ _ _ M.data.hs.1.le
  have hlast : r (Fin.last (steps.length+1)) = 1 := physicalQuantileGrid_last ..
  have hg:0 < laplaceComparisonStrength M.data.d M.lam a:=laplaceComparisonStrength_pos M.data.d M.hlam a
  have hlog0:0 < Real.log M.data.N:=zero_lt_one.trans_le hlog
  have hK1:0 < K+1:=by linarith
  have hmono:MonotoneOn (fun t=>laplaceComparisonStrength M.data.d M.lam t*t) (Icc (0:ℝ) 1):=
    (laplaceComparisonStrength_monotonicities M.data.hd.ne' M.hlam (r₀:=0) le_rfl).2
  constructor
  · intro s hs
    have hst:s+eta ≤ 1:=by linarith [hs.2]
    have hinc:=positive_origin_sampled_radius_field_increment steps r hr
      (by rw [hfirst]; exact M.data.rmin_nonneg) hlast field
      hN hlog M.data.hd hnd M.hlam M.hld (s:=s) (t:=s+eta) hmesh (by rw [hfirst]; exact horigin.trans_lt hs.1) hst (by linarith) extra hextra hprefix
    have hq:=radiusGridPoint_bounds r hr (s:=s+eta) (by rw [hfirst]; linarith [hs.1]) (by simpa only [hlast] using hst) hmesh
    have hqmem:=radiusGridPoint_mem r hr (s+eta)
    simp only [hfirst,hlast] at hqmem
    have haq:a ≤ radiusGridPoint r (s+eta):=by linarith [hs.1]
    have ha1:a ≤ 1:=haq.trans hqmem.2
    have hmon:=hmono ⟨ha.le,ha1⟩ ⟨M.data.rmin_nonneg.trans hqmem.1,hqmem.2⟩ haq
    have hgq:0 < laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r (s+eta)):=laplaceComparisonStrength_pos M.data.d M.hlam _
    have hcap:radiusGridPoint r (s+eta) ≤ (K+1)*a:=by linarith [hq.2,hs.2]
    have hprod:=mul_le_mul_of_nonneg_left hcap hgq.le
    have hga:laplaceComparisonStrength M.data.d M.lam a ≤ (K+1)*laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r (s+eta)):=by
      nlinarith
    have hgap:eta ≤ 4*(s+eta-s-mesh):=by linarith
    have hnum:=mul_le_mul_of_nonneg_left hgap hgq.le
    have hnum':eta*laplaceComparisonStrength M.data.d M.lam a ≤
        4*(K+1)*laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r (s+eta))*(s+eta-s-mesh):=by
      have hh:=mul_le_mul_of_nonneg_left hga heta.le
      have hj:=mul_le_mul_of_nonneg_left hnum hK1.le
      nlinarith
    apply le_trans _ hinc
    apply (div_le_div_iff₀ (by positivity : 0 < 24*(K+1)*Real.log M.data.N)
      (by positivity : 0 < 3*Real.log M.data.N)).mpr
    have hh:=mul_le_mul_of_nonneg_right hnum' hlog0.le
    have hn:0 ≤ laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r (s+eta))*(s+eta-s-mesh):=by
      apply mul_nonneg hgq.le
      linarith
    have hj:=mul_nonneg (mul_nonneg hK1.le hlog0.le) hn
    nlinarith
  · intro s hs
    have hspos:0 < s:=by linarith [hs.1]
    have hs1:s ≤ 1:=hs.2.trans hT
    have hinc:=positive_origin_sampled_radius_field_increment steps r hr
      (by rw [hfirst]; exact M.data.rmin_nonneg) hlast field
      hN hlog M.data.hd hnd M.hlam M.hld (s:=3*s/4) (t:=s) hmesh (by rw [hfirst]; linarith [hs.1])
      hs1 (by linarith) extra hextra hprefix
    have hq:=radiusGridPoint_bounds r hr (s:=s) (by rw [hfirst]; linarith [hs.1])
      (by simpa only [hlast] using hs1) hmesh
    have hqmem:=radiusGridPoint_mem r hr s
    simp only [hfirst,hlast] at hqmem
    have haq:a ≤ radiusGridPoint r s:=by linarith [hs.1]
    have ha1:a ≤ 1:=haq.trans hqmem.2
    have hmon:=hmono ⟨ha.le,ha1⟩ ⟨M.data.rmin_nonneg.trans hqmem.1,hqmem.2⟩ haq
    have hgq:0 < laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r s):=laplaceComparisonStrength_pos M.data.d M.hlam _
    have hgap:radiusGridPoint r s ≤ 8*(s-3*s/4-mesh):=by linarith [hs.1,hq.2]
    have hnum:=mul_le_mul_of_nonneg_left hgap hgq.le
    have hga:=mul_le_mul_of_nonneg_left hetaA hg.le
    have hnum':eta*laplaceComparisonStrength M.data.d M.lam a ≤
        8*laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r s)*(s-3*s/4-mesh):=by nlinarith
    apply le_trans _ hinc
    apply (div_le_div_iff₀ (by positivity : 0 < 24*(K+1)*Real.log M.data.N)
      (by positivity : 0 < 3*Real.log M.data.N)).mpr
    have hh:=mul_le_mul_of_nonneg_right hnum' hlog0.le
    have hn:0 ≤ laplaceComparisonStrength M.data.d M.lam (radiusGridPoint r s)*(s-3*s/4-mesh):=by
      apply mul_nonneg hgq.le
      linarith [hs.1]
    have hj:=mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ K+1) (mul_nonneg hlog0.le hn)
    nlinarith

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
