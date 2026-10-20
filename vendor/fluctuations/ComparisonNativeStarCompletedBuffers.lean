module

public import ComparisonNativeStarWindowClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
namespace NativeStarBuffer

theorem eventually_comparison_completed_buffer_polynomial (p:ℕ) (Bclock:ℝ)
    {m delta gamma c1 saving Q K Cprof Ccap Fcap cFloor Ddepth:ℝ}
    (hm:0 < m) (hdelta:0 ≤ delta) (hgamma:0 < gamma) (hmargin:delta < 3*m)
    (hsaving:saving < (3*m-delta)/8-c1) (hK:1 ≤ K) (hCprof:0 ≤ Cprof)
    (hCcap:0 ≤ Ccap) (hcFloor:0 < cFloor) (hDepth:0 ≤ Ddepth) :
    ∀ᶠn:ℕ in atTop,∀{c:ℝ} {k M:ℝ → ℝ}
      (hc:0 < c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
      (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hMm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
      (α:inverseIntegralConstraints 0 0 k M) (b:ℝ → ℝ≥0) (hb:MonotoneOn b (Icc (0:ℝ) 1))
      (d lam E x xs mesh:ℝ) (as:List PositiveMass) (ho:MassOrdered 0 as),
      let R:=comparisonSweepQuantile hc hk hkc hMm hM α
      let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
      let q:=completedPathClock n b hf
      let steps:=sampleClockSteps q 0 as
      let ha:=sampleClockSteps_ordered q as ho
      ∀(w:PhysicalBandWindow n steps xs),
      0 < d → 1/(n:ℝ) ≤ d → 0 < lam → lam ≤ d^2 → lam ≤ Bclock → 0 < E →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E → E ≤ d^2/Real.sqrt n →
      0 < x → (n:ℝ)^delta*Real.sqrt n*E/Real.sqrt lam ≤ x → x ≤ w.a → 0 < xs →
      w.radius=physicalQuantileGrid zero_le_one zero_le_one hc hk hkc hMm hM α steps ha →
      (∀j:Fin (steps.length+1),w.radius j.succ-w.radius j.castSucc ≤ mesh) →
      mesh ≤ w.η/2 → mesh ≤ w.a/8 → w.b+w.η ≤ 1 → (2:ℝ)^w.depth*w.b ≤ 1 →
      w.b ≤ K*w.a → w.mass ≤ K*w.C*w.a →
      w.A ≤ comparisonCap n delta (comparisonSmallMass n E) (comparisonConstraintLength n E d) E d (Cprof*w.a) →
      0 < w.A →
      w.η=(1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength d lam w.a*w.a^4)))*w.a →
      w.D₀=w.η*laplaceComparisonStrength d lam w.a/(24*(K+1)*Real.log (n:ℝ)) →
      w.C ≤ Ccap → w.F ≤ Fcap → cFloor ≤ w.c₀ →
      (w.depth:ℝ) ≤ Ddepth*Real.log (n:ℝ) →
      (n:ℝ)^(-c1)*w.a ≤ w.mass →
      physicalRawRatio n (p+1) steps 0 xs (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id ≤ Q →
      ∀v:ℝ,w.a ≤ v → physicalBufferCenteredNorm n steps (q 0)
        (physicalWindowWeight steps 0 w.selected) (2*(p+1):ℕ) ≤ (n:ℝ)^(-saving)*v := by
  have hLcap:0 ≤ 24*(K+1):=by linarith
  have hlogevent:∀ᶠn:ℕ in atTop,1 ≤ Real.log (n:ℝ):=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_comparison_actual_buffer_polynomial p Bclock hm hdelta hgamma hmargin
    hsaving hK hCprof hCcap hcFloor hDepth hLcap,
    eventually_gt_atTop (1:ℕ),hlogevent] with n hn hn1 hlog
  intro c k M hc hk hkc hMm hM α b hb d lam E x xs mesh as ho
  dsimp only
  intro w hd hnd hlam hld hB hE hlo hup hx hrange hxa hxs hradius hmesh hmEta hmA hend hT
    hbK hmass hAcap hA heta hD hC hF hc0 hdepth hmasslow hQ v hav
  have hN:1 ≤ (n:ℝ):=by exact_mod_cast hn1.le
  have hn0:0 < n:=zero_lt_one.trans hn1
  have hlog0:0 < Real.log (n:ℝ):=zero_lt_one.trans_le hlog
  let R:=comparisonSweepQuantile hc hk hkc hMm hM α
  let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q:=completedPathClock n b hf
  let steps:=sampleClockSteps q 0 as
  let ha:=sampleClockSteps_ordered q as ho
  let field:GaussianStep (FeatureIndex n) → ℝ≥0:=fun st=>st.2 (Sum.inl ⟨0,hn0⟩)
  have hhf:MonotoneOn hf (Icc (0:ℝ) 1):=by
    apply toNNReal_monotoneOn
    intro u hu v hv huv
    exact (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).2
      (comparisonSweepQuantile_bounds hc hk hkc hMm hM α u)
      (comparisonSweepQuantile_bounds hc hk hkc hMm hM α v)
      (comparisonSweepQuantile_monotone hc hk hkc hMm hM α huv)
  have hclock:=comparison_completed_buffer_clocks hc hk hkc hMm hM α n hn0 b hb hN hlog
    hd hnd hlam hld as ho (hx.trans_le hxa) w.η_pos w.η_le hK hbK hmEta hmA hend hT
  dsimp only [R,hf,q,steps,ha,field] at hclock
  rw [←hradius] at hclock
  have hpair:=hclock hmesh
  have hfirst:∀s∈Ioc w.a w.b,w.D₀ ≤ physicalFieldDuration field
      (steps.take (radiusGridCut w.radius (s+w.η)))-
        physicalFieldDuration field (steps.take (radiusGridCut w.radius s)):=by
    simpa only [hD,field,steps,q,hf,R] using hpair.1
  have hdyad:∀s∈Icc (2*w.a) ((2:ℝ)^w.depth*w.b),w.D₀ ≤ physicalFieldDuration field
      (steps.take (radiusGridCut w.radius s))-
        physicalFieldDuration field (steps.take (radiusGridCut w.radius (3*s/4))):=by
    simpa only [hD,field,steps,q,hf,R] using hpair.2
  have hfield:∀st∈steps,∀i:Fin n,st.2 (Sum.inl i)=field st:=
    sampledFieldClock_aligned n hn0 b hf as 0
  have htotal:physicalFieldDuration field steps ≤ Bclock:=by
    have hh:=sampledFieldDuration_index n hn0 b hf hb hhf as ho as.length le_rfl
    dsimp only at hh
    have ht:List.take as.length (sampleClockSteps (completedPathClock n b hf) 0 as)=
        sampleClockSteps (completedPathClock n b hf) 0 as:=by
      apply List.take_of_length_le
      simp only [sampleClockSteps_length]
      exact le_rfl
    rw [ht] at hh
    change physicalFieldDuration field steps=_ at hh
    rw [hh]
    have hRbounds:=comparisonSweepQuantile_bounds hc hk hkc hMm hM α (physicalCutMass 0 steps as.length)
    have hg:=laplaceComparisonStrength_le d hlam.le (R (physicalCutMass 0 steps as.length))
    have hnonneg:0 ≤ laplaceComparisonStrength d lam (R (physicalCutMass 0 steps as.length))*
      R (physicalCutMass 0 steps as.length):=mul_nonneg (laplaceComparisonStrength_pos d hlam _).le hRbounds.1
    change ((laplaceComparisonStrength d lam (R (physicalCutMass 0 steps as.length))*
      R (physicalCutMass 0 steps as.length)).toNNReal:ℝ)-(hf 0:ℝ) ≤ Bclock
    rw [Real.toNNReal_of_nonneg hnonneg,NNReal.coe_mk]
    have hmul:=mul_le_mul hg hRbounds.2 hRbounds.1 hlam.le
    nlinarith [NNReal.coe_nonneg (hf 0)]
  let L:=24*(K+1)*Real.log (n:ℝ)
  have hL:0 < L:=by dsimp [L];positivity
  have hclockfloor:(1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength d lam w.a*w.a^4)))*w.a*
      laplaceComparisonStrength d lam w.a/L ≤ w.D₀:=by rw [←heta,hD]
  exact hn steps ha (q 0) xs hxs w field d lam E x L v hd hlam hld hE hlo hup hx hrange hxa
    hAcap hfield htotal hfirst hdyad hQ hbK hmass hL hA heta hclockfloor hC hF hc0 hlog hdepth
    le_rfl hmasslow hav

end NativeStarBuffer
end OAI.SKFluctuations
