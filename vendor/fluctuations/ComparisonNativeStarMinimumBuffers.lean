module

public import ComparisonNativeStarMinimumCapSaving
public import ComparisonNativeStarCompletedBuffers
public import ComparisonSignedCavityActualMinimumResampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem eventually_actual_minimum_completed_buffer_polynomial
    (p : ℕ) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D c1 saving Q K Cprof Fcap Ddepth : ℝ}
    (hm : 0 < m) (_hdelta : 0 ≤ delta) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmargin : delta < 3*m) (hsaving : saving < (3*m-delta)/8-c1)
    (hK : 1 ≤ K) (hCprof : 0 ≤ Cprof) (hcl : 0 < cl) (hcu : 0 ≤ cu)
    (hDepth : 0 ≤ Ddepth) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      (∀u,M.h u=0) →
      ∀(as : List PositiveMass) (ho : MassOrdered 0 as),partitionEnd 0 as=1 →
      let q := completedPathClock n M.bf M.hf
      let steps := sampleClockSteps q 0 as
      let ha := sampleClockSteps_ordered q as ho
      ∀(w : PhysicalBandWindow n steps M.xs) (mesh v : ℝ),
      w.radius=physicalQuantileGrid zero_le_one zero_le_one M.context.hc
        M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha steps ha →
      (∀j : Fin (steps.length+1),w.radius j.succ-w.radius j.castSucc ≤ mesh) →
      mesh ≤ w.η/2 → mesh ≤ w.a/8 → w.b+w.η ≤ 1 →
      (2:ℝ)^w.depth*w.b ≤ 1 → w.b ≤ K*w.a → w.mass ≤ K*w.C*w.a →
      w.A ≤ M.context.M (Cprof*w.a) → 0 < w.A →
      w.η=(1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength M.context.d M.lam w.a*w.a^4)))*w.a →
      w.D₀=w.η*laplaceComparisonStrength M.context.d M.lam w.a/(24*(K+1)*Real.log (n:ℝ)) →
      w.C ≤ cu → w.F ≤ Fcap → cl/2 ≤ w.c₀ →
      (w.depth:ℝ) ≤ Ddepth*Real.log (n:ℝ) →
      (n:ℝ)^(-c1)*w.a ≤ w.mass →
      physicalRawRatio n (p+1) steps 0 M.xs
        (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id ≤ Q →
      w.a ≤ v →
      physicalBufferCenteredNorm n steps (q 0)
        (physicalWindowWeight steps 0 w.selected) (2*(p+1):ℕ) ≤ (n:ℝ)^(-saving)*v := by
  let Rcap := (2*(Cprof+1)+(Cprof+1)^2)/((1/(Ct+1))*(1/C0)^3)
  have hRcap : 0 ≤ Rcap := by dsimp only [Rcap]; positivity
  have hLcap : 0 ≤ 24*(K+1) := by linarith
  have hlogevent : ∀ᶠn : ℕ in atTop,1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_physical_buffer_polynomial_native_scale p Bclock
    (by linarith : 0 < 3*m-delta) hRcap hsaving hK hcu
    (by positivity : 0 < cl/2) hDepth hLcap,
    eventually_actual_minimum_star_cap_saving Bclock hm hC0 hCt hCprof,
    eventually_comparisonLowerScale_depth hC0 hm,hlogevent,eventually_gt_atTop (1:ℕ)]
    with n hbuf hcap hdepth hlog hn
  intro M hzero as ho he
  dsimp only
  intro w mesh v hradius hmesh hmEta hmA hend hT hbK hmass hAcap hA heta hD hC hF hc0
    hJ hmasslow hQ hav
  let q := completedPathClock n M.bf M.hf
  let steps := sampleClockSteps q 0 as
  let ha := sampleClockSteps_ordered q as ho
  have hN : 1 ≤ (n:ℝ) := by exact_mod_cast hn.le
  have hN0 : 0 < (n:ℝ) := M.context.hN
  have hn0 : 0 < n := M.context.hn
  have hwa : 0 < w.a := M.hxs.trans_le w.xa
  have hwa1 : w.a ≤ 1 := by linarith [w.ab,w.η_pos]
  have hnd : 1/(n:ℝ) ≤ M.context.d := by
    have H := hdepth M.context.E M.context.d M.context.hE M.context.hd M.hlower
    have hs : comparisonLowerScale n M.context.E M.context.d ≤ M.context.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ M.context.hd).mpr (by simpa only [pow_two] using M.hupper)
    exact H.trans hs
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  have hbf : MonotoneOn M.bf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.1
  have hhf : MonotoneOn M.hf (Icc (0:ℝ) 1) := toNNReal_monotoneOn had.2.1
  have hhfeq : M.hf=(fun u=>(laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u).toNNReal) := by
    funext u
    simp only [NativeOverlapMinimum.hf,hzero,zero_add]
  have hclock := comparison_completed_buffer_clocks M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha n hn0 M.bf hbf hN hlog M.context.hd hnd M.hlam M.hld
    as ho hwa w.η_pos w.η_le hK hbK hmEta hmA hend hT
  dsimp only at hclock
  rw [←hhfeq,←hradius] at hclock
  have hclocks := hclock hmesh
  let field : GaussianStep (FeatureIndex n) → ℝ≥0 := fun st=>st.2 (Sum.inl ⟨0,hn0⟩)
  have htotal : physicalFieldDuration field steps ≤ Bclock := by
    rw [sampledFieldDuration_total n hn0 M.bf M.hf hbf hhf as ho he]
    exact M.clockBudget
  have hg : 0 < laplaceComparisonStrength M.context.d M.lam w.a :=
    laplaceComparisonStrength_pos M.context.d M.hlam _
  have hratio : w.A/((n:ℝ)*laplaceComparisonStrength M.context.d M.lam w.a*w.a^4) ≤
      Rcap*(n:ℝ)^(-(3*m-delta)) :=
    (div_le_div_of_nonneg_right hAcap (by positivity)).trans (hcap M w.a w.xa hwa1)
  let L := 24*(K+1)*Real.log (n:ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hfloor : (1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength M.context.d M.lam w.a*w.a^4)))*w.a*
      laplaceComparisonStrength M.context.d M.lam w.a/L ≤ w.D₀ := by rw [←heta,hD]
  exact hbuf steps ha (q 0) M.xs M.hxs w field
    (laplaceComparisonStrength M.context.d M.lam w.a) L v
    (sampledFieldClock_aligned n hn0 M.bf M.hf as 0) htotal
    (by simpa only [hD,steps,q,field] using hclocks.1)
    (by simpa only [hD,steps,q,field] using hclocks.2)
    hQ hbK hmass hg hL hA heta hfloor hC hF hc0 hlog hJ le_rfl hratio hmasslow hav

end OAI.SKFluctuations.LaplaceWindowFormalization
