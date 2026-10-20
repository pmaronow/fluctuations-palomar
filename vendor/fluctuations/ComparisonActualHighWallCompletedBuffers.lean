module

public import ComparisonActualHighWallBufferClocks
public import ComparisonActualHighWallStarProjectionMoment
public import ComparisonNativeStarCompletedBuffers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy NativeStarBuffer
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 9500000
attribute [local instance] Classical.propDecidable

theorem eventually_actual_high_wall_completed_buffer_polynomial
    (p : ℕ) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D c1 saving Q K Cprof Fcap Ddepth : ℝ}
    (hm : 0 < m) (_hdelta : 0 ≤ delta) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmargin : delta < 3*m) (hsaving : saving < (3*m-delta)/8-c1)
    (hK : 1 ≤ K) (hCprof : 0 ≤ Cprof) (hcl : 0 < cl) (hcu : 0 ≤ cu)
    (hDepth : 0 ≤ Ddepth) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀(as : List PositiveMass) (ho : MassOrdered 0 as),partitionEnd 0 as=1 →
      let q := completedPathClock n M.bf M.hf
      let steps := sampleClockSteps q 0 as
      let ha := sampleClockSteps_ordered q as ho
      ∀(w : PhysicalBandWindow n steps M.xs) (mesh v : ℝ),
      w.radius=physicalQuantileGrid M.data.hr M.data.hs1 M.data.hc
        M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha steps ha →
      (∀j : Fin (steps.length+1),w.radius j.succ-w.radius j.castSucc ≤ mesh) →
      M.data.rmin ≤ w.a/4 → mesh ≤ w.η/2 → mesh ≤ w.a/8 → w.b+w.η ≤ 1 →
      (2:ℝ)^w.depth*w.b ≤ 1 → w.b ≤ K*w.a → w.mass ≤ K*w.C*w.a →
      w.A ≤ M.data.M (Cprof*w.a) → 0 < w.A →
      w.η=(1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength M.data.d (M.data.d^2) w.a*w.a^4)))*w.a →
      w.D₀=w.η*laplaceComparisonStrength M.data.d (M.data.d^2) w.a/(24*(K+1)*Real.log (n:ℝ)) →
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
    eventually_actual_high_wall_star_cap_saving Bclock hm hC0 hCt hCprof,
    eventually_comparisonLowerScale_depth hC0 hm,hlogevent,eventually_gt_atTop (1:ℕ)]
    with n hbuf hcap hdepth hlog hn
  intro M as ho he
  dsimp only
  intro w mesh v hradius hmesh hwall hmEta hmA hend hT hbK hmass hAcap hA heta hD hC hF hc0
    hJ hmasslow hQ hav
  let q := completedPathClock n M.bf M.hf
  let steps := sampleClockSteps q 0 as
  let ha := sampleClockSteps_ordered q as ho
  have hN : 1 ≤ (n:ℝ) := by exact_mod_cast hn.le
  have hN0 : 0 < (n:ℝ) := M.data.hN
  have hn0 : 0 < n := M.data.hn
  have hwa : 0 < w.a := M.hxs.trans_le w.xa
  have hwa1 : w.a ≤ 1 := by linarith [w.ab,w.η_pos]
  have hnd : 1/(n:ℝ) ≤ M.data.d := by
    have H := hdepth M.data.E M.data.d M.data.hE M.data.hd M.hlower
    have hs : comparisonLowerScale n M.data.E M.data.d ≤ M.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ M.data.hd).mpr (by simpa only [pow_two] using M.hupper)
    exact H.trans hs
  have hbf := M.data.bf_monotone M.alpha
  have hhf := M.data.hf_monotone M.alpha
  have hclocks := actual_high_wall_completed_buffer_clocks M.data M.alpha hN hlog hnd as ho
    hwa hwall w.η_pos w.η_le hK hbK hmEta hmA hend hT
    (by intro j;dsimp only;simpa only [hradius] using hmesh j)
  let field : GaussianStep (FeatureIndex n) → ℝ≥0 := fun st=>st.2 (Sum.inl ⟨0,hn0⟩)
  have htotal : physicalFieldDuration field steps ≤ Bclock := by
    rw [sampledFieldDuration_total n hn0 M.bf M.hf hbf hhf as ho he]
    exact (M.data.field_clock_budget M.alpha).trans M.hT
  have hg : 0 < laplaceComparisonStrength M.data.d (M.data.d^2) w.a :=
    laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) _
  have hratio : w.A/((n:ℝ)*laplaceComparisonStrength M.data.d (M.data.d^2) w.a*w.a^4) ≤
      Rcap*(n:ℝ)^(-(3*m-delta)) :=
    (div_le_div_of_nonneg_right hAcap (by positivity)).trans (hcap M w.a w.xa hwa1)
  let L := 24*(K+1)*Real.log (n:ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hfloor : (1/Real.sqrt (w.A*((n:ℝ)*laplaceComparisonStrength M.data.d (M.data.d^2) w.a*w.a^4)))*w.a*
      laplaceComparisonStrength M.data.d (M.data.d^2) w.a/L ≤ w.D₀ := by rw [←heta,hD]
  exact hbuf steps ha (q 0) M.xs M.hxs w field
    (laplaceComparisonStrength M.data.d (M.data.d^2) w.a) L v
    (sampledFieldClock_aligned n hn0 M.bf M.hf as 0) htotal
    (by simpa only [hD,steps,q,field,hradius] using hclocks.1)
    (by simpa only [hD,steps,q,field,hradius] using hclocks.2)
    hQ hbK hmass hg hL hA heta hfloor hC hF hc0 hlog hJ le_rfl hratio hmasslow hav

end OAI.SKFluctuations.LaplaceWindowFormalization
