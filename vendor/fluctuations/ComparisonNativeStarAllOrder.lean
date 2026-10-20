module

public import ComparisonNativeStarCompletedInnovation
public import ComparisonSignedCavityActualStarProjection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7000000
namespace NativeStarBuffer

structure CompletedStarBufferGeometry {n:ℕ}
    {steps:List (GaussianStep (FeatureIndex n))} {xs:ℝ}
    (r:Fin (steps.length+2) → ℝ)
    (d lam E x mesh delta c1 K Cprof Ccap Fcap cFloor Ddepth:ℝ) where
  window:PhysicalBandWindow n steps xs
  radius_eq:window.radius=r
  radius_mesh:∀j:Fin (steps.length+1),window.radius j.succ-window.radius j.castSucc ≤ mesh
  mesh_eta:mesh ≤ window.η/2
  mesh_a:mesh ≤ window.a/8
  end_room:window.b+window.η ≤ 1
  dyadic_room:(2:ℝ)^window.depth*window.b ≤ 1
  band_width:window.b ≤ K*window.a
  mass_upper:window.mass ≤ K*window.C*window.a
  x_lower:x ≤ window.a
  cap_upper:window.A ≤ comparisonCap n delta (comparisonSmallMass n E)
    (comparisonConstraintLength n E d) E d (Cprof*window.a)
  cap_pos:0 < window.A
  balance:window.η=(1/Real.sqrt (window.A*((n:ℝ)*laplaceComparisonStrength d lam window.a*window.a^4)))*window.a
  duration:window.D₀=window.η*laplaceComparisonStrength d lam window.a/(24*(K+1)*Real.log (n:ℝ))
  C_upper:window.C ≤ Ccap
  F_upper:window.F ≤ Fcap
  c_lower:cFloor ≤ window.c₀
  depth_upper:(window.depth:ℝ) ≤ Ddepth*Real.log (n:ℝ)
  mass_lower:(n:ℝ)^(-c1)*window.a ≤ window.mass

structure OriginalStarProjectionGeometry {n:ℕ}
    (steps:List (GaussianStep (FeatureIndex n))) (fork t:ℕ)
    (xs H v theta d lam E delta Cprof Lcount H₀ Bclock:ℝ) where
  D₀:ℝ
  duration_floor:laplaceComparisonStrength d lam v*theta*v/
    (3*comparisonCap n delta (comparisonSmallMass n E)
      (comparisonConstraintLength n E d) E d (Cprof*v)*Real.log (n:ℝ)) ≤ D₀
  duration_pos:0 < D₀
  u:ℕ
  cs:List (ℝ×ℕ)
  a:Fin cs.length → ℝ
  D:Fin cs.length → ℝ
  a₀:ℝ
  Dshort:ℝ
  central_le:t ≤ u
  terminal_bound:u ≤ steps.length+1
  last_cut:lastLayerCut cs u=steps.length+1
  short_amplitude:0 < a₀
  short_floor:D₀ ≤ Dshort
  short_upper:Dshort ≤ Bclock
  short_clock:PhysicalProjectionClock n steps fork t u a₀ Dshort
  first_anchor:xs+physicalCutMass 0 steps u ≤ H*a₀^2
  layer_cuts:∀j,cutPredecessor cs u j ≤ (cs.get j).2 ∧ (cs.get j).2 ≤ steps.length+1
  layer_clocks:∀j,0 < a j ∧ D₀ ≤ D j ∧ D j ≤ Bclock ∧
    PhysicalProjectionClock n steps fork (cutPredecessor cs u j) (cs.get j).2 (a j) (D j)
  anchors:∀i j,i ≤ j.succ → xs+physicalCutMass 0 steps (overlapComponentEnd cs u i) ≤ H*(a j)^2
  count:((cs.length+2:ℕ):ℝ) ≤ Lcount*Real.log (n:ℝ)
  anchor_upper:H ≤ H₀/v

theorem explicit_common_star_exponents {kappa:ℝ} (hk:0 < kappa) :
    let c1:=kappa/64
    let saving:=kappa/256
    0 < c1 ∧ 0 < saving ∧ saving < kappa/8-c1 ∧
      2*saving < kappa-c1 ∧ saving < c1/2 := by
  dsimp only
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem eventually_star_profile_error {c1 saving:ℝ} (hs:saving < c1/2) :
    ∀ᶠn:ℕ in atTop,∀v:ℝ,0 ≤ v → 2*(n:ℝ)^(-c1/2)*v ≤ (n:ℝ)^(-saving)*v := by
  filter_upwards [eventually_log_polynomial_saving 0 (by linarith : 2*(saving/2) < c1/2) (2:ℝ)] with n hn
  intro v hv
  have hh:2*(n:ℝ)^(-c1/2) ≤ (n:ℝ)^(-saving):=by
    simpa only [pow_zero,mul_one,show -2*(saving/2)=-saving by ring,show -(c1/2)=-c1/2 by ring] using hn
  exact mul_le_mul_of_nonneg_right hh hv

theorem eventually_comparison_original_star_all_order (k:ℕ) (Bclock:ℝ)
    {m delta gamma c1 saving Q K Cprof Ccap Fcap cFloor Ddepth Lcount H₀ Astar:ℝ}
    (hm:0 < m) (hdelta:0 ≤ delta) (hgamma:0 < gamma) (hmargin:delta < 3*m)
    (hsaving:0 < saving) (hbuffer:saving < (3*m-delta)/8-c1)
    (hprojection:2*saving < 3*m-delta-c1) (hselection:saving < c1/2)
    (hQ:0 ≤ Q) (hK:1 ≤ K) (hCprof:0 ≤ Cprof) (hCcap:0 ≤ Ccap)
    (hcFloor:0 < cFloor) (hDepth:0 ≤ Ddepth) (hCount:0 ≤ Lcount) (hH₀:0 ≤ H₀) (hAstar:0 ≤ Astar) :
    ∀ᶠn:ℕ in atTop,∀{c:ℝ} {floor cap:ℝ → ℝ}
      (hc:0 < c) (hk:ContinuousOn floor (Icc (0:ℝ) 1))
      (hkc:∀r∈Icc (0:ℝ) 1,c ≤ floor r) (hMm:MonotoneOn cap (Icc (0:ℝ) 1)) (hM:0 ≤ cap 1)
      (α:inverseIntegralConstraints 0 0 floor cap) (b:ℝ → ℝ≥0) (hb:MonotoneOn b (Icc (0:ℝ) 1))
      (d lam E x xs mesh v theta H Sstar:ℝ) (as:List PositiveMass) (ho:MassOrdered 0 as),
      let R:=comparisonSweepQuantile hc hk hkc hMm hM α
      let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
      let q:=completedPathClock n b hf
      let steps:=sampleClockSteps q 0 as
      let ha:=sampleClockSteps_ordered q as ho
      let r:=physicalQuantileGrid zero_le_one zero_le_one hc hk hkc hMm hM α steps ha
      ∀(fork t:ℕ) (B:PhysicalStarBufferData n steps (q 0) fork t Sstar)
        (Gm Gp:CompletedStarBufferGeometry (xs:=xs) r d lam E x mesh delta c1 K Cprof Ccap Fcap cFloor Ddepth)
        (P:OriginalStarProjectionGeometry steps fork t xs H v theta d lam E delta Cprof Lcount H₀ Bclock),
      0 < d → 1/(n:ℝ) ≤ d → 0 < lam → lam ≤ d^2 → lam ≤ Bclock → 0 < E →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*d ≤ E → E ≤ d^2/Real.sqrt n →
      0 < x → (n:ℝ)^delta*Real.sqrt n*E/Real.sqrt lam ≤ x → x ≤ v → 0 < xs → 0 ≤ H →
      (n:ℝ)^(-c1) ≤ theta →
      Gm.window.a ≤ v → Gp.window.a ≤ v →
      B.km=physicalWindowWeight steps 0 Gm.window.selected →
      B.kp=physicalWindowWeight steps 0 Gp.window.selected →
      B.eta ≤ 2*(n:ℝ)^(-c1/2)*v → |Sstar| ≤ Astar*v →
      physicalRawRatio n (k+1) steps 0 xs (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id ≤ Q →
      physicalStarPairMoment n (k+1) steps (Measure.pi fun i=>gaussianReal 0 (q 0 i))
        id measurable_id fork Sstar ≤
      ((3:ℝ)^(2*(k+1)-1)*(1+5^(2*(k+1))+2^(4*(k+1)-2)*(32^(2*(k+1))+(Astar+5)^(2*(k+1)))))*
        ((n:ℝ)^(-saving))^(k+1)*v^(2*(k+1)) := by
  filter_upwards [eventually_comparison_completed_buffer_polynomial k Bclock hm hdelta hgamma hmargin hbuffer
    hK hCprof hCcap hcFloor hDepth,
    eventually_comparison_actual_star_projection k 0 Bclock hm hdelta hgamma hCprof hCount (sq_nonneg Q) hH₀ hprojection,
    eventually_star_profile_error hselection,eventually_gt_atTop (1:ℕ)] with n hbuf hproj hmean hn
  intro c floor cap hc hk hkc hMm hM α b hb d lam E x xs mesh v theta H Sstar as ho
  dsimp only
  intro fork t B Gm Gp P hd hnd hlam hld hBclock hE hlo hup hx hrange hxv hxs hH htheta
    hmV hpV hkm hkp heta hS hraw
  let R:=comparisonSweepQuantile hc hk hkc hMm hM α
  let hf:=fun u=>(laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q:=completedPathClock n b hf
  let steps:=sampleClockSteps q 0 as
  let ha:=sampleClockSteps_ordered q as ho
  let r:=physicalQuantileGrid zero_le_one zero_le_one hc hk hkc hMm hM α steps ha
  have hN:0 < (n:ℝ):=by exact_mod_cast (zero_lt_one.trans hn)
  have hv:0 < v:=hx.trans_le hxv
  have hepsilon:0 < (n:ℝ)^(-saving):=Real.rpow_pos_of_pos hN _
  have he1:(n:ℝ)^(-saving) ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn.le) (by linarith)
  have hcm (G:CompletedStarBufferGeometry (xs:=xs) r d lam E x mesh delta c1 K Cprof Ccap Fcap cFloor Ddepth)
      (hav:G.window.a ≤ v):physicalBufferCenteredNorm n steps (q 0)
        (physicalWindowWeight steps 0 G.window.selected) (2*(k+1):ℕ) ≤ (n:ℝ)^(-saving)*v := by
    exact hbuf hc hk hkc hMm hM α b hb d lam E x xs mesh as ho G.window
      hd hnd hlam hld hBclock hE hlo hup hx hrange G.x_lower hxs G.radius_eq G.radius_mesh
      G.mesh_eta G.mesh_a G.end_room G.dyadic_room G.band_width G.mass_upper G.cap_upper G.cap_pos
      G.balance G.duration G.C_upper G.F_upper G.c_lower G.depth_upper G.mass_lower hraw v hav
  have hCm:=hcm Gm hmV
  have hCp:=hcm Gp hpV
  rw [←hkm] at hCm
  rw [←hkp] at hCp
  have hQ0:0 ≤ physicalRawRatio n (k+1) steps 0 xs
    (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id:=
    zero_le_one.trans (physicalRawRatio_one_le n (k+1) steps 0 xs
      (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)
  have hQsq:(physicalRawRatio n (k+1) steps 0 xs
      (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id)^2 ≤ Q^2*(Real.log (n:ℝ))^0:=by
    simpa only [pow_zero,mul_one] using pow_le_pow_left₀ hQ0 hraw 2
  have hProj:=hproj (FeatureIndex n → ℝ) steps 0 P.D₀ xs H v theta d lam E x
    P.duration_pos hxs hH ha hd hlam hld hE hlo hup hx hrange hxv htheta P.duration_floor P.anchor_upper
    (Measure.pi fun i=>gaussianReal 0 (q 0 i)) id measurable_id fork t P.u P.cs P.a P.D P.a₀ P.Dshort
    P.central_le P.terminal_bound P.last_cut P.short_amplitude P.short_floor P.short_upper P.short_clock
    P.first_anchor P.layer_cuts P.layer_clocks P.anchors P.count hQsq
  have hEta:B.eta ≤ (n:ℝ)^(-saving)*v:=heta.trans (hmean v hv.le)
  exact physical_star_from_buffer_data_polynomial n (k+1) (by omega) steps ha (q 0) fork t Sstar B
    hepsilon he1 hv.le hAstar hS hCm hCp hEta hProj

end NativeStarBuffer
end OAI.SKFluctuations
