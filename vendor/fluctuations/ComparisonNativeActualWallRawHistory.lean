module

public import ComparisonNativeActualWallProfileHistory
public import ComparisonNativeActualGeneralBareEndpointCost
public import ComparisonActualHighWallWeakenConstants
public import ComparisonNativeActualGeneralProfileHistoryAssembly
public import ComparisonNativeActualComparableBandCompleteProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

structure ActualNativeWallHistory
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T c0 : ℝ) where
  wall : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock
  root : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock
  history : ActualWeakSelectedHistoryChain c0 root M
  seedx : ℕ→ℝ
  hx : ∀n,0 < seedx n
  hxunit : ∀ᶠn in atTop,seedx n ≤ 1
  htarget : ∀ᶠn in atTop,comparisonConditionalScale (wall n).data.N delta
    (wall n).data.E ((wall n).data.d^2) ≤ seedx n
  hcap : ∀ᶠn in atTop,(wall n).z ≤ Az*seedx n
  hweak : Tendsto (fun n=>(wall n).data.g (seedx n)/(seedx n)^2) atTop (𝓝 0)
  hs : Tendsto (fun n=>(wall n).data.s/actualChildCutoff (dim n+1) delta c0
    (wall n).data.d ((wall n).data.d^2) (seedx n)) atTop (𝓝 0)
  hcut : ∀ᶠn in atTop,actualChildCutoff (dim n+1) delta c0 (wall n).data.d
    ((wall n).data.d^2) (seedx n) ≤ comparisonLowerScale (root n).context.N
      (root n).context.E (root n).context.d
  hb : ∀ᶠn in atTop,∀u,(root n).b u=(wall n).data.b (wall n).alpha u
  hh : ∀ᶠn in atTop,∀u,(root n).h u=(wall n).data.h (wall n).alpha u
  hfieldscale : ∀ᶠn in atTop,(wall n).data.d^2 ≤ comparisonLowerScale
    (root n).context.N (root n).context.E (root n).context.d
  hTemp : ∀ᶠn in atTop,(wall n).data.T=T
  hT : 0 < T

namespace ActualNativeWallHistory
variable {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
variable {cl' cu' Az' Ct' D' Bclock' : ℝ}
def comp (G : ActualNativeWallHistory M T c0) (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    ActualNativeWallHistory (fun n=>M (phi n)) T c0 where
  wall := fun n=>G.wall (phi n)
  root := fun n=>G.root (phi n)
  history := G.history.comp phi hphi.tendsto_atTop
  seedx := fun n=>G.seedx (phi n)
  hx := fun n=>G.hx (phi n)
  hxunit := hphi.tendsto_atTop.eventually G.hxunit
  htarget := hphi.tendsto_atTop.eventually G.htarget
  hcap := hphi.tendsto_atTop.eventually G.hcap
  hweak := G.hweak.comp hphi.tendsto_atTop
  hs := G.hs.comp hphi.tendsto_atTop
  hcut := hphi.tendsto_atTop.eventually G.hcut
  hb := hphi.tendsto_atTop.eventually G.hb
  hh := hphi.tendsto_atTop.eventually G.hh
  hfieldscale := hphi.tendsto_atTop.eventually G.hfieldscale
  hTemp := hphi.tendsto_atTop.eventually G.hTemp
  hT := G.hT

def weaken_constants (G : ActualNativeWallHistory M T c0)
    (hcl : cl' ≤ cl) (hcu : cu ≤ cu') (hAz : Az ≤ Az')
    (hCt : Ct ≤ Ct') (hD : D ≤ D') (hB : Bclock ≤ Bclock') :
    ActualNativeWallHistory (fun n=>(M n).weakenConstants hcl hcu hAz hCt hD hB) T c0 where
  wall := fun n=>(G.wall n).weakenConstants hcl hcu hAz hCt hD hB
  root := fun n=>(G.root n).weakenConstants hcl hcu hAz hCt hD hB
  history := G.history.weaken_constants hcl hcu hAz hCt hD hB
  seedx := G.seedx
  hx := G.hx
  hxunit := G.hxunit
  htarget := G.htarget
  hcap := by
    filter_upwards [G.hcap] with n hn
    exact hn.trans (mul_le_mul_of_nonneg_right hAz (G.hx n).le)
  hweak := G.hweak
  hs := G.hs
  hcut := G.hcut
  hb := G.hb
  hh := G.hh
  hfieldscale := G.hfieldscale
  hTemp := G.hTemp
  hT := G.hT

def append_child (G : ActualNativeWallHistory M T c0)
    (Q : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ x n)
    (hcap : ∀ᶠn in atTop,(M n).z ≤ Az*x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hd : ∀ᶠn in atTop,(Q n).context.d=actualChildRadius c0 (x n))
    (hE : ∀ᶠn in atTop,(Q n).context.E=actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (x n))
    (hb : ∀ᶠn in atTop,∀u,(Q n).b u=(M n).b u-laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
    (hh : ∀ᶠn in atTop,∀u,(Q n).h u=(M n).h u+laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u)
    :
    ActualNativeWallHistory Q T c0 where
  wall := G.wall
  root := G.root
  history := .child G.history x hx hxunit htarget hcap hweak hd hE hb hh
  seedx := G.seedx
  hx := G.hx
  hxunit := G.hxunit
  htarget := G.htarget
  hcap := G.hcap
  hweak := G.hweak
  hs := G.hs
  hcut := G.hcut
  hb := G.hb
  hh := G.hh
  hfieldscale := G.hfieldscale
  hTemp := G.hTemp
  hT := G.hT

def profile (G : ActualNativeWallHistory M T c0)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ActualNativeWallProfileHistory M T c0 where
  wall := G.wall
  root := G.root
  history := G.history
  seedx := G.seedx
  hx := G.hx
  hxunit := G.hxunit
  htarget := G.htarget
  hcap := G.hcap
  hweak := G.hweak
  hs := G.hs
  hcut := G.hcut
  hb := G.hb
  hh := G.hh
  hfieldscale := G.hfieldscale
  hTemp := G.hTemp
  hT := G.hT
  xs_zero := hxs

theorem endpoint_cost_tendsto_zero (G : ActualNativeWallHistory M T c0)
    (hs : Tendsto (fun n=>(G.wall n).data.s) atTop (𝓝 0))
    (hd : Tendsto (fun n=>(G.wall n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) := by
  apply actual_weak_general_bare_history_endpoint_cost_tendsto_zero G.history
  have H:=ActualHighWallData.endpoint_L1_cost_tendsto_zero G.wall G.hTemp hs hd
  apply H.congr'
  filter_upwards [G.hb,G.hh] with n hb hh
  have Hb : (G.root n).b=(G.wall n).data.b (G.wall n).alpha:=funext hb
  have Hh : (G.root n).h=(G.wall n).data.h (G.wall n).alpha:=funext hh
  rw [Hb,Hh]

theorem total_root (G : ActualNativeWallHistory M T c0) :
    ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0 := by
  apply G.history.total_root_general_bare
  filter_upwards [G.hTemp,G.hb,G.hh] with n ht hb hh
  constructor
  · intro u hu
    rw [hb,hh,←((G.wall n).data.clock_coe (G.wall n).alpha hu).1,
      ←((G.wall n).data.clock_coe (G.wall n).alpha hu).2]
    exact ((G.wall n).data.total_clock_le (G.wall n).alpha u hu).trans_eq ht
  · rw [hh,←((G.wall n).data.clock_coe (G.wall n).alpha (by norm_num)).2,
      (G.wall n).data.root_field_zero (G.wall n).alpha]
    rfl

end ActualNativeWallHistory
end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
