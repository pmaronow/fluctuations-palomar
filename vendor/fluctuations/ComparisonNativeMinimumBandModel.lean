module

public import ComparisonNativeMinimumPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 4000000

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

structure BandGeometry (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : a.Potential) where
  ag : ℝ
  zg : ℝ
  lo : ℝ
  hi : ℝ
  Ko : ℝ
  cutRadius : ℝ
  hag : 0 < ag
  hagz : ag ≤ zg
  hzg : zg ≤ 1
  hlo : 0 ≤ lo
  hKo : 1 ≤ Ko
  hband : hi+a.context.U ≤ Ko*(lo+a.context.U)
  hcut : 0 < cutRadius
  hcut1 : cutRadius ≤ 1
  clockRegularity : NativePullbackClockRegularity a.alpha.val.val a.b a.h ag zg
  capSet : Set ℝ
  hopen : IsOpen capSet
  hcapSet : capSet ⊆ Ioo (0 : ℝ) 1
  hnegative : ∀r ∈ capSet, p.H r < 0
  hcomponent : ∀r ∈ capSet, p.H (sInf (ordConnectedComponent capSet r)) = 0 ∧
    (p.H (sSup (ordConnectedComponent capSet r)) = 0 ∨ sSup (ordConnectedComponent capSet r) = 1)
  l : ℕ
  hl : 2 < l
  y : ℝ
  Q : ℝ
  Lside : ℝ
  hy : 0 < y
  hQ : 1 ≤ Q
  hLside : 0 ≤ Lside
  bandMass : ℝ
  hbandMass : 0 < bandMass

def BandGeometry.toModel
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {p : a.Potential} (g : a.BandGeometry p)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d) : NativeBandModel where
  c := a.context.floor
  k := a.context.k
  M := a.context.M
  hc := a.context.hc
  hk := a.context.hk
  hkc := a.context.hkc
  hm := a.context.hm
  hM := a.context.hM
  n := n
  dphys := dphys
  e := e
  N := a.context.N
  delta := delta
  U := a.context.U
  Lcap := a.context.L
  E := a.context.E
  d := a.context.d
  lam := a.lam
  hN := by change (1 : ℝ) ≤ (n+1 : ℕ); exact_mod_cast Nat.succ_pos n
  hlog := hlog
  hU := a.context.hU
  hLcap := a.context.hL
  hE := a.context.hE
  hd := a.context.hd
  hnd := hnd
  hlam := a.hlam
  hld := a.hld
  hMdef := rfl
  b := a.b
  h := a.h
  hb := a.hb
  hlb := a.hlb
  hh := a.hh
  hh0 := a.hh0
  alpha := a.alpha
  H := p.H
  multiplier := a.controlFactor
  hH := p.hH
  hJ := fun r _ => a.controlFactor_pos r
  hD := p.hD
  hbang := p.hbang
  hzero := p.hzero
  ag := g.ag
  zg := g.zg
  lo := g.lo
  hi := g.hi
  Ko := g.Ko
  cutRadius := g.cutRadius
  hag := g.hag
  hagz := g.hagz
  hzg := g.hzg
  hlo := g.hlo
  hKo := g.hKo
  hband := g.hband
  hcut := g.hcut
  hcut1 := g.hcut1
  clockRegularity := g.clockRegularity
  capSet := g.capSet
  hopen := g.hopen
  hcapSet := g.hcapSet
  hnegative := g.hnegative
  hcomponent := g.hcomponent
  l := g.l
  hl := g.hl
  xs := a.xs
  y := g.y
  Q := g.Q
  Lside := g.Lside
  hxs := a.hxs
  hy := g.hy
  hQ := g.hQ
  hLside := g.hLside
  bandMass := g.bandMass
  hbandMass := g.hbandMass

theorem BandGeometry.toModel_error_density
    {a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {p : a.Potential} (g : a.BandGeometry p)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (hlog : 1 ≤ Real.log a.context.N) (hnd : 1/a.context.N ≤ a.context.d) (u : ℝ) :
    let b := g.toModel dphys e hlog hnd
    b.R u = a.R u ∧ b.bf u = a.bf u ∧ b.hf u = a.hf u ∧
      b.thermal u = orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
