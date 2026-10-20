module

public import ComparisonActualHighWallPotential
public import ComparisonNativeVirtualContacts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal

def ActualHighWallOverlapMinimum.Potential.toVirtualContactData
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {minimum : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : minimum.Potential) : NativeVirtualContactData delta where
  N := minimum.data.N
  U := comparisonSmallMass minimum.data.N minimum.data.E
  L := comparisonConstraintLength minimum.data.N minimum.data.E minimum.data.d
  E := minimum.data.E
  d := minimum.data.d
  origin := minimum.data.rmin
  u0 := minimum.data.s
  hN := minimum.data.hN
  hU := minimum.data.hU
  hL := minimum.data.hL
  hE := minimum.data.hE
  hd := minimum.data.hd
  hLU := min_le_left _ _
  horigin := minimum.data.hrbounds.1.le
  hwork := minimum.data.hr
  alpha := minimum.alpha
  H := p.H
  hH := p.hH
  hfloor := p.hfloor
  hcap := p.hbang

end OAI.SKFluctuations.LaplaceWindowFormalization
