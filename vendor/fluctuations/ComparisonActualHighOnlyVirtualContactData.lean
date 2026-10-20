module

public import ComparisonActualHighOnlyPotential
public import ComparisonNativeVirtualContacts

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
def ActualHighOnlyOverlapMinimum.Potential.toVirtualContactData
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {minimum : ActualHighOnlyOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    (p : minimum.Potential) : NativeVirtualContactData delta where
  N := minimum.context.N
  U := minimum.context.U
  L := minimum.context.L
  E := minimum.context.E
  d := minimum.context.d
  origin := 0
  u0 := minimum.data.s
  hN := minimum.context.hN
  hU := minimum.context.hU
  hL := minimum.context.hL
  hE := minimum.context.hE
  hd := minimum.context.hd
  hLU := min_le_left _ _
  horigin := le_rfl
  hwork := zero_le_one
  alpha := minimum.alpha
  H := p.H
  hH := p.hH
  hfloor := p.hfloor
  hcap := p.hbang

end OAI.SKFluctuations.LaplaceWindowFormalization
