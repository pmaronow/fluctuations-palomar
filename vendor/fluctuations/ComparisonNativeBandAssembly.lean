module

public import ComparisonNativeShellCapSideVariance
public import ComparisonNativeShellCapUnionCovariance
public import ComparisonCapSideVarianceEndpointFilled
public import ComparisonNativeEndpointUnionCovarianceRate
public import ComparisonNativeWeightedDefectLimit
public import ComparisonNativeBinScale
public import ComparisonNativeMaskMassTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3200000
attribute [local instance] Classical.propDecidable

structure NativeBandModel where
  c : ℝ
  k : ℝ→ℝ
  M : ℝ→ℝ
  hc : 0< c
  hk : ContinuousOn k (Icc (0:ℝ) 1)
  hkc : ∀r∈Icc (0:ℝ) 1,c≤ k r
  hm : MonotoneOn M (Icc (0:ℝ) 1)
  hM : 0≤ M 1
  n : ℕ
  dphys : ℕ
  e : Fin (dphys+1)≃FeatureIndex (n+1)
  N : ℝ
  delta : ℝ
  U : ℝ
  Lcap : ℝ
  E : ℝ
  d : ℝ
  lam : ℝ
  hN : 1≤ N
  hlog : 1≤ Real.log N
  hU : 0< U
  hLcap : 0< Lcap
  hE : 0< E
  hd : 0< d
  hnd : 1/N≤ d
  hlam : 0< lam
  hld : lam≤ d^2
  hMdef : M=comparisonCap N delta U Lcap E d
  b : ℝ→ℝ
  h : ℝ→ℝ
  hb : MonotoneOn b (Icc (0:ℝ) 1)
  hlb : lam≤ b 0
  hh : MonotoneOn h (Icc (0:ℝ) 1)
  hh0 : 0≤ h 0
  alpha : inverseIntegralConstraints 0 0 k M
  H : ℝ→ℝ
  multiplier : ℝ→ℝ
  hH : AbsolutelyContinuousOnInterval H 0 1
  hJ : ∀r∈Icc (0:ℝ) 1,0< multiplier r
  hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
    (multiplier r*radiusComparisonGradient (laplaceComparisonStrength d lam) alpha.val.val
      (orderedPathS (n+1)
        (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)).toNNReal)
        (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)*
          comparisonSweepQuantile hc hk hkc hm hM alpha u).toNNReal))
      (orderedPathB (n+1)
        (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)).toNNReal)
        (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)*
          comparisonSweepQuantile hc hk hkc hm hM alpha u).toNNReal)) r) r
  hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→deriv alpha.val.val r=M (alpha.val.val r)
  hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
    radiusComparisonGradient (laplaceComparisonStrength d lam) alpha.val.val
      (orderedPathS (n+1)
        (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)).toNNReal)
        (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)*
          comparisonSweepQuantile hc hk hkc hm hM alpha u).toNNReal))
      (orderedPathB (n+1)
        (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)).toNNReal)
        (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM alpha u)*
          comparisonSweepQuantile hc hk hkc hm hM alpha u).toNNReal)) r=0
  ag : ℝ
  zg : ℝ
  lo : ℝ
  hi : ℝ
  Ko : ℝ
  cutRadius : ℝ
  hag : 0< ag
  hagz : ag≤ zg
  hzg : zg≤1
  hlo : 0≤ lo
  hKo : 1≤ Ko
  hband : hi+U≤ Ko*(lo+U)
  hcut : 0< cutRadius
  hcut1 : cutRadius≤1
  clockRegularity : NativePullbackClockRegularity alpha.val.val b h ag zg
  capSet : Set ℝ
  hopen : IsOpen capSet
  hcapSet : capSet⊆Ioo (0:ℝ) 1
  hnegative : ∀r∈capSet,H r<0
  hcomponent : ∀r∈capSet,H (sInf (ordConnectedComponent capSet r))=0 ∧
    (H (sSup (ordConnectedComponent capSet r))=0 ∨ sSup (ordConnectedComponent capSet r)=1)
  l : ℕ
  hl : 2< l
  xs : ℝ
  y : ℝ
  Q : ℝ
  Lside : ℝ
  hxs : 0< xs
  hy : 0< y
  hQ : 1≤ Q
  hLside : 0≤ Lside
  bandMass : ℝ
  hbandMass : 0< bandMass

namespace NativeBandModel

abbrev R (m : NativeBandModel) := comparisonSweepQuantile m.hc m.hk m.hkc m.hm m.hM m.alpha

abbrev bf (m : NativeBandModel) := fun u=>(m.b u-laplaceComparisonStrength m.d m.lam (m.R u)).toNNReal

abbrev hf (m : NativeBandModel) := fun u=>(m.h u+laplaceComparisonStrength m.d m.lam (m.R u)*m.R u).toNNReal

abbrev q (m : NativeBandModel) := comparisonNativeCompletedClock m.hc m.hk m.hkc m.hm m.hM
  m.n m.d m.lam m.b m.h m.alpha

def P (m : NativeBandModel) : ℝ := (m.n+1:ℝ)*laplaceComparisonStrength m.d m.lam m.zg

def rho (m : NativeBandModel) : ℝ := m.alpha.val.val m.cutRadius

def AS (m : NativeBandModel) : ℝ := 108*m.Ko^2*(Real.log m.N)^2

def AC (m : NativeBandModel) : ℝ := 54*m.Ko^2*(Real.log m.N)^2

def Cnode (m : NativeBandModel) : ℝ := 2*ClockTree.errorJetVariation 2 0 0*
  clockVariationBound (physicalFeatureCoordinateBound m.n) m.q

def D0 (m : NativeBandModel) : ℝ := 9*Real.log m.N*
  ((m.Lcap/m.N^m.delta)*Real.log ((1+m.U)/m.U))

def reverse (m : NativeBandModel) (D : ℝ) : ℝ :=
  D^(((m.l:ℝ)-2)/((m.l:ℝ)-1))*((2*m.Q)^(2*m.l)*m.y^m.l)^(1/((m.l:ℝ)-1))

def thermal (m : NativeBandModel) : ℝ→ℝ := fun u=>
  orderedPathB (m.n+1) m.bf m.hf u-(orderedPathS (m.n+1) m.bf m.hf u)^2

end NativeBandModel

structure NativeBandRefinement (m : NativeBandModel) where
  as : ℕ→List PositiveMass
  mesh : ℕ→ℝ
  ho : ∀j,MassOrdered 0 (as j)
  he : ∀j,partitionEnd 0 (as j)=1
  hm : ∀j,PartitionMesh (mesh j) 0 (as j)
  hm0 : ∀j,0 ≤ mesh j
  hmesh : Tendsto mesh atTop (𝓝 0)

namespace NativeBandRefinement

abbrev steps {m : NativeBandModel} (s : NativeBandRefinement m) (j : ℕ) := sampleClockSteps m.q 0 (s.as j)

def mu {m : NativeBandModel} (s : NativeBandRefinement m) (j : ℕ) :=
  comparisonPhysicalRadiusMeasure m.hc m.hk m.hkc m.hm m.hM m.n m.dphys m.e m.d m.lam
    m.b m.h m.alpha (s.as j) (s.ho j)

def diameter {m : NativeBandModel} (s : NativeBandRefinement m) (j : ℕ) : ℝ := m.D0+2*(s.mesh j*m.Cnode)

end NativeBandRefinement

structure NativeBandFixedCapGeometry (m : NativeBandModel) where
  count : ℕ
  a : Fin count→ℝ
  z : Fin count→ℝ
  weight : Fin count→ℝ
  hga : ∀i,m.ag≤ a i
  haz : ∀i,a i< z i
  hgz : ∀i,z i≤ m.zg
  haH : ∀i,m.H (a i)=0
  hzH : ∀i,m.H (z i)=0 ∨ z i=1
  hnegative : ∀i,∀r∈Ioo (a i) (z i),m.H r<0
  hamass : ∀i,m.lo≤ m.alpha.val.val (a i)
  hzmass : ∀i,m.alpha.val.val (z i)≤ m.hi
  hweight : ∀i,0≤ weight i
  contact : ℝ→ℝ
  hmeas : Measurable contact
  bound : ℝ
  hb0 : 0≤ bound
  hbound : ∀r,‖contact r‖≤ bound
  hnonneg : ∀r,0≤ contact r

namespace NativeBandFixedCapGeometry

def fixed {m : NativeBandModel} (f : NativeBandFixedCapGeometry m) : ℝ→ℝ :=
  fixedCapContactWeight f.a f.z f.weight {r | r∈Ioo m.ag m.zg ∧ m.H r=0} f.contact

end NativeBandFixedCapGeometry

structure NativeBandSideGeometry (m : NativeBandModel) (s : NativeBandRefinement m) (cut : ℝ) where
  fixedCaps : NativeBandFixedCapGeometry m
  K : ℕ→ℕ
  selected : (j : ℕ)→Finset (Fin ((s.steps j).length+1))
  unit : (j : ℕ)→Fin ((s.steps j).length+1)→Fin (K j)
  x : ℕ→ℕ→ℝ
  widths : ℕ→ℝ
  width : ℝ
  hwidth : 2*cut≤ width
  hwidths : ∀j,2*cut≤ widths j
  hwidthlim : Tendsto widths atTop (𝓝 width)
  hstart : ∀j,x j 0=0
  hend : ∀j,x j (K j)=widths j
  hx : ∀j,∀u:Fin (K j),x j u.val< x j (u.val+1)
  hmass : ∀j,∀u:Fin (K j),physicalSelectedUnitMass (s.steps j) (selected j) (unit j) u=
    x j (u.val+1)-x j u.val
  hleft : ∀j,∀i∈selected j,m.cutRadius≤ m.R (partitionPoint 0 (s.as j) i.val)
  hsupport : ∀j,∀ᵐ r,r∉Ioo m.ag m.zg→comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (selected j) (unit j) (fun u=>sideSquareColumn (x j) cut (widths j) u.val) r=0
  hcolumns : Tendsto (fun j=>∫r in Ioo m.ag m.zg,
    |comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)
      (selected j) (unit j) (fun u=>sideSquareColumn (x j) cut (widths j) u.val) r-fixedCaps.fixed r|)
    atTop (𝓝 0)

namespace NativeBandSideGeometry

def filled {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (g : NativeBandSideGeometry m s cut) (j : ℕ) : ℝ :=
  (2*(∫r,deriv m.alpha.val.val r*comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (g.selected j) (g.unit j)
      (fun u=>sideSquareColumn (g.x j) cut (g.widths j) u.val) r∂s.mu j)+4*s.mesh j/cut)/m.rho

end NativeBandSideGeometry

structure NativeBandUnionGeometry (m : NativeBandModel) (s : NativeBandRefinement m)
    (selected : (j : ℕ)→Finset (Fin ((s.steps j).length+1))) (v : ℝ) where
  fixedCaps : NativeBandFixedCapGeometry m
  hmasslim : Tendsto (fun j=>∑i,physicalSelectedCellMass (s.steps j) (selected j) i) atTop (𝓝 v)
  hleft : ∀j,∀i∈selected j,m.cutRadius≤ m.R (partitionPoint 0 (s.as j) i.val)
  hsupport : ∀j,∀ᵐ r,r∉Ioo m.ag m.zg→comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r=0
  hcolumns : Tendsto (fun j=>∫r in Ioo m.ag m.zg,
    |comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)
      (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r-fixedCaps.fixed r|) atTop (𝓝 0)

namespace NativeBandUnionGeometry

def filled {m : NativeBandModel} {s : NativeBandRefinement m}
    {selected : (j : ℕ)→Finset (Fin ((s.steps j).length+1))} {v : ℝ}
    (_g : NativeBandUnionGeometry m s selected v) (j : ℕ) : ℝ :=
  (2*(∫r,deriv m.alpha.val.val r*comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r∂s.mu j)+2*s.mesh j)/m.rho^2

end NativeBandUnionGeometry

structure NativeBandFrame (m : NativeBandModel) (s : NativeBandRefinement m)
    (bins : ℕ) (cut w : ℝ) where
  B : ℕ
  side : Fin B→NativeBandSideGeometry m s cut
  label : Fin B→Fin bins
  hlabel : Function.Injective label
  A : (j : ℕ)→Finset (Fin ((s.steps j).length+1))
  K0 : ℕ→ℕ
  unit0 : (j : ℕ)→Fin ((s.steps j).length+1)→Fin (K0 j)
  hpos : ∀j,∀i∈A j,0< pathMassDifferences (s.steps j) 0 i
  hclass0 : ∀j,∀i∈A j,∀t∈A j,
    unit0 j i=unit0 j t ↔ wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val))=
      wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) t.val))
  hmassUpper : ∀j,∀i∈A j,m.xs+physicalCutMass 0 (s.steps j) i.val≤ m.y
  rawUpper : ∀j,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
    (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q
  hbin : ∀j,∀bb,(side bb).selected j=NativeUnitHeight.bin
    (fun i=>physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val)
    (A j) (unit0 j) bins w (label bb)
  hclass : ∀j,∀bb,∀i∈(side bb).selected j,∀t∈(side bb).selected j,
    (side bb).unit j i=(side bb).unit j t ↔
      wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val))=
        wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) t.val))
  horder : ∀j,∀bb,MonotoneOn ((side bb).unit j) ((side bb).selected j:Set _)
  hlower : ∀j,∀i∈A j,m.cutRadius≤ m.R (partitionPoint 0 (s.as j) i.val)
  hsideLog : ∀j,∀bb,Real.log ((side bb).widths j/cut)≤ m.Lside
  v : ℝ
  hv : 0< v
  hsumWidth : ∑bb,(side bb).width=v
  hvUpper : v≤ m.bandMass
  unionGeometry : NativeBandUnionGeometry m s
    (fun j=>Finset.univ.biUnion (fun bb=>(side bb).selected j)) v
  mask : ℝ→ℝ
  hmask : Measurable mask
  hmaskBound : ∀r∈Icc (0:ℝ) 1,mask r∈Icc (0:ℝ) 1
  hmaskPoint : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
    Tendsto (fun j=>comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
      m.q m.alpha (s.as j) (Finset.univ.biUnion (fun bb=>(side bb).selected j))
        (fun _=>(0:Fin 1)) (fun _=>1) r) atTop (𝓝 (mask r))

namespace NativeBandModel

theorem P_pos (m : NativeBandModel) : 0< m.P :=
  mul_pos (by positivity) (laplaceComparisonStrength_pos m.d m.hlam m.zg)

theorem rho_pos (m : NativeBandModel) : 0< m.rho := by
  have hp := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
    (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) ⟨m.hcut.le,m.hcut1⟩ m.hcut
  simpa only [rho,m.alpha.property.1] using hp

theorem AS_nonneg (m : NativeBandModel) : 0≤ m.AS := by dsimp [AS]; positivity

theorem AC_nonneg (m : NativeBandModel) : 0≤ m.AC := by dsimp [AC]; positivity

theorem D0_pos (m : NativeBandModel) : 0< m.D0 := by
  have hlog : 0< Real.log m.N := by linarith [m.hlog]
  have hratio : 1<(1+m.U)/m.U := (lt_div_iff₀ m.hU).mpr (by linarith)
  have hp : 0< m.N := zero_lt_one.trans_le m.hN
  dsimp [D0]
  exact mul_pos (mul_pos (by norm_num) hlog)
    (mul_pos (div_pos m.hLcap (Real.rpow_pos_of_pos hp _)) (Real.log_pos hratio))

theorem Cnode_nonneg (m : NativeBandModel) : 0≤ m.Cnode := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hclock := clockVariationBound_nonneg (physicalFeatureCoordinateBound m.n) m.q
    (completedPathClock_monotone (m.n+1) (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1))
  exact mul_nonneg (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _)) hclock

theorem reverse_nonneg (m : NativeBandModel) {D : ℝ} (hD : 0≤ D) : 0≤ m.reverse D := by
  apply mul_nonneg (Real.rpow_nonneg hD _) (Real.rpow_nonneg _ _)
  exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans m.hQ)) _)
    (pow_nonneg m.hy.le _)

end NativeBandModel

namespace NativeBandRefinement

theorem diameter_nonneg {m : NativeBandModel} (s : NativeBandRefinement m) (j : ℕ) :
    0≤ s.diameter j := add_nonneg m.D0_pos.le
      (mul_nonneg (by norm_num) (mul_nonneg (s.hm0 j) m.Cnode_nonneg))

theorem diameter_tendsto {m : NativeBandModel} (s : NativeBandRefinement m) :
    Tendsto s.diameter atTop (𝓝 m.D0) := by
  change Tendsto (fun j=>m.D0+2*(s.mesh j*m.Cnode)) atTop (𝓝 m.D0)
  simpa only [mul_zero,zero_mul,add_zero] using
    ((s.hmesh.mul_const m.Cnode).const_mul 2).const_add m.D0

end NativeBandRefinement

namespace NativeBandSideGeometry

theorem filled_eventually {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (g : NativeBandSideGeometry m s cut) (hcut : 0< cut) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ j in atTop,g.filled j≤(m.AS/(m.P*m.rho))*Real.log (g.width/cut)+ε := by
  let f := g.fixedCaps
  have ht := comparisonPhysicalRegularLeftContactCapSideVarianceFilled_eventually
    m.hc m.hk m.hkc m.hm m.hM m.hN m.hlog m.hU m.hLcap m.hE m.hd m.hnd m.hlam m.hld
    m.hMdef m.n m.dphys m.e m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha m.H m.multiplier
    m.hH m.hJ m.hD m.hbang m.hzero m.hag m.hagz m.hzg m.hlo m.hKo m.hband
    f.a f.z f.weight f.hga f.haz f.hgz f.haH f.hzH f.hnegative f.hamass f.hzmass f.hweight
    s.as s.mesh s.ho s.he s.hm s.hm0 s.hmesh m.clockRegularity
    f.contact f.hmeas f.bound f.hb0 f.hbound f.hnonneg g.K g.selected g.unit g.x g.widths
    hcut g.hwidth g.hwidths g.hwidthlim g.hstart g.hend g.hx g.hmass m.hcut m.hcut1 g.hleft
    g.hsupport g.hcolumns hε
  filter_upwards [ht] with j hj
  exact hj.1

end NativeBandSideGeometry

namespace NativeBandUnionGeometry

theorem filled_eventually {m : NativeBandModel} {s : NativeBandRefinement m}
    {selected : (j : ℕ)→Finset (Fin ((s.steps j).length+1))} {v : ℝ}
    (g : NativeBandUnionGeometry m s selected v) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ j in atTop,g.filled j≤(m.AC/(m.P*m.rho^2))*v+ε := by
  let f := g.fixedCaps
  have ht := comparisonPhysicalRegularLeftContactCapUnionCovariance_eventually
    m.hc m.hk m.hkc m.hm m.hM m.hN m.hlog m.hU m.hLcap m.hE m.hd m.hnd m.hlam m.hld
    m.hMdef m.n m.dphys m.e m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha m.H m.multiplier
    m.hH m.hJ m.hD m.hbang m.hzero m.hag m.hagz m.hzg m.hlo m.hKo m.hband
    f.a f.z f.weight f.hga f.haz f.hgz f.haH f.hzH f.hnegative f.hamass f.hzmass f.hweight
    s.as s.mesh s.ho s.he s.hm s.hm0 s.hmesh m.clockRegularity
    f.contact f.hmeas f.bound f.hb0 f.hbound f.hnonneg selected g.hmasslim m.hcut m.hcut1 g.hleft
    g.hsupport g.hcolumns hε
  filter_upwards [ht] with j hj
  exact hj.1

end NativeBandUnionGeometry
namespace NativeBandFrame

abbrev selected {m : NativeBandModel} {s : NativeBandRefinement m} {bins : ℕ} {cut w : ℝ}
    (f : NativeBandFrame m s bins cut w) (j : ℕ) := Finset.univ.biUnion (fun bb=>(f.side bb).selected j)

def totalWidth {m : NativeBandModel} {s : NativeBandRefinement m} {bins : ℕ} {cut w : ℝ}
    (f : NativeBandFrame m s bins cut w) (j : ℕ) : ℝ := ∑bb,(f.side bb).widths j

def sideFilled {m : NativeBandModel} {s : NativeBandRefinement m} {bins : ℕ} {cut w : ℝ}
    (f : NativeBandFrame m s bins cut w) (j : ℕ) : ℝ := ∑bb,(f.side bb).filled j

def defect {m : NativeBandModel} {s : NativeBandRefinement m} {bins : ℕ} {cut w : ℝ}
    (f : NativeBandFrame m s bins cut w) (j : ℕ) : ℝ :=
  ∑i,physicalSelectedCellMass (s.steps j) (f.selected j) i*
    actualCutReplicaDefect (m.n+1) (s.steps j) (m.q 0) i.val
      (physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val)

theorem bin_disjoint {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) (j : ℕ) :
    Pairwise (fun bb cc=>Disjoint ((f.side bb).selected j) ((f.side cc).selected j)) := by
  intro bb cc hne
  apply Finset.disjoint_left.mpr
  intro i hib hic
  rw [f.hbin j bb] at hib
  rw [f.hbin j cc] at hic
  have hb := (Finset.mem_filter.mp hib).2
  have hc := (Finset.mem_filter.mp hic).2
  exact hne (f.hlabel (Fin.ext (hb.symm.trans hc)))

theorem B_pos {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) : 0< f.B := by
  by_contra h
  have hB : f.B=0 := by omega
  have hs : (∑bb,(f.side bb).width)=0 := by
    apply Finset.sum_eq_zero
    intro bb _
    exfalso
    have hi := bb.isLt
    omega
  linarith [f.hsumWidth,f.hv]

theorem totalWidth_pos {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) (hcut : 0< cut) (j : ℕ) :
    0< f.totalWidth j := by
  apply Finset.sum_pos
  · intro bb _
    linarith [(f.side bb).hwidths j]
  · exact ⟨⟨0,f.B_pos⟩,Finset.mem_univ _⟩

theorem totalWidth_tendsto {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) :
    Tendsto f.totalWidth atTop (𝓝 f.v) := by
  have ht := tendsto_finset_sum Finset.univ (fun bb _=>(f.side bb).hwidthlim)
  change Tendsto (fun j=>∑bb,(f.side bb).widths j) atTop (𝓝 f.v)
  simpa only [f.hsumWidth] using ht

theorem finite_budget {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w)
    (hcut : 0< cut) (hw : 0< w) (hRange : m.Q^2*m.y≤(bins:ℝ)*w) (j : ℕ) :
    f.defect j≤ nativeConditionalLedgerBudget f.B (f.totalWidth j) cut (w+s.diameter j)
      (f.sideFilled j) (f.unionGeometry.filled j) (m.reverse (s.diameter j)) m.Lside := by
  have hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→m.H r<0→deriv m.alpha.val.val r=
      comparisonCap m.N m.delta m.U m.Lcap m.E m.d (m.alpha.val.val r) := by
    filter_upwards [m.hbang] with r hr hr01 hrH
    simpa only [congrFun m.hMdef (m.alpha.val.val r)] using hr hr01 hrH
  have hraw0 : 0≤ physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id :=
    zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hRangeActual : (physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id)^2*m.y≤(bins:ℝ)*w :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hraw0 (f.rawUpper j) _) m.hy.le).trans hRange
  have hn := actual_comparison_native_conditional_finite_assembly
    m.hc m.hk m.hkc m.hm m.hM m.hN m.hlog m.hd m.hnd m.hlam m.hld m.n m.b m.h
    m.hb m.hlb m.hh m.hh0 m.alpha m.H m.multiplier m.hH m.hJ m.hD m.hU m.hLcap m.hE
    hbang m.hopen m.hcapSet m.hnegative m.hcomponent (s.as j) (s.ho j) (s.he j) (s.hm j)
    m.l m.hl m.hxs m.hy.le hw (f.A j) (f.unit0 j) (f.hpos j) (f.hclass0 j)
    (f.hmassUpper j) hRangeActual f.label f.hlabel
    (fun bb=>(f.side bb).selected j) (f.hbin j) (fun bb=>(f.side bb).K j)
    (fun bb=>(f.side bb).unit j) (fun bb=>(f.side bb).x j) (fun bb=>(f.side bb).widths j)
    (f.hclass j) (f.horder j) (fun bb=>(f.side bb).hstart j) (fun bb=>(f.side bb).hend j)
    (fun bb=>(f.side bb).hx j) (fun bb=>(f.side bb).hmass j)
    hcut (fun bb=>(f.side bb).hwidths j) rfl (f.totalWidth_pos hcut j)
    m.hLside (f.hsideLog j) m.hcut m.hcut1 (f.hlower j) (s.hm0 j) m.dphys m.e
  dsimp only at hn
  have heq : (∑i,(∑bb,physicalSelectedCellMass (s.steps j) ((f.side bb).selected j) i)*
      actualCutReplicaDefect (m.n+1) (s.steps j) (m.q 0) i.val
        (physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val))=f.defect j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [selectedCellMass_sum_eq_biUnion _ _ (f.bin_disjoint j)]
  erw [heq] at hn
  have hlR : (2:ℝ)< m.l := by exact_mod_cast m.hl
  have hp : 0≤1/((m.l:ℝ)-1) := div_nonneg zero_le_one (by linarith)
  have hbase : ((2*physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id)^(2*m.l)*m.y^m.l)≤
      (2*m.Q)^(2*m.l)*m.y^m.l :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (by norm_num) hraw0)
        (mul_le_mul_of_nonneg_left (f.rawUpper j) (by norm_num)) _)
      (pow_nonneg m.hy.le _)
  have hrev := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hraw0) _)
      (pow_nonneg m.hy.le _)) hbase hp)
    (Real.rpow_nonneg (s.diameter_nonneg j) (((m.l:ℝ)-2)/((m.l:ℝ)-1)))
  have hrevScaled := mul_le_mul_of_nonneg_left hrev
    (mul_nonneg (by norm_num : (0:ℝ)≤32) (f.totalWidth_pos hcut j).le)
  let rawR := (s.diameter j)^(((m.l:ℝ)-2)/((m.l:ℝ)-1))*
    ((2*physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id)^(2*m.l)*m.y^m.l)^
        (1/((m.l:ℝ)-1))
  change f.defect j≤48*f.sideFilled j+(76+64*m.Lside)*f.totalWidth j*(w+s.diameter j)^2+
    32*f.totalWidth j*rawR+
      (66+64*m.Lside+65536*(1+m.Lside)^2)*f.unionGeometry.filled j+16*(f.B:ℝ)*cut at hn
  change 32*f.totalWidth j*rawR≤32*f.totalWidth j*m.reverse (s.diameter j) at hrevScaled
  unfold nativeConditionalLedgerBudget
  exact hn.trans (add_le_add (add_le_add (add_le_add le_rfl hrevScaled) le_rfl) le_rfl)

theorem defect_tendsto {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) :
    Tendsto f.defect atTop (𝓝 (∫u in 0..1,f.mask (m.R u)*m.thermal u)) := by
  have hmasks := comparisonNativeMask_mass_L1_tendsto_of_radius_ae m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha s.as s.ho s.he (fun _=>1) f.selected (fun _ _=>(0:Fin 1)) f.mask f.hmaskPoint
  have hmasks' : Tendsto (fun j=>∫u in 0..1,
      |nativeSelectedMassMask m.q (s.as j) (f.selected j) u-f.mask (m.R u)|) atTop (𝓝 0) := by
    simpa only [nativeSelectedMassMask,intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc] using hmasks
  have hmeas : Measurable (fun u=>f.mask (m.R u)) := f.hmask.comp
    (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hbound : ∀u∈Ioc (0:ℝ) 1,f.mask (m.R u)∈Icc (0:ℝ) 1 :=
    fun u _=>f.hmaskBound _ (comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u)
  exact actual_comparison_native_selected_defect_tendsto m.hc m.hk m.hkc m.hm m.hM
    m.n m.hd.ne' m.hlam.le m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha s.as s.mesh s.ho s.he s.hm
    s.hmesh f.selected _ hmeas hbound hmasks'

theorem sideFilled_eventually {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w) (hcut : 0< cut)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ j in atTop,f.sideFilled j≤ m.AS*(f.B:ℝ)*m.Lside/(m.P*m.rho)+ε := by
  let err := ε/((f.B:ℝ)+1)
  have herr : 0< err := div_pos hε (by positivity)
  have hall : ∀bb,∀ᶠ j in atTop,(f.side bb).filled j≤
      (m.AS/(m.P*m.rho))*Real.log ((f.side bb).width/cut)+err :=
    fun bb=>(f.side bb).filled_eventually hcut herr
  have hlog bb : Real.log ((f.side bb).width/cut)≤ m.Lside := by
    have hwpos : 0<(f.side bb).width := by linarith [(f.side bb).hwidth]
    have hl := ((Real.continuousAt_log (div_pos hwpos hcut).ne').tendsto.comp
      ((f.side bb).hwidthlim.div_const cut))
    exact le_of_tendsto hl (Eventually.of_forall (fun j=>f.hsideLog j bb))
  have hcoef : 0≤ m.AS/(m.P*m.rho) := div_nonneg m.AS_nonneg (mul_pos m.P_pos m.rho_pos).le
  filter_upwards [Filter.eventually_all.mpr hall] with j hj
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun bb _=>(hj bb).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hlog bb) hcoef) le_rfl))
  have herrbound : (f.B:ℝ)*err≤ε := by
    dsimp [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<(f.B:ℝ)+1)).mpr
    nlinarith
  change (∑bb,(f.side bb).filled j)≤_
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have heq : (f.B:ℝ)*(m.AS/(m.P*m.rho)*m.Lside+err)=
      m.AS*(f.B:ℝ)*m.Lside/(m.P*m.rho)+(f.B:ℝ)*err := by ring
  rw [heq] at hs
  exact hs.trans (add_le_add le_rfl herrbound)

theorem thermal_le_native_budget {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w)
    (hcut : 0< cut) (hw : 0< w) (hRange : m.Q^2*m.y≤(bins:ℝ)*w) :
    (∫u in 0..1,f.mask (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget f.B f.v cut (w+m.D0)
        (m.AS*(f.B:ℝ)*m.Lside/(m.P*m.rho))
        (m.AC*f.v/(m.P*m.rho^2)) (m.reverse m.D0) m.Lside := by
  let VS := m.AS*(f.B:ℝ)*m.Lside/(m.P*m.rho)
  let TC := m.AC*f.v/(m.P*m.rho^2)
  let C := 66+64*m.Lside+65536*(1+m.Lside)^2
  have hC : 0≤ C := by have hL := m.hLside; dsimp [C]; positivity
  have hD := s.diameter_tendsto
  have hrev : Tendsto (fun j=>m.reverse (s.diameter j)) atTop (𝓝 (m.reverse m.D0)) :=
    (hD.rpow_const (Or.inl m.D0_pos.ne')).mul_const _
  apply le_of_forall_pos_le_add
  intro t ht
  let err := t/(48+C+1)
  have herr : 0< err := div_pos ht (by linarith)
  have hv := f.sideFilled_eventually hcut herr
  have hc := f.unionGeometry.filled_eventually herr
  have hupper : ∀ᶠ j in atTop,f.defect j≤
      nativeConditionalLedgerBudget f.B (f.totalWidth j) cut (w+s.diameter j)
        (VS+err) (TC+err) (m.reverse (s.diameter j)) m.Lside := by
    filter_upwards [hv,hc] with j hvj hcj
    have hn := f.finite_budget hcut hw hRange j
    unfold nativeConditionalLedgerBudget at hn ⊢
    have hT : C*f.unionGeometry.filled j≤ C*(TC+err) :=
      mul_le_mul_of_nonneg_left (by simpa only [div_mul_eq_mul_div] using hcj) hC
    dsimp only [VS,C] at *
    linarith
  have hlimUpper : Tendsto (fun j=>nativeConditionalLedgerBudget f.B (f.totalWidth j) cut
      (w+s.diameter j) (VS+err) (TC+err) (m.reverse (s.diameter j)) m.Lside) atTop
      (𝓝 (nativeConditionalLedgerBudget f.B f.v cut (w+m.D0) (VS+err) (TC+err)
        (m.reverse m.D0) m.Lside)) := by
    unfold nativeConditionalLedgerBudget
    exact (((tendsto_const_nhds.add
      ((f.totalWidth_tendsto.const_mul _).mul ((hD.const_add w).pow 2))).add
      ((f.totalWidth_tendsto.const_mul 32).mul hrev)).add tendsto_const_nhds).add
        tendsto_const_nhds
  have hlimit := le_of_tendsto_of_tendsto f.defect_tendsto hlimUpper hupper
  have herrbound : (48+C)*err≤ t := by
    dsimp [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<48+C+1)).mpr
    nlinarith
  dsimp only [VS,TC] at hlimit
  unfold nativeConditionalLedgerBudget at hlimit ⊢
  dsimp only [C] at herrbound
  nlinarith

theorem thermal_le_band_budget {m : NativeBandModel} {s : NativeBandRefinement m}
    {bins : ℕ} {cut w : ℝ} (f : NativeBandFrame m s bins cut w)
    (hcut : 0< cut) (hw : 0< w) (hRange : m.Q^2*m.y≤(bins:ℝ)*w) :
    (∫u in 0..1,f.mask (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget bins m.bandMass cut (w+m.D0)
        (m.AS*(bins:ℝ)*m.Lside/(m.P*m.rho))
        (m.AC*m.bandMass/(m.P*m.rho^2)) (m.reverse m.D0) m.Lside := by
  have hn := f.thermal_le_native_budget hcut hw hRange
  have hB : f.B≤ bins := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f.label f.hlabel
  have hBR : (f.B:ℝ)≤ bins := by exact_mod_cast hB
  have hV := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBR m.AS_nonneg) m.hLside)
    (mul_pos m.P_pos m.rho_pos).le
  have hT := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left f.hvUpper m.AC_nonneg) (mul_pos m.P_pos (sq_pos_of_pos m.rho_pos)).le
  have hmean := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left f.hvUpper (by linarith [m.hLside] : 0≤76+64*m.Lside))
    (sq_nonneg (w+m.D0))
  have hrev := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left f.hvUpper (by norm_num : (0:ℝ)≤32))
    (m.reverse_nonneg m.D0_pos.le)
  have hcutB := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hBR (by norm_num : (0:ℝ)≤16)) hcut.le
  have hC : 0≤66+64*m.Lside+65536*(1+m.Lside)^2 := by have hL := m.hLside; positivity
  have hTc := mul_le_mul_of_nonneg_left hT hC
  unfold nativeConditionalLedgerBudget at hn ⊢
  nlinarith

end NativeBandFrame

theorem actual_native_ordinary_band_optimized
    (m : NativeBandModel) (s : NativeBandRefinement m) {cut : ℝ} (hcut : 0< cut)
    (constructed : ∀k : ℕ,1≤ k→NativeBandFrame m s k cut ((m.Q^2*m.y)/(k:ℝ))) :
    ∃k : ℕ,∃hk : 1≤ k,
      (k:ℝ)≤((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2 ∧
      (∫u in 0..1,(constructed k hk).mask (m.R u)*m.thermal u)≤
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)+16*(k:ℝ)*cut := by
  obtain ⟨k,hk,hks,hbudget⟩ := exists_integer_native_bin_scale m.hLside m.AS_nonneg m.AC_nonneg
    m.hbandMass m.rho_pos m.P_pos m.D0_pos.le (zero_le_one.trans m.hQ) m.hy.le
    (m.reverse_nonneg m.D0_pos.le) cut
  rw [mul_right_comm m.AS m.Lside (k:ℝ)] at hbudget
  have hcover := native_bin_width_coverage (zero_lt_one.trans_le m.hQ) m.hy hk
  exact ⟨k,hk,hks,((constructed k hk).thermal_le_band_budget hcut hcover.1 hcover.2).trans hbudget⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
