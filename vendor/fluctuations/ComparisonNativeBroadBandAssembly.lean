module

public import ComparisonNativeShellMixedSideVariance
public import ComparisonNativeShellMixedUnionCovariance
public import ComparisonNativeBandAssembly
public import ComparisonNativeEndpointMixedUnionCovarianceRate
public import ComparisonNativeBroadUnitGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3400000
attribute [local instance] Classical.propDecidable

def nativeBroadPoints (width : ℝ) (i : ℕ) : ℝ := if i=0 then 0 else width

structure NativeBroadFrame (m : NativeBandModel) (s : NativeBandRefinement m) (cut : ℝ) where
  capA : ℝ
  capZ : ℝ
  ha : 0≤ capA
  haz : capA< capZ
  hz : capZ≤1
  hboundary : (m.H capA=0 ∧ m.H capZ=0) ∨ (capA=0 ∧ m.H capZ=0) ∨ (m.H capA=0 ∧ capZ=1)
  hnegative : ∀r∈Ioo capA capZ,m.H r<0
  slice : Set ℝ
  hsliceMeas : MeasurableSet slice
  hsliceCap : slice⊆Ioo capA capZ
  hsliceGroup : slice⊆Ioo m.ag m.zg
  hoverlap : max capA m.ag < min capZ m.zg
  scale : ℝ
  ceiling : ℝ
  hscale : m.U≤ scale
  hceiling : ceiling∈Icc (0:ℝ) 1
  hcomparable : ceiling≤4*scale
  hsliceCeiling : ∀r∈slice,m.alpha.val.val r≤ ceiling
  hsliceMass : scale≤∫r in slice,deriv m.alpha.val.val r
  hcal : m.d^3*m.Lcap*m.U≤ m.E
  selected : (j : ℕ)→Finset (Fin ((s.steps j).length+1))
  widths : ℕ→ℝ
  width : ℝ
  hwidth : 2*cut≤ width
  hwidths : ∀j,2*cut≤ widths j
  hwidthlim : Tendsto widths atTop (𝓝 width)
  hmass : ∀j,physicalSelectedUnitMass (s.steps j) (selected j) (fun _=>(0:Fin 1)) 0=widths j
  hmasslim : Tendsto (fun j=>∑i,physicalSelectedCellMass (s.steps j) (selected j) i) atTop (𝓝 width)
  hwidthMass : width=∫r in slice,deriv m.alpha.val.val r
  hpos : ∀j,∀i∈selected j,0< pathMassDifferences (s.steps j) 0 i
  hleft : ∀j,∀i∈selected j,m.cutRadius≤ m.R (partitionPoint 0 (s.as j) i.val)
  hcapRows : ∀j,∀i∈selected j,m.R (partitionPoint 0 (s.as j) i.val)∈Ioo capA capZ
  hmassUpper : ∀j,∀i∈selected j,m.xs+physicalCutMass 0 (s.steps j) i.val≤ m.y
  rawUpper : ∀j,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
    (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q
  hsideLog : ∀j,Real.log (widths j/cut)≤ m.Lside
  hsupportSide : ∀j,∀ᵐ r,r∉Ioo m.ag m.zg→comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (selected j) (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r=0
  hsupportMask : ∀j,∀ᵐ r,r∉Ioo m.ag m.zg→comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r=0
  hsideColumns : Tendsto (fun j=>∫r in Ioo m.ag m.zg,
    |comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)
      (selected j) (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r-
      fixedSliceContactWeight (fun _ : Fin 1=>slice)
        (fun _=>sideSquareColumn (nativeBroadPoints width) cut width 0)
        {r | r∈Ioo m.ag m.zg ∧ m.H r=0} (fun _=>0) r|) atTop (𝓝 0)
  hmaskColumns : Tendsto (fun j=>∫r in Ioo m.ag m.zg,
    |comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)
      (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r-
      fixedSliceContactWeight (fun _ : Fin 1=>slice) (fun _=>1)
        {r | r∈Ioo m.ag m.zg ∧ m.H r=0} (fun _=>0) r|) atTop (𝓝 0)
  hmaskPoint : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
    Tendsto (fun j=>comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
      m.q m.alpha (s.as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r)
      atTop (𝓝 (slice.indicator (fun _=>1) r))

namespace NativeBroadFrame

def loss {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) : ℝ := m.Ko^2+25*(1+f.scale/m.U)*Real.log ((1+m.U)/m.U)+1

def AS {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) : ℝ := 108*f.loss*(Real.log m.N)^2

def AC {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) : ℝ := 54*f.loss*(Real.log m.N)^2

def sideFilled {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (j : ℕ) : ℝ :=
  (2*(∫r,deriv m.alpha.val.val r*comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (f.selected j) (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints (f.widths j)) cut (f.widths j) u.val) r∂s.mu j)+
        4*s.mesh j/cut)/m.rho

def unionFilled {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (j : ℕ) : ℝ :=
  (2*(∫r,deriv m.alpha.val.val r*comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (f.selected j) (fun _=>(0:Fin 1)) (fun _=>1) r∂s.mu j)+2*s.mesh j)/m.rho^2

def defect {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (j : ℕ) : ℝ :=
  ∑i,physicalSelectedCellMass (s.steps j) (f.selected j) i*
    actualCutReplicaDefect (m.n+1) (s.steps j) (m.q 0) i.val
      (physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val)

theorem point_geometry {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (hcut : 0< cut) (j : ℕ) :
    nativeBroadPoints (f.widths j) 0=0 ∧ nativeBroadPoints (f.widths j) 1=f.widths j ∧
    (∀u:Fin 1,nativeBroadPoints (f.widths j) u.val< nativeBroadPoints (f.widths j) (u.val+1)) ∧
    (∀u:Fin 1,physicalSelectedUnitMass (s.steps j) (f.selected j) (fun _=>(0:Fin 1)) u=
      nativeBroadPoints (f.widths j) (u.val+1)-nativeBroadPoints (f.widths j) u.val) := by
  have hp : 0< f.widths j := by linarith [f.hwidths j]
  refine ⟨by simp [nativeBroadPoints],by simp [nativeBroadPoints],?_,?_⟩
  · intro u
    have hu : u.val=0 := by omega
    simpa only [hu,nativeBroadPoints,ite_true,Nat.zero_add,show (1:ℕ)≠0 by omega,ite_false] using hp
  · intro u
    have hu : u=0 := Fin.eq_zero u
    simpa [hu,nativeBroadPoints] using f.hmass j

theorem sideFilled_eventually {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (hcut : 0< cut) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ j in atTop,f.sideFilled j≤(f.AS/(m.P*m.rho))*Real.log (f.width/cut)+ε := by
  let points := fun j=>nativeBroadPoints (f.widths j)
  let weight := fun _ : Fin 1=>sideSquareColumn (nativeBroadPoints f.width) cut f.width 0
  have hcase : ∀i : Fin 1,
      ((fun _ : Fin 1=>f.slice) i=Ioo f.capA f.capZ ∧ m.ag≤ f.capA ∧ f.capZ≤ m.zg ∧
        m.H f.capA=0 ∧ m.H f.capZ=0 ∧ m.lo≤ m.alpha.val.val f.capA ∧ m.alpha.val.val f.capZ≤ m.hi) ∨
      (((m.H f.capA=0 ∧ m.H f.capZ=0) ∨ (f.capA=0 ∧ m.H f.capZ=0) ∨ (m.H f.capA=0 ∧ f.capZ=1)) ∧ max f.capA m.ag < min f.capZ m.zg ∧ m.U≤ f.scale ∧ f.scale≤ f.scale ∧
        f.ceiling∈Icc (0:ℝ) 1 ∧ f.ceiling≤4*f.scale ∧
        (∀r∈f.slice,m.alpha.val.val r≤ f.ceiling) ∧ f.scale≤∫r in f.slice,deriv m.alpha.val.val r) := by
    intro i
    exact Or.inr ⟨f.hboundary,f.hoverlap,f.hscale,le_rfl,f.hceiling,f.hcomparable,
      f.hsliceCeiling,f.hsliceMass⟩
  have hcase' := hcase
  have ht := comparisonPhysicalRegularMixedSideVarianceFilled_eventually
    m.hc m.hk m.hkc m.hm m.hM m.hN m.hlog m.hU m.hLcap m.hE m.hd m.hnd m.hlam m.hld
    m.hMdef m.n m.dphys m.e m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha m.H m.multiplier
    m.hH m.hJ m.hD m.hbang m.hzero m.hag m.hagz m.hzg m.hlo m.hKo m.hband
    (show (1:ℝ)≤4 by norm_num) f.hscale f.hcal
    (fun _ : Fin 1=>f.capA) (fun _=>f.capZ) (fun _=>f.scale) (fun _=>f.ceiling) weight
    (fun _=>f.ha) (fun _=>f.haz) (fun _=>f.hz) (fun _=>f.slice) (fun _=>f.hsliceMeas)
    (fun _=>f.hsliceCap) (fun _=>f.hsliceGroup) (fun _=>f.hnegative) hcase'
    (fun _=>sideSquareColumn_nonneg _ f.hwidth 0)
    s.as s.mesh s.ho s.he s.hm s.hm0 s.hmesh m.clockRegularity
    (fun _=>0) measurable_const 0 le_rfl (fun _=>by simp) (fun _=>le_rfl)
    (fun _=>1) f.selected (fun _ _=>(0:Fin 1)) points f.widths hcut f.hwidth f.hwidths f.hwidthlim
    (fun j=>(f.point_geometry hcut j).1) (fun j=>(f.point_geometry hcut j).2.1)
    (fun j=>(f.point_geometry hcut j).2.2.1) (fun j=>(f.point_geometry hcut j).2.2.2)
    m.hcut m.hcut1 f.hleft f.hsupportSide f.hsideColumns hε
  filter_upwards [ht] with j hj
  simpa only [AS,loss,sideFilled,NativeBandRefinement.mu,NativeBandModel.P,NativeBandModel.rho,
    Nat.cast_add,Nat.cast_one,points,show ((4:ℝ)+1)^2=25 by norm_num] using hj.1

theorem unionFilled_eventually {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ j in atTop,f.unionFilled j≤(f.AC/(m.P*m.rho^2))*f.width+ε := by
  have hcase : ∀i : Fin 1,
      ((fun _ : Fin 1=>f.slice) i=Ioo f.capA f.capZ ∧ m.ag≤ f.capA ∧ f.capZ≤ m.zg ∧
        m.H f.capA=0 ∧ (m.H f.capZ=0 ∨ f.capZ=1) ∧
        m.lo≤ m.alpha.val.val f.capA ∧ m.alpha.val.val f.capZ≤ m.hi) ∨
      (((m.H f.capA=0 ∧ m.H f.capZ=0) ∨ (f.capA=0 ∧ m.H f.capZ=0) ∨
        (m.H f.capA=0 ∧ f.capZ=1)) ∧ max f.capA m.ag < min f.capZ m.zg ∧
        m.U≤ f.scale ∧ f.scale≤ f.scale ∧ f.ceiling∈Icc (0:ℝ) 1 ∧ f.ceiling≤4*f.scale ∧
        (∀r∈f.slice,m.alpha.val.val r≤ f.ceiling) ∧ f.scale≤∫r in f.slice,deriv m.alpha.val.val r) := by
    intro i
    exact Or.inr ⟨f.hboundary,f.hoverlap,f.hscale,le_rfl,f.hceiling,f.hcomparable,
      f.hsliceCeiling,f.hsliceMass⟩
  have ht := comparisonPhysicalRegularEndpointMixedUnionCovariance_eventually
    m.hc m.hk m.hkc m.hm m.hM m.hN m.hlog m.hU m.hLcap m.hE m.hd m.hnd m.hlam m.hld
    m.hMdef m.n m.dphys m.e m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha m.H m.multiplier
    m.hH m.hJ m.hD m.hbang m.hzero m.hag m.hagz m.hzg m.hlo m.hKo m.hband
    (show (1:ℝ)≤4 by norm_num) f.hscale f.hcal
    (fun _ : Fin 1=>f.capA) (fun _=>f.capZ) (fun _=>f.scale) (fun _=>f.ceiling) (fun _=>1)
    (fun _=>f.ha) (fun _=>f.haz) (fun _=>f.hz) (fun _=>f.slice) (fun _=>f.hsliceMeas)
    (fun _=>f.hsliceCap) (fun _=>f.hsliceGroup) (fun _=>f.hnegative) hcase (fun _=>by norm_num)
    s.as s.mesh s.ho s.he s.hm s.hm0 s.hmesh m.clockRegularity
    (fun _=>0) measurable_const 0 le_rfl (fun _=>by simp) (fun _=>le_rfl)
    f.selected f.hmasslim m.hcut m.hcut1 f.hleft f.hsupportMask f.hmaskColumns hε
  filter_upwards [ht] with j hj
  simpa only [AC,loss,unionFilled,NativeBandRefinement.mu,NativeBandModel.P,NativeBandModel.rho,
    Nat.cast_add,Nat.cast_one,show ((4:ℝ)+1)^2=25 by norm_num] using hj.1

theorem sampled_increment {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (j : ℕ) {i t : Fin ((s.steps j).length+1)}
    (hi : i∈f.selected j) (ht : t∈f.selected j) (hit : i.val≤ t.val) :
    physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val≤ s.diameter j := by
  have hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→m.H r<0→deriv m.alpha.val.val r=
      comparisonCap m.N m.delta m.U m.Lcap m.E m.d (m.alpha.val.val r) := by
    filter_upwards [m.hbang] with r hr hr01 hrH
    simpa only [congrFun m.hMdef (m.alpha.val.val r)] using hr hr01 hrH
  have htravel := potential_comparison_cap_interval_travel (zero_lt_one.trans_le m.hN) m.hU m.hLcap m.hE m.hd
    (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property)
    (fun r _=>m.alpha.val.property.1 r) hbang f.ha f.hz f.haz.le f.hnegative
  have hmass := partitionPoint_mono (s.as j) (s.ho j) hit
  have hrad := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha hmass
  have hinc := actual_variableEndpoint_comparison_cap_increment_endpoint_cases
    m.hc m.hk m.hkc m.hm m.hM m.hN m.hlog m.hd m.hnd m.hlam m.hld (m.n+1) (by omega)
    m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha m.H m.multiplier m.hH m.hJ m.hD f.ha f.hz
    (f.hcapRows j i hi) (f.hcapRows j t ht) hrad f.hboundary f.hnegative
  have hleft := comparison_nativeCutMass_lowerRadius m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha (s.as j) (s.ho j) (f.selected j) (f.hleft j)
  have hui : 0< partitionPoint 0 (s.as j) i.val := by
    have hh := m.rho_pos.trans_le (hleft i hi)
    simpa only [NativeBandRefinement.steps,
      physicalCutMass_sampleClockSteps m.q 0 (s.as j) i.val (by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)] using hh
  have hut : 0< partitionPoint 0 (s.as j) t.val := hui.trans_le hmass
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have herr := physicalSampledNodeSecondMoment_increment_le m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (s.as j) (s.ho j) (s.he j) (s.hm j)
    (by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)
    (by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ t.isLt) hui hut
  rw [←comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha
    (partitionPoint_mem (s.as j) (s.ho j) i.val),
    ←comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha
    (partitionPoint_mem (s.as j) (s.ho j) t.val)] at herr
  have hlength := mul_le_mul_of_nonneg_left htravel.2.1
    (by linarith [m.hlog] : 0≤9*Real.log m.N)
  dsimp only [NativeBandRefinement.diameter,NativeBandModel.D0,NativeBandModel.Cnode,
    NativeBandModel.bf,NativeBandModel.hf,NativeBandModel.q,comparisonNativeCompletedClock,
    NativeBandRefinement.steps] at *
  linarith

theorem sampled_oscillation {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (j : ℕ) {i t : Fin ((s.steps j).length+1)}
    (hi : i∈f.selected j) (ht : t∈f.selected j) :
    |physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val|≤ s.diameter j := by
  have ho := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  rcases le_total i.val t.val with hit|hti
  · rw [abs_of_nonneg (sub_nonneg.mpr
      (physicalPathSecondMoment_mono _ _ ho _ hit (by simpa only [NativeBandRefinement.steps] using Nat.le_of_lt_succ t.isLt)))]
    exact f.sampled_increment j hi ht hit
  · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr
      (physicalPathSecondMoment_mono _ _ ho _ hti (by simpa only [NativeBandRefinement.steps] using Nat.le_of_lt_succ i.isLt)))]
    exact f.sampled_increment j ht hi hti

theorem sampled_reverse {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (j : ℕ) {i t : Fin ((s.steps j).length+1)}
    (hi : i∈f.selected j) (ht : t∈f.selected j) (hit : i.val≤ t.val) :
    physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val≤ m.reverse (s.diameter j) := by
  have ho := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  have hbase : 0≤ physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) t.val-
      physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val :=
    sub_nonneg.mpr (physicalPathSecondMoment_mono _ _ ho _ hit (by simpa only [NativeBandRefinement.steps] using Nat.le_of_lt_succ t.isLt))
  have hlR : (2:ℝ)< m.l := by exact_mod_cast m.hl
  have hp : 0≤((m.l:ℝ)-2)/((m.l:ℝ)-1) := div_nonneg (by linarith) (by linarith)
  have hd := Real.rpow_le_rpow hbase (f.sampled_increment j hi ht hit) hp
  have hn := physical_movement_fourth_le_raw_interpolation (m.n+1) m.l m.hl
    (s.steps j) ho (m.q 0) m.hxs hit (by omega)
  have hraw0 : 0≤ physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id :=
    zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hmass0 : 0≤ m.xs+physicalCutMass 0 (s.steps j) t.val :=
    add_nonneg m.hxs.le (physicalCutMass_mem _ ho _).1
  have hrawPower := pow_le_pow_left₀ (mul_nonneg (by norm_num) hraw0)
    (mul_le_mul_of_nonneg_left (f.rawUpper j) (by norm_num : (0:ℝ)≤2)) (2*m.l)
  have hmassPower := pow_le_pow_left₀ hmass0 (f.hmassUpper j t ht) m.l
  have hprod := mul_le_mul hrawPower hmassPower (pow_nonneg hmass0 _)
    (pow_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans m.hQ)) _)
  have hrp := Real.rpow_le_rpow
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hraw0) _) (pow_nonneg hmass0 _))
    hprod (div_nonneg zero_le_one (by linarith : 0≤(m.l:ℝ)-1))
  have hfinal := mul_le_mul hd hrp (Real.rpow_nonneg
    (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hraw0) _) (pow_nonneg hmass0 _)) _)
    (Real.rpow_nonneg (s.diameter_nonneg j) _)
  exact hn.trans (by simpa only [NativeBandModel.reverse] using hfinal)

theorem finite_budget {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (hcut : 0< cut) (j : ℕ) :
    f.defect j≤ nativeConditionalLedgerBudget 1 (f.widths j) cut (s.diameter j)
      (f.sideFilled j) (f.unionFilled j) (m.reverse (s.diameter j)) m.Lside := by
  have ho := sampleClockSteps_ordered m.q (s.as j) (s.ho j)
  have hp : 0< f.widths j := by linarith [f.hwidths j]
  have hpoints := f.point_geometry hcut j
  have hc := comparisonNativeWeightedCovarianceEnergy_le_integral
    m.hc m.hk m.hkc m.hm m.hM m.n m.dphys m.e m.d m.lam m.b m.h m.alpha
    (s.as j) (s.ho j) (s.he j) (s.hm j) (s.hm0 j) (f.selected j)
    (fun _=>(0:Fin 1)) (fun _=>1) (fun _=>by norm_num) (by norm_num : (0:ℝ)≤1)
    (fun _=>le_rfl) m.hcut m.hcut1 (f.hleft j)
  dsimp only at hc
  rw [nativeWeightedCovarianceEnergy_one] at hc
  simp only [mul_one] at hc
  change (∑i,physicalSelectedCellMass (s.steps j) (f.selected j) i*
    actualCutCovarianceEnergy (m.n+1) (s.steps j) (m.q 0) i.val)≤ f.unionFilled j at hc
  have hT0 : 0≤ f.unionFilled j := (Finset.sum_nonneg (fun i _=>mul_nonneg
    (physicalSelectedCellMass_nonneg _ ho _ i)
    (actualCutCovarianceEnergy_nonneg _ _ ho _ _))).trans hc
  let tauC := f.unionFilled j/f.widths j
  have htau0 : 0≤ tauC := div_nonneg hT0 hp.le
  have htau : f.widths j*tauC=f.unionFilled j := by dsimp [tauC];field_simp [hp.ne']
  have hv := physical_actual_bin_variance_le_native_integral
    m.hc m.hk m.hkc m.hm m.hM m.n m.dphys m.e m.d m.lam m.b m.h m.alpha
    (s.as j) (s.ho j) (s.he j) (s.hm j) (s.hm0 j) (f.selected j) (fun _=>(0:Fin 1))
    (nativeBroadPoints (f.widths j)) hpoints.1 hpoints.2.1 hcut (f.hwidths j)
    hpoints.2.2.1 m.hcut m.hcut1 (f.hleft j)
  dsimp only at hv
  change actualBinSideVariance (m.n+1) 1 (s.steps j) (m.q 0) (f.selected j)
    (fun _=>(0:Fin 1)) (nativeBroadPoints (f.widths j)) cut (f.widths j)≤ f.sideFilled j at hv
  have hreverseL : ∀bb:Fin 1,∀i t:Fin ((s.steps j).length+1),i.val< t.val→
      fineCoupling (physicalSelectedCellMass (s.steps j) (f.selected j)) (fun _=>(0:Fin 1))
        (fun u v=>coarseLeft (nativeBroadPoints (f.widths j)) 0 cut (f.widths j-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val≤ m.reverse (s.diameter j) := by
    intro bb i t hit hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    exact f.sampled_reverse j hi ht hit.le
  have hreverseR : ∀bb:Fin 1,∀i t:Fin ((s.steps j).length+1),t.val< i.val→
      fineCoupling (physicalSelectedCellMass (s.steps j) (f.selected j)) (fun _=>(0:Fin 1))
        (fun u v=>coarseRight (nativeBroadPoints (f.widths j)) (f.widths j) cut (f.widths j-cut) u v) i t≠0→
      physicalSideMovementMoment (m.n+1) (s.steps j) (m.q 0) i.val t.val≤ m.reverse (s.diameter j) := by
    intro bb i t hti hP
    obtain ⟨hi,ht⟩ := physicalFineCoupling_mem_selected _ _ _ _ hP
    rw [physicalSideMovementMoment_comm _ _ _ i.val t.val]
    exact f.sampled_reverse j ht hi hti.le
  have hn := physical_selected_bins_defect_le_variance_budget (v:=f.widths j) (m.n+1) 1 (s.steps j) ho (m.q 0)
    (fun _=>1) (fun _=>f.selected j) (fun _ _=>(0:Fin 1))
    (fun _=>nativeBroadPoints (f.widths j)) (fun _=>f.widths j)
    (fun _=>hpoints.1) (fun _=>hpoints.2.1) hcut (fun _=>f.hwidths j)
    (fun _=>hpoints.2.2.1) (fun _=>hpoints.2.2.2) (s.diameter_nonneg j) htau0
    (m.reverse_nonneg (s.diameter_nonneg j)) m.hLside (fun _=>f.hsideLog j)
    (by simp) (fun _ i hi t ht=>f.sampled_oscillation j hi ht)
    (by simpa using hv) (by simpa only [Fin.sum_univ_one,htau] using hc) hreverseL hreverseR
  dsimp only at hn
  rw [actualBinsVarianceBudget_native_expansion,htau] at hn
  simpa only [Fin.sum_univ_one,defect] using hn

theorem defect_tendsto {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) :
    Tendsto f.defect atTop (𝓝 (∫u in 0..1,f.slice.indicator (fun _=>1) (m.R u)*m.thermal u)) := by
  have hmasks := comparisonNativeMask_mass_L1_tendsto_of_radius_ae m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha s.as s.ho s.he (fun _=>1) f.selected (fun _ _=>(0:Fin 1))
    (f.slice.indicator (fun _=>1)) f.hmaskPoint
  have hmasks' : Tendsto (fun j=>∫u in 0..1,
      |nativeSelectedMassMask m.q (s.as j) (f.selected j) u-
        f.slice.indicator (fun _=>1) (m.R u)|) atTop (𝓝 0) := by
    simpa only [nativeSelectedMassMask,intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc] using hmasks
  have hmeas : Measurable (fun u=>f.slice.indicator (fun _ : ℝ=> (1:ℝ)) (m.R u)) :=
    (measurable_const.indicator f.hsliceMeas).comp
      (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hbound : ∀u∈Ioc (0:ℝ) 1,f.slice.indicator (fun _ : ℝ=> (1:ℝ)) (m.R u)∈Icc (0:ℝ) 1 := by
    intro u hu
    by_cases hs:m.R u∈f.slice <;> simp [hs]
  exact actual_comparison_native_selected_defect_tendsto m.hc m.hk m.hkc m.hm m.hM
    m.n m.hd.ne' m.hlam.le m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha s.as s.mesh s.ho s.he s.hm
    s.hmesh f.selected _ hmeas hbound hmasks'

theorem thermal_le_native_budget {m : NativeBandModel} {s : NativeBandRefinement m} {cut : ℝ}
    (f : NativeBroadFrame m s cut) (hcut : 0< cut) :
    (∫u in 0..1,f.slice.indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeConditionalLedgerBudget 1 f.width cut m.D0
        (f.AS/(m.P*m.rho)*Real.log (f.width/cut))
        (f.AC*f.width/(m.P*m.rho^2)) (m.reverse m.D0) m.Lside := by
  let VS := f.AS/(m.P*m.rho)*Real.log (f.width/cut)
  let TC := f.AC*f.width/(m.P*m.rho^2)
  let C := 66+64*m.Lside+65536*(1+m.Lside)^2
  have hC : 0≤ C := by have hL:=m.hLside;dsimp [C];positivity
  have hD := s.diameter_tendsto
  have hrev : Tendsto (fun j=>m.reverse (s.diameter j)) atTop (𝓝 (m.reverse m.D0)) :=
    (hD.rpow_const (Or.inl m.D0_pos.ne')).mul_const _
  apply le_of_forall_pos_le_add
  intro t ht
  let err := t/(48+C+1)
  have herr : 0< err := div_pos ht (by linarith)
  have hv := f.sideFilled_eventually hcut herr
  have hc := f.unionFilled_eventually herr
  have hupper : ∀ᶠ j in atTop,f.defect j≤ nativeConditionalLedgerBudget 1 (f.widths j) cut
      (s.diameter j) (VS+err) (TC+err) (m.reverse (s.diameter j)) m.Lside := by
    filter_upwards [hv,hc] with j hvj hcj
    have hn := f.finite_budget hcut j
    unfold nativeConditionalLedgerBudget at hn ⊢
    have hT : C*f.unionFilled j≤ C*(TC+err) :=
      mul_le_mul_of_nonneg_left (by simpa only [div_mul_eq_mul_div] using hcj) hC
    have hV : 48*f.sideFilled j≤48*(VS+err) :=
      mul_le_mul_of_nonneg_left hvj (by norm_num : (0:ℝ)≤48)
    exact hn.trans (add_le_add (add_le_add (add_le_add (add_le_add hV le_rfl) le_rfl) hT) le_rfl)
  have hlimUpper : Tendsto (fun j=>nativeConditionalLedgerBudget 1 (f.widths j) cut
      (s.diameter j) (VS+err) (TC+err) (m.reverse (s.diameter j)) m.Lside) atTop
      (𝓝 (nativeConditionalLedgerBudget 1 f.width cut m.D0 (VS+err) (TC+err)
        (m.reverse m.D0) m.Lside)) := by
    unfold nativeConditionalLedgerBudget
    exact (((tendsto_const_nhds.add
      ((f.hwidthlim.const_mul _).mul (hD.pow 2))).add
      ((f.hwidthlim.const_mul 32).mul hrev)).add tendsto_const_nhds).add tendsto_const_nhds
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

end NativeBroadFrame
end OAI.SKFluctuations.LaplaceWindowFormalization
