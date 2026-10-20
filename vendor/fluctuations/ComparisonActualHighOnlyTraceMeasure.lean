module

public import ComparisonShiftedNativePhysicalConcentration
public import ComparisonActualHighOnlyInnovation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

theorem sampledCell_increment
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (before after : List PositiveMass) (v : PositiveMass)
    (ho : MassOrdered 0 (before++v::after))
    (hvorder : MassOrdered (partitionEnd 0 before) (v::after))
    (hhigh : a.data.s≤ partitionEnd 0 before) {z : ℝ} (hz : z≤1)
    (hRz : a.shiftedNativeModel.R v.val≤ z) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 (before++v::after)
    let ha : OrderedSteps 0 (steps++[]) := by simpa using sampleClockSteps_ordered m.q _ ho
    ((m.R v.val-m.R (partitionEnd 0 before)).toNNReal:ℝ)*
      physicalRootedCapCellTrace n dphys e (m.q 0) steps [] ha before.length≤
      (physicalPathSecondMoment (n+1) steps (m.q 0) (before.length+1)-
        physicalPathSecondMoment (n+1) steps (m.q 0) before.length)/
          ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)) := by
  dsimp only
  let m:=a.shiftedNativeModel
  let u:=partitionEnd 0 before
  let common:=sampleClockSteps m.q 0 before
  let st : GaussianStep (FeatureIndex (n+1)):=(v.val,fun j=>m.q v.val j-m.q u j)
  let extra:=sampleClockSteps m.q v.val after
  have hsteps : sampleClockSteps m.q 0 (before++v::after)=(common++[st])++extra := by
    rw [sampleClockSteps_append]
    simp only [sampleClockSteps]
    dsimp only [common,st,extra,u]
    simp only [List.append_assoc,List.singleton_append]
    rfl
  have hu : u∈Icc a.data.s 1:=⟨hhigh,(massOrdered_bounds hvorder).2⟩
  have hv : v.val∈Icc a.data.s 1:=⟨hhigh.trans hvorder.2.1,(massOrdered_bounds hvorder.2.2).2⟩
  let F:=((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z
  have hF : 0< F:=mul_pos (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d a.hlam z)
  let w : ℝ≥0:=(m.R v.val-m.R u).toNNReal
  have hsl : F*(w:ℝ)≤ st.2 (Sum.inl 0) := by
    have H:=a.high_field_radius_gap hN hlog hnd hu hv hvorder.2.1
    have hanti := (laplaceComparisonStrength_monotonicities a.data.hd.ne'
      a.hlam le_rfl).1
      (m.R_bounds v.val) ⟨(m.R_bounds v.val).1.trans hRz,hz⟩ hRz
    have hcoef : 0≤((1:ℝ)/3)/Real.log a.data.N:=by positivity
    have Hcoef:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hanti hcoef)
      (sub_nonneg.mpr (m.R_monotone hvorder.2.1))
    change _≤((m.hf v.val-m.hf u:ℝ≥0):ℝ)
    rw [NNReal.coe_sub_def,Real.coe_toNNReal _ (sub_nonneg.mpr
      (m.R_monotone hvorder.2.1))]
    change F*(m.R v.val-m.R u)≤ max ((a.hf v.val:ℝ)-(a.hf u:ℝ)) 0
    exact (Hcoef.trans H).trans (le_max_left _ _)
  have ha' : OrderedSteps 0 (((common++[st])++extra)++[]) := by
    rw [List.append_nil,←hsteps]
    exact sampleClockSteps_ordered m.q _ ho
  have hi:=physicalRootedCapCellTrace_full_mul_duration_le_increment n dphys e (m.q 0)
    common st extra [] ha' w hF (fun j=>by rfl) hsl
  simp only [←hsteps,List.append_nil] at hi
  simpa only [common,sampleClockSteps_length,List.append_nil,w,u,m,F] using hi

theorem sampledCell_increment_at_index
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (j : ℕ) (hj : j< as.length)
    (hhigh : a.data.s≤ partitionPoint 0 as j) {z : ℝ} (hz : z≤1)
    (hRz : a.shiftedNativeModel.R (partitionPoint 0 as (j+1))≤ z) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let ha : OrderedSteps 0 (steps++[]) := by simpa using sampleClockSteps_ordered m.q _ ho
    ((m.R (partitionPoint 0 as (j+1))-m.R (partitionPoint 0 as j)).toNNReal:ℝ)*
      physicalRootedCapCellTrace n dphys e (m.q 0) steps [] ha j≤
      (physicalPathSecondMoment (n+1) steps (m.q 0) (j+1)-
        physicalPathSecondMoment (n+1) steps (m.q 0) j)/
          ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)) := by
  have hdecomp : as.take j++as[j]::as.drop (j+1)=as:=by
    rw [←List.drop_eq_getElem_cons hj,List.take_append_drop]
  have hov : MassOrdered (partitionEnd 0 (as.take j)) (as[j]::as.drop (j+1)):=by
    rw [massPartition_take_end,←List.drop_eq_getElem_cons hj]
    exact massPartition_drop_ordered as ho j
  have hRz' : a.shiftedNativeModel.R as[j].val≤ z:=by
    simpa only [massPartition_point_succ_eq_getElem 0 as hj] using hRz
  have ht:=a.sampledCell_increment hN hlog hnd dphys e (as.take j) (as.drop (j+1)) as[j]
    (by simpa only [hdecomp] using ho) hov (by simpa only [massPartition_take_end] using hhigh) hz hRz'
  simpa only [hdecomp,List.length_take,min_eq_left hj.le,massPartition_take_end,
    ←massPartition_point_succ_eq_getElem 0 as hj] using ht

theorem radiusMeasure_interval_le
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hend : partitionEnd 0 as=1)
    {mesh p z : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh)
    (hp : (0:ℝ)< p) (hpz : p≤ z) (hz : z≤1) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    m.radiusMeasure dphys e as ho (Ioo p z)≤
      ENNReal.ofReal ((a.radiusS z-a.radiusS p)/F)+
        ENNReal.ofReal (2*(mesh*Cnode)/F+2*(mesh/m.c)) := by
  dsimp only
  let m:=a.shiftedNativeModel
  let steps:=sampleClockSteps m.q 0 as
  let ha : OrderedSteps 0 (steps++[]) := by simpa using sampleClockSteps_ordered m.q _ ho
  let C:=fun j=>physicalRootedCapCellTrace n dphys e (m.q 0) steps [] ha j
  let x:=fun j=>m.R (partitionPoint 0 as j)
  let y:=fun j=>physicalPathSecondMoment (n+1) steps (m.q 0) (min j as.length)
  let Sext:=fun r:ℝ=>a.radiusS (projIcc (0:ℝ) 1 zero_le_one r)
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) m.q
  have hSm := a.radius_moments
  have hSext : Monotone Sext:=by
    intro u v huv
    exact hSm.1 (projIcc _ _ _ u).property (projIcc _ _ _ v).property
      (monotone_projIcc zero_le_one huv)
  have hSextEq r (hr : r∈Icc (0:ℝ) 1) : Sext r=a.radiusS r:=by
    simp only [Sext,projIcc_of_mem zero_le_one hr]
  have hx : Monotone x:=m.R_monotone.comp (partitionPoint_mono as ho)
  have hy : Monotone y:=physicalSampledSecondMoment_clipped_monotone _ _ _ as ho
  have hC (j : ℕ) : C j∈Icc (0:ℝ) 1:=physicalRootedCapCellTrace_mem_Icc _ _ _ _ _ _ _ j
  have hF : 0< F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d a.hlam z))
  have hCn : 0≤ Cnode:=mul_nonneg (mul_nonneg (by norm_num)
    (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg _ _ (completedPathClock_monotone _ m.hbf m.hhf))
  have hnode (j : ℕ) (hj : j≤ as.length) (hxi : x j∈Icc p z) :
      |y j-Sext (x j)|≤ mesh*Cnode:=by
    have hxI := m.R_bounds (partitionPoint 0 as j)
    have hhigh : a.data.s< partitionPoint 0 as j:=
      a.radius_high_mass (hp.trans_le hxi.1)
    have huHigh : partitionPoint 0 as j∈Icc a.data.s 1:=
      ⟨hhigh.le,(partitionPoint_mem as ho j).2⟩
    rw [hSextEq _ hxI]
    change |physicalPathSecondMoment (n+1) steps (m.q 0) (min j as.length)-
      orderedPathS (n+1) a.bf a.hf (a.alpha.val.val (m.R (partitionPoint 0 as j)))|≤_
    rw [m.R_spec huHigh,min_eq_left hj]
    exact physicalSampledNodeSecondMoment_error n a.bf a.hf m.hbf m.hhf as ho hend hmesh
      j hj (a.data.hs.1.trans_lt hhigh)
  have hinc (j : ℕ) (hj : j< as.length) (hpj : p≤ x j) (hjz : x (j+1)≤ z) :
      (x (j+1)-x j)*C j≤(y (j+1)-y j)/F:=by
    have hhigh : a.data.s≤ partitionPoint 0 as j:=
      (a.radius_high_mass (hp.trans_le hpj)).le
    have ht:=a.sampledCell_increment_at_index hN hlog hnd dphys e as ho j hj hhigh hz hjz
    dsimp only at ht
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr (hx (Nat.le_succ j)))] at ht
    simpa only [y,min_eq_left hj.le,min_eq_left (by omega : j+1≤ as.length),
      C,x,m,steps,ha,F] using ht
  have hbound r : finiteRadiusCellDensity as.length x C r≤1:=by
    rw [←radiusCellEnergyDensity_eq_finite_sum m.R 0 as C r]
    exact (radiusCellEnergyDensity_mem_Icc _ m.R_monotone as ho C hC r).2
  have hwidth (j : ℕ) (_hj : j< as.length) : x (j+1)-x j≤ mesh/m.c:=
    a.sampled_radius_step_le as ho hmesh0 hmesh j
  have ht:=finite_radius_cell_measure_interval_le hx hy hSext hpz (mul_nonneg hmesh0 hCn) hF
    (div_nonneg hmesh0 m.hc.le) (fun j _=>(hC j).1) hwidth hbound hnode hinc
  rw [hSextEq p ⟨hp.le,hpz.trans hz⟩,hSextEq z ⟨hp.le.trans hpz,hz⟩] at ht
  simpa only [ShiftedNativeBandModel.radiusMeasure,ShiftedNativeBandModel.radiusDensity,
    physicalRadiusCellEnergyDensity,Nat.zero_add,radiusCellEnergyDensity_eq_finite_sum,
    m,steps,ha,C,x,y,F,Cnode] using ht

theorem radiusMeasure_interval_le_fixedStrength
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hend : partitionEnd 0 as=1)
    {mesh p q z : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh)
    (hp : (0:ℝ)< p) (hpq : p≤ q) (hqz : q≤ z) (hz : z≤1) :
    let m:=a.shiftedNativeModel
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    m.radiusMeasure dphys e as ho (Ioo p q)≤
      ENNReal.ofReal ((a.radiusS q-a.radiusS p)/F)+
        ENNReal.ofReal (2*(mesh*Cnode)/F+2*(mesh/m.c)) := by
  dsimp only
  let m:=a.shiftedNativeModel
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) z)
  let Fq:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) q)
  let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) m.q
  have hκ : 0<((1:ℝ)/3)/Real.log a.data.N:=div_pos (by norm_num) (by linarith)
  have hF : 0< F:=mul_pos (by positivity)
    (mul_pos hκ (laplaceComparisonStrength_pos a.data.d a.hlam z))
  have hFF : F≤ Fq:=by
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤(n+1:ℝ))
    apply mul_le_mul_of_nonneg_left _ hκ.le
    exact (laplaceComparisonStrength_monotonicities a.data.hd.ne'
      a.hlam le_rfl).1
      ⟨hp.le.trans hpq,hqz.trans hz⟩ ⟨hp.le.trans (hpq.trans hqz),hz⟩ hqz
  have hSp : 0≤ a.radiusS q-a.radiusS p:=sub_nonneg.mpr
    (a.radius_moments.1 ⟨hp.le,hpq.trans (hqz.trans hz)⟩
      ⟨hp.le.trans hpq,hqz.trans hz⟩ hpq)
  have hCn : 0≤ Cnode:=mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg _ _ (completedPathClock_monotone _ m.hbf m.hhf))
  have ht:=a.radiusMeasure_interval_le hN hlog hnd dphys e as ho hend hmesh hmesh0 hp hpq (hqz.trans hz)
  dsimp only at ht
  apply ht.trans
  apply add_le_add
  · exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hSp hF hFF)
  · apply ENNReal.ofReal_le_ofReal
    have H:=div_le_div_of_nonneg_left (show 0≤2*(mesh*Cnode) from by positivity) hF hFF
    dsimp only [F,Fq,Cnode,m] at H
    linarith

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
