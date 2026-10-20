module

public import ComparisonActualHighOnlyRetainedUnitGeometry
public import ComparisonNativeConditionalAssembly
public import ComparisonNativeLocalDiameterAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 32000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def Potential.retainedBin (P : a.Potential) {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (bb : Fin bins) : Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1)) :=
  NativeUnitHeight.bin
    (fun i=>physicalPathSecondMoment (n+1) (sampleClockSteps a.shiftedNativeModel.q 0 as)
      (a.shiftedNativeModel.q 0) i.val) (P.retainedRows c Dcuts ag zg as)
    (firstWholeUnitCell P.negativeSet (a.shiftedNativeModel.rowRadius as)) bins w bb

theorem Potential.retainedBin_subset (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    P.retainedBin c Dcuts ag zg as bins w bb⊆P.retainedRows c Dcuts ag zg as := Finset.filter_subset _ _

theorem Potential.retainedBin_exists_coordinates (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    Nonempty (NativeConstructedCoordinates (sampleClockSteps a.shiftedNativeModel.q 0 as)
      (P.retainedBin c Dcuts ag zg as bins w bb) (a.shiftedNativeModel.rowRadius as) P.negativeSet) := by
  apply exists_nativeConstructedCoordinates _ (sampleClockSteps_ordered _ _ ho) _ _ _
    (a.shiftedNativeModel.rowRadius_monotone as ho) P.negativeSet
  intro i hi
  exact ((P.retainedRows_mem c Dcuts ag zg as i).mp
    (P.retainedBin_subset c Dcuts ag zg as bins w bb hi)).2.2.1

def Potential.retainedBinCoordinates (P : a.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (bins : ℕ) (w : ℝ) (bb : Fin bins) :
    NativeConstructedCoordinates (sampleClockSteps a.shiftedNativeModel.q 0 as)
      (P.retainedBin c Dcuts ag zg as bins w bb) (a.shiftedNativeModel.rowRadius as) P.negativeSet :=
  Classical.choice (P.retainedBin_exists_coordinates c Dcuts ag zg as ho bins w bb)

private theorem physical_reverse_le_of_unit_oscillation
    (ell : ℕ) (hell : 2 < ell)
    (steps : List (GaussianStep (FeatureIndex (n+1)))) (hs : OrderedSteps 0 steps)
    (q0 : FeatureIndex (n+1)→ℝ≥0) {xs y diam : ℝ} (hxs : 0 < xs)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ steps.length)
    (hinc : physicalPathSecondMoment (n+1) steps q0 j-
      physicalPathSecondMoment (n+1) steps q0 i ≤ diam)
    (hmass : xs+physicalCutMass 0 steps j ≤ y) :
    physicalSideMovementMoment (n+1) steps q0 i j ≤ 
      diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*physicalRawRatio (n+1) ell steps 0 xs
          (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id)^(2*ell)*y^ell)^
            (1/((ell:ℝ)-1)) := by
  have hbase : 0 ≤ physicalPathSecondMoment (n+1) steps q0 j-
      physicalPathSecondMoment (n+1) steps q0 i :=
    sub_nonneg.mpr (physicalPathSecondMoment_mono (n+1) steps hs q0 hij hj)
  have hlR : (2:ℝ) < ell := by exact_mod_cast hell
  have hpow:=Real.rpow_le_rpow hbase hinc
    (div_nonneg (by linarith : 0 ≤ (ell:ℝ)-2) (by linarith : 0 ≤ (ell:ℝ)-1))
  have hraw:=physical_movement_fourth_le_raw_interpolation (n+1) ell hell steps hs q0 hxs hij (hj.trans (Nat.le_succ _))
  let Q:=physicalRawRatio (n+1) ell steps 0 xs
    (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
  have hQ : 0 ≤ Q := zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hm0 : 0 ≤ xs+physicalCutMass 0 steps j:=add_nonneg hxs.le (physicalCutMass_mem steps hs j).1
  have hmasspow:=pow_le_pow_left₀ hm0 hmass ell
  have hcoef : 0 ≤ (2*Q)^(2*ell):=by positivity
  have hlarge:=mul_le_mul_of_nonneg_left hmasspow hcoef
  have hlargepow:=Real.rpow_le_rpow (mul_nonneg hcoef (pow_nonneg hm0 _)) hlarge
    (div_nonneg zero_le_one (by linarith : 0 ≤ (ell:ℝ)-1))
  have hD : 0 ≤ diam:=hbase.trans hinc
  exact hraw.trans (mul_le_mul hpow hlargepow
    (Real.rpow_nonneg (mul_nonneg hcoef (pow_nonneg hm0 _)) _) (Real.rpow_nonneg hD _))

theorem Potential.retained_conditional_finite_assembly
    (P : a.Potential) {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=0) ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (Dcuts : Finset ℝ) {ag zg : ℝ} (hag : (0:ℝ) < ag) (_hzg : zg ≤ 1)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {v K : ℝ} (hv : 0 < v) (hK : 0 < K)
    (hleft : ∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E)
    (hspan : ∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v)
    (ell : ℕ) (hell : 2 < ell) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {bins B : ℕ} (hB : 0 < B) (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    {y w cut Lside : ℝ} (hw : 0 < w) (hcut : 0 < cut) (hLside : 0 ≤ Lside)
    (hmassY : a.xs+a.alpha.val.val zg ≤ y)
    (hheight : (physicalRawRatio (n+1) ell (sampleClockSteps a.shiftedNativeModel.q 0 as)
      0 a.xs (Measure.pi fun j=>gaussianReal 0 (a.shiftedNativeModel.q 0 j)) id measurable_id)^2*y ≤ 
        (bins:ℝ)*w)
    (hwidth : ∀bb : Fin B,2*cut ≤ 
      (P.retainedBinCoordinates c Dcuts ag zg as ho bins w (label bb)).x
        (P.retainedBinCoordinates c Dcuts ag zg as ho bins w (label bb)).K)
    (hsideLog : ∀bb : Fin B,Real.log (
      (P.retainedBinCoordinates c Dcuts ag zg as ho bins w (label bb)).x
        (P.retainedBinCoordinates c Dcuts ag zg as ho bins w (label bb)).K/cut) ≤ Lside)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1)) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Js:=fun bb=>P.retainedBin c Dcuts ag zg as bins w (label bb)
    let co:=fun bb=>P.retainedBinCoordinates c Dcuts ag zg as ho bins w (label bb)
    let width:=fun bb=>(co bb).x (co bb).K
    let mu:=m.radiusMeasure dphys e as ho
    let V:=∑bb,(2*(∫r,deriv a.alpha.val.val r*m.unitColumn as (Js bb) (co bb).unit
      (fun u=>sideSquareColumn (co bb).x cut (width bb) u.val) r∂mu)+4*mesh/cut)/a.alpha.val.val ag
    let Tau:=(2*(∫r,deriv a.alpha.val.val r*m.unitColumn as (Finset.univ.biUnion Js)
      (fun _=>(0:Fin 1)) (fun _=>1) r∂mu)+2*mesh)/(a.alpha.val.val ag)^2
    let diameter:=a.localCapDiameter v K+2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q))
    let Q:=physicalRawRatio (n+1) ell steps 0 a.xs
      (Measure.pi fun j=>gaussianReal 0 (m.q 0 j)) id measurable_id
    let reverse:=diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
    (∑i,(∑bb,physicalSelectedCellMass steps (Js bb) i)*
      actualCutReplicaDefect (n+1) steps (m.q 0) i.val
        (physicalPathSecondMoment (n+1) steps (m.q 0) i.val)) ≤ 
      nativeConditionalLedgerBudget B (∑bb,width bb) cut (w+diameter) V Tau reverse Lside := by
  dsimp only
  let m:=a.shiftedNativeModel
  let steps:=sampleClockSteps m.q 0 as
  let A:=P.retainedRows c Dcuts ag zg as
  let unit0:=firstWholeUnitCell P.negativeSet (m.rowRadius as)
  let Js:=fun bb : Fin B=>P.retainedBin c Dcuts ag zg as bins w (label bb)
  let co:=fun bb : Fin B=>P.retainedBinCoordinates c Dcuts ag zg as ho bins w (label bb)
  let width:=fun bb : Fin B=>(co bb).x (co bb).K
  let mu:=m.radiusMeasure dphys e as ho
  let V:=∑bb,(2*(∫r,deriv a.alpha.val.val r*m.unitColumn as (Js bb) (co bb).unit
    (fun u=>sideSquareColumn (co bb).x cut (width bb) u.val) r∂mu)+4*mesh/cut)/a.alpha.val.val ag
  let Tau:=(2*(∫r,deriv a.alpha.val.val r*m.unitColumn as (Finset.univ.biUnion Js)
    (fun _=>(0:Fin 1)) (fun _=>1) r∂mu)+2*mesh)/(a.alpha.val.val ag)^2
  let diameter:=a.localCapDiameter v K+2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) m.q))
  let Q:=physicalRawRatio (n+1) ell steps 0 a.xs
    (Measure.pi fun j=>gaussianReal 0 (m.q 0 j)) id measurable_id
  let reverse:=diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  let total:=∑bb,width bb
  let tauC:=Tau/total
  have hs : OrderedSteps 0 steps:=sampleClockSteps_ordered _ _ ho
  have hsub (bb : Fin B) : Js bb⊆A:=P.retainedBin_subset c Dcuts ag zg as bins w (label bb)
  have hdata i (hi : i∈A):=(P.retainedRows_mem c Dcuts ag zg as i).mp hi
  have hhigh : ∀bb,∀i∈Js bb,m.u0 ≤ partitionPoint 0 as i.val :=
    fun bb i hi=>(hdata i (hsub bb hi)).2.2.2.1
  have hlower : ∀bb,∀i∈Js bb,ag ≤ m.R (partitionPoint 0 as i.val) :=
    fun bb i hi=>(hdata i (hsub bb hi)).2.2.2.2.1
  have hdisjoint : Pairwise (fun bb cc=>Disjoint (Js bb) (Js cc)) := by
    intro bb cc hne
    apply Finset.disjoint_left.mpr
    intro i hib hic
    have hb:=(Finset.mem_filter.mp hib).2
    have hc:=(Finset.mem_filter.mp hic).2
    exact hne (hlabel (Fin.ext (hb.symm.trans hc)))
  have hmassUpper : ∀i∈A,a.xs+physicalCutMass 0 steps i.val ≤ y := by
    intro i hi
    have hd:=hdata i hi
    have hp:=partitionPoint_mem as ho i.val
    have hnode:=m.R_monotone (partitionPoint_mono as ho (Nat.le_succ i.val))
    have hh:=m.alpha.val.property.2 (hnode.trans hd.2.2.2.2.2)
    rw [m.R_spec ⟨hd.2.2.2.1,hp.2⟩] at hh
    rw [physicalCutMass_sampleClockSteps m.q 0 as i.val hd.1.le]
    linarith
  have hag1 : ag ≤ 1 := by
    let bb : Fin B:=⟨0,hB⟩
    have hstrict:=(co bb).strict_of_width hcut (hwidth bb)
    have hn : (Js bb).Nonempty := by
      by_contra hh
      have heq:=Finset.not_nonempty_iff_eq_empty.mp hh
      have hz0 : width bb=0 := by
        dsimp only [width]
        rw [(co bb).width]
        change physicalWindowMass steps 0 (Js bb)=0
        rw [heq]
        simp [physicalWindowMass]
      have hw0:=hwidth bb
      change 2*cut ≤ width bb at hw0
      linarith
    obtain ⟨i,hi⟩:=hn
    exact (hlower bb i hi).trans (m.R_bounds _).2
  have hvariance : (∑bb,actualBinSideVariance (n+1) (co bb).K steps (m.q 0)
      (Js bb) (co bb).unit (co bb).x cut (width bb)) ≤ V := by
    apply Finset.sum_le_sum
    intro bb _
    exact m.actual_bin_sideVariance_le_integral dphys e as ho he hmesh hmesh0
      (Js bb) (co bb).unit (hhigh bb) (co bb).x (co bb).start rfl hcut (hwidth bb)
      ((co bb).strict_of_width hcut (hwidth bb)) hag hag1 (hlower bb)
  have htrace0 : (∑i,(∑bb,physicalSelectedCellMass steps (Js bb) i)*
      actualCutCovarianceEnergy (n+1) steps (m.q 0) i.val) ≤ Tau :=
    m.selectedUnionCovarianceEnergy_le_integral dphys e as ho he hmesh hmesh0 Js hdisjoint
      hhigh hag hag1 hlower
  have hTau : 0 ≤ Tau := (Finset.sum_nonneg (fun i _=>mul_nonneg
    (Finset.sum_nonneg (fun bb _=>physicalSelectedCellMass_nonneg steps hs (Js bb) i))
    (actualCutCovarianceEnergy_nonneg (n+1) steps hs (m.q 0) i.val))).trans htrace0
  have hwidth0 : ∀bb : Fin B,0 ≤ width bb:=fun bb=>(by have HH:=hwidth bb;change 2*cut ≤ width bb at HH;linarith)
  have htotal : 0 < total := by
    let bb : Fin B:=⟨0,hB⟩
    have Hsingle:=Finset.single_le_sum (s:=Finset.univ) (f:=width)
      (fun j _=>hwidth0 j) (Finset.mem_univ bb)
    have HH:=hwidth bb
    change 2*cut ≤ width bb at HH
    exact (show 0 < width bb by linarith).trans_le Hsingle
  have htauC : 0 ≤ tauC:=div_nonneg hTau htotal.le
  have hvt : total*tauC=Tau := by dsimp only [tauC];field_simp [htotal.ne']
  have htrace : (∑i,(∑bb,physicalSelectedCellMass steps (Js bb) i)*
      actualCutCovarianceEnergy (n+1) steps (m.q 0) i.val) ≤ total*tauC:=by rw [hvt];exact htrace0
  have hosc:=P.retained_unit_oscillation c hwhole hcontacts Dcuts ag zg hN hlog hnd
    hv hK hleft hspan as ho he hmesh hmesh0
  have hCd : 0 ≤ a.localCapDiameter v K :=
    mul_nonneg (show 0≤9*Real.log a.data.N by linarith) a.cavityCapTravel_nonneg
  have hdiam : 0 ≤ diameter := by
    unfold diameter
    have hLn : 0 ≤ Real.log a.data.N:=by linarith
    have hQn:=a.data.hN;have hdn:=a.data.hd;have hEn:=a.data.hE
    have hCn:=clockVariationBound_nonneg (physicalFeatureCoordinateBound n) m.q
      (completedPathClock_monotone _ m.hbf m.hhf)
    have hEr:=ClockTree.errorJetVariation_nonneg 2 0 0
    positivity
  have hheightActual:=physical_native_unit_bins_profile_diameter (n+1) ell (by omega) steps hs
    (m.q 0) A unit0 a.hxs hw hmassUpper hheight
    (fun i hi j hj heq=>hosc i hi j hj ((firstWholeUnitCell_eq_iff P.negativeSet (m.rowRadius as) j i).mp heq).symm)
  have hS : ∀bb,∀i∈Js bb,∀j∈Js bb,
      |physicalPathSecondMoment (n+1) steps (m.q 0) j.val-
        physicalPathSecondMoment (n+1) steps (m.q 0) i.val| ≤ w+diameter := by
    intro bb i hi j hj
    exact hheightActual (label bb) hi hj
  have hQ : 0 ≤ Q := zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
  have hy : 0 ≤ y := (add_nonneg a.hxs.le (a.alpha.val.property.1 zg).1).trans hmassY
  have hreverse0 : 0 ≤ reverse := by
    dsimp only [reverse]
    exact mul_nonneg (Real.rpow_nonneg hdiam _)
      (Real.rpow_nonneg (mul_nonneg (by positivity) (pow_nonneg hy ell)) _)
  have hreverseL : ∀bb,∀i j : Fin (steps.length+1),i.val < j.val→
      fineCoupling (physicalSelectedCellMass steps (Js bb)) (co bb).unit
        (fun u t=>coarseLeft (co bb).x 0 cut (width bb-cut) u t) i j≠0→
      physicalSideMovementMoment (n+1) steps (m.q 0) i.val j.val ≤ reverse := by
    intro bb i j hij hP
    obtain ⟨hi,hj⟩:=physicalFineCoupling_mem_selected _ _ _ _ hP
    have heq:=nonzero_fineCoarseLeft_reverse_same_unit _ _ _ (co bb).order
      (co bb).x ((co bb).strict_of_width hcut (hwidth bb)) 0 cut (width bb-cut) hi hj hij hP
    have hsame:=((co bb).classes i hi j hj).mp heq
    have hh:=hosc i (hsub bb hi) j (hsub bb hj) hsame
    exact physical_reverse_le_of_unit_oscillation ell hell steps hs (m.q 0) a.hxs hij.le
      (by have HH:=(hdata j (hsub bb hj)).1;simpa only [steps,sampleClockSteps_length] using HH.le)
      (by linarith only [hh]) (hmassUpper j (hsub bb hj))
  have hreverseR : ∀bb,∀i j : Fin (steps.length+1),j.val < i.val→
      fineCoupling (physicalSelectedCellMass steps (Js bb)) (co bb).unit
        (fun u t=>coarseRight (co bb).x (width bb) cut (width bb-cut) u t) i j≠0→
      physicalSideMovementMoment (n+1) steps (m.q 0) i.val j.val ≤ reverse := by
    intro bb i j hji hP
    obtain ⟨hi,hj⟩:=physicalFineCoupling_mem_selected _ _ _ _ hP
    have heq:=nonzero_fineCoarseRight_reverse_same_unit _ _ _ (co bb).order
      (co bb).x ((co bb).strict_of_width hcut (hwidth bb)) (width bb) cut (width bb-cut) hi hj hji hP
    have hsame:=((co bb).classes i hi j hj).mp heq
    have hh:=hosc j (hsub bb hj) i (hsub bb hi) hsame.symm
    rw [physicalSideMovementMoment_comm (n+1) steps (m.q 0) i.val j.val]
    exact physical_reverse_le_of_unit_oscillation ell hell steps hs (m.q 0) a.hxs hji.le
      (by have HH:=(hdata i (hsub bb hi)).1;simpa only [steps,sampleClockSteps_length] using HH.le)
      (by linarith only [hh]) (hmassUpper i (hsub bb hi))
  have HH:=physical_selected_bins_defect_le_variance_budget (n+1) B steps hs (m.q 0)
    (fun bb=>(co bb).K) Js (fun bb=>(co bb).unit) (fun bb=>(co bb).x) width
    (fun bb=>(co bb).start) (fun _=>rfl) hcut hwidth
    (fun bb=>(co bb).strict_of_width hcut (hwidth bb)) (fun bb=>(co bb).mass)
    (add_nonneg hw.le hdiam) htauC hreverse0 hLside hsideLog rfl hS hvariance htrace hreverseL hreverseR
  dsimp only at HH
  rw [actualBinsVarianceBudget_native_expansion,hvt] at HH
  exact HH

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
