module

public import ComparisonNativeSideVariance
public import ComparisonNativeVarianceBinGeometry
public import ComparisonActualVarianceBinAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2400000

def nativeConditionalLedgerBudget (B : ℕ) (v cut eta V T R L : ℝ) : ℝ :=
  48*V+(76+64*L)*v*eta^2+32*v*R+
    (66+64*L+65536*(1+L)^2)*T+16*(B:ℝ)*cut

theorem actualBinsVarianceBudget_native_expansion (B : ℕ) (v cut eta V tauC R L : ℝ) :
    2*actualBinsVarianceBudget B v cut eta V tauC R L+
      (256*(1+L))^2*v*tauC=
      nativeConditionalLedgerBudget B v cut eta V (v*tauC) R L := by
  unfold actualBinsVarianceBudget nativeConditionalLedgerBudget
  ring

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r ∈ Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

section NativeConditionalAssembly
variable
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d)
    (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n : ℕ) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam ≤ b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r ∈ Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {delta Ucap Lcap E : ℝ} (hUcap : 0<Ucap) (hLcap : 0<Lcap) (hE : 0<E)
    (hbang : ∀ᵐ r,r ∈ Icc (0:ℝ) 1→H r<0→deriv α.val.val r=
      comparisonCap N delta Ucap Lcap E d (α.val.val r))
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0)
    (hcontact : ∀r ∈ U,H (sInf (ordConnectedComponent U r))=0 ∧
      (H (sSup (ordConnectedComponent U r))=0 ∨ sSup (ordConnectedComponent U r)=1))
variable (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
variable {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
local notation "Rc" => comparisonSweepQuantile hc hk hkc hm hM α
local notation "qc" => comparisonNativeClock hc hk hkc hm hM n b h α d lam
local notation "sc" => sampleClockSteps qc 0 as
local notation "Dc" => 9*Real.log N*((Lcap/N^delta)*Real.log ((1+Ucap)/Ucap))+
  2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) qc))
local notation "rad" => (fun i:Fin ((sc).length+1)=>Rc (physicalCutMass 0 sc (i:ℕ)))

include hN hlog hd hnd hlam hld hb hlb hh hh0 hH hJ hD hUcap hLcap hE hbang
  hopen hU hneg hcontact ho he hmesh in
theorem actual_comparison_native_conditional_finite_assembly
    (l : ℕ) (hl : 2<l) {xs y w : ℝ} (hxs : 0<xs) (hy : 0 ≤ y) (hw : 0<w)
    {K0 bins B : ℕ} (A : Finset (Fin ((sc).length+1)))
    (unit0 : Fin ((sc).length+1)→Fin K0)
    (hpos : ∀i ∈ A,0<pathMassDifferences sc 0 i)
    (hclass0 : ∀i ∈ A,∀j ∈ A,unit0 i=unit0 j ↔ wholeUnit U (rad i)=wholeUnit U (rad j))
    (hmassUpper : ∀i ∈ A,xs+physicalCutMass 0 sc i.val ≤ y)
    (hheightWidth : (physicalRawRatio (n+1) l sc 0 xs
      (Measure.pi fun j=>gaussianReal 0 (qc 0 j)) id measurable_id)^2*y ≤ (bins:ℝ)*w)
    (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (Js : Fin B→Finset (Fin ((sc).length+1)))
    (hbin : ∀bb,Js bb=NativeUnitHeight.bin
      (fun i=>physicalPathSecondMoment (n+1) sc (qc 0) i.val) A unit0 bins w (label bb))
    (K : Fin B→ℕ) (unit : ∀bb:Fin B,Fin ((sc).length+1)→Fin (K bb))
    (x : Fin B→ℕ→ℝ) (width : Fin B→ℝ)
    (hclass : ∀bb,∀i ∈ Js bb,∀j ∈ Js bb,
      unit bb i=unit bb j ↔ wholeUnit U (rad i)=wholeUnit U (rad j))
    (horder : ∀bb,MonotoneOn (unit bb) (Js bb:Set _))
    (hstart : ∀bb,x bb 0=0) (hend : ∀bb,x bb (K bb)=width bb)
    (hx : ∀bb,∀u:Fin (K bb),x bb u.val<x bb (u.val+1))
    (hmass : ∀bb,∀u:Fin (K bb),physicalSelectedUnitMass sc (Js bb) (unit bb) u=
      x bb (u.val+1)-x bb u.val)
    {cut v Lside a : ℝ} (hcut : 0<cut) (hwidth : ∀bb,2*cut ≤ width bb)
    (hv : ∑bb,width bb=v) (hvpos : 0<v)
    (hLside : 0 ≤ Lside) (hsideLog : ∀bb,Real.log (width bb/cut) ≤ Lside)
    (ha : 0<a) (ha1 : a ≤ 1)
    (hlower : ∀i ∈ A,a ≤ Rc (partitionPoint 0 as i.val))
    (hmesh0 : 0 ≤ mesh) (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1)) :
    let mu := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho
    let V := ∑bb,
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        qc α as (Js bb) (unit bb) (fun u=>sideSquareColumn (x bb) cut (width bb) u.val) r ∂mu)+
        4*mesh/cut)/α.val.val a
    let T := (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        qc α as (Finset.univ.biUnion Js) (fun _=>(0:Fin 1)) (fun _=>1) r ∂mu)+
        2*mesh)/(α.val.val a)^2
    let Q := physicalRawRatio (n+1) l sc 0 xs
      (Measure.pi fun j=>gaussianReal 0 (qc 0 j)) id measurable_id
    let reverse := Dc^(((l:ℝ)-2)/((l:ℝ)-1))*
      ((2*Q)^(2*l)*y^l)^(1/((l:ℝ)-1))
    (∑i,(∑bb,physicalSelectedCellMass sc (Js bb) i)*
      actualCutReplicaDefect (n+1) sc (qc 0) i.val
        (physicalPathSecondMoment (n+1) sc (qc 0) i.val)) ≤
      nativeConditionalLedgerBudget B v cut (w+Dc) V T reverse Lside := by
  dsimp only
  let mu := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho
  let V := ∑bb,
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        qc α as (Js bb) (unit bb) (fun u=>sideSquareColumn (x bb) cut (width bb) u.val) r ∂mu)+
        4*mesh/cut)/α.val.val a
  let T := (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
      qc α as (Finset.univ.biUnion Js) (fun _=>(0:Fin 1)) (fun _=>1) r ∂mu)+
      2*mesh)/(α.val.val a)^2
  let Q := physicalRawRatio (n+1) l sc 0 xs
    (Measure.pi fun j=>gaussianReal 0 (qc 0 j)) id measurable_id
  let reverse := Dc^(((l:ℝ)-2)/((l:ℝ)-1))*
    ((2*Q)^(2*l)*y^l)^(1/((l:ℝ)-1))
  let tauC := T/v
  have hsteps : OrderedSteps 0 sc := sampleClockSteps_ordered qc as ho
  have hsub (bb : Fin B) : Js bb⊆A := by
    intro i hi
    rw [hbin bb] at hi
    exact (Finset.mem_filter.mp hi).1
  have hdisjoint : Pairwise (fun bb cc=>Disjoint (Js bb) (Js cc)) := by
    intro bb cc hne
    apply Finset.disjoint_left.mpr
    intro i hib hic
    rw [hbin bb] at hib
    rw [hbin cc] at hic
    have hb := (Finset.mem_filter.mp hib).2
    have hc := (Finset.mem_filter.mp hic).2
    exact hne (hlabel (Fin.ext (hb.symm.trans hc)))
  have hαa : 0<α.val.val a := by
    have hp := inverseConstraint_strictMonoOn hc hk hkc α.property
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp) ⟨ha.le,ha1⟩ ha
    simpa only [α.property.1] using hp
  have hfloor := comparison_nativeCutMass_lowerRadius hc hk hkc hm hM qc α as ho A hlower
  have hstartA : ∀i ∈ A,0<physicalCutMass 0 sc i.val := fun i hi=>hαa.trans_le (hfloor i hi)
  have hD0 : 0 ≤ Dc := comparisonNativeDiameter_nonneg hc hk hkc hm hM
    hN hlog hd hlam n b h hb hlb hh hh0 α hUcap hLcap as ho hmesh
  have heta : 0 ≤ w+Dc := add_nonneg hw.le hD0
  have hQ0 : 0 ≤ Q := zero_le_one.trans
    (physicalRawRatio_one_le (n+1) l sc 0 xs _ id measurable_id)
  have hreverse0 : 0 ≤ reverse := mul_nonneg (Real.rpow_nonneg hD0 _)
    (Real.rpow_nonneg (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hQ0) _)
      (pow_nonneg hy _)) _)
  have hW0 (r : ℝ) : 0 ≤ comparisonNativeUnitColumnWeight hc hk hkc hm hM
      qc α as (Finset.univ.biUnion Js) (fun _=>(0:Fin 1)) (fun _=>1) r := by
    have hcol : ∀j,nativeSelectedColumn (Finset.univ.biUnion Js)
        (fun _=>(0:Fin 1)) (fun _=>1) j ∈ Icc (0:ℝ) 1 := by
      intro j
      unfold nativeSelectedColumn
      split_ifs <;> norm_num
    exact (radiusCellEnergyDensity_mem_Icc_bound Rc
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho _
      (show (0:ℝ) ≤ 1 by norm_num) hcol r).1
  have hT0 : 0 ≤ T := div_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (integral_nonneg
      (fun r=>mul_nonneg α.val.property.2.deriv_nonneg (hW0 r))))
      (mul_nonneg (by norm_num) hmesh0)) (sq_nonneg _)
  have htauC0 : 0 ≤ tauC := div_nonneg hT0 hvpos.le
  have htrace : (∑i,(∑bb,physicalSelectedCellMass sc (Js bb) i)*
      actualCutCovarianceEnergy (n+1) sc (qc 0) i.val) ≤ v*tauC := by
    have hn := comparisonNativeSelectedUnionCovarianceEnergy_le_integral hc hk hkc hm hM
      n dphys e d lam b h α as ho he hmesh hmesh0 Js hdisjoint ha ha1
      (fun bb i hi=>hlower i (hsub bb hi))
    have heq : v*tauC=T := by dsimp only [tauC];field_simp [hvpos.ne']
    rw [heq]
    exact hn
  have hvariance : (∑bb,actualBinSideVariance (n+1) (K bb) sc (qc 0)
      (Js bb) (unit bb) (x bb) cut (width bb)) ≤ V := by
    apply Finset.sum_le_sum
    intro bb _
    exact physical_actual_bin_variance_le_native_integral hc hk hkc hm hM
      n dphys e d lam b h α as ho he hmesh hmesh0 (Js bb) (unit bb) (x bb)
      (hstart bb) (hend bb) hcut (hwidth bb) (hx bb) ha ha1
      (fun i hi=>hlower i (hsub bb hi))
  have hheight := actual_comparison_native_bins_height_contract hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh l hl hxs hw
    A unit0 hpos hstartA hclass0 hmassUpper hheightWidth
  have hS : ∀bb,∀i ∈ Js bb,∀j ∈ Js bb,
      |physicalPathSecondMoment (n+1) sc (qc 0) j.val-
        physicalPathSecondMoment (n+1) sc (qc 0) i.val| ≤ w+Dc := by
    intro bb i hi j hj
    rw [hbin bb] at hi hj
    exact hheight (label bb) i hi j hj
  have hreverse (bb : Fin B) := actual_comparison_native_reverse_contracts hc hk hkc hm hM
    hN hlog hd hnd hlam hld n b h hb hlb hh hh0 α H J hH hJ hD
    hUcap hLcap hE hbang hopen hU hneg hcontact as ho he hmesh l hl hxs
    (Js bb) (unit bb) (fun i hi=>hpos i (hsub bb hi))
    (fun i hi=>hstartA i (hsub bb hi)) (hclass bb) (horder bb) (x bb) (hx bb)
    0 (width bb) cut (width bb-cut)
  have hmassPower (i : Fin ((sc).length+1)) (hi : i ∈ A) :
      ((2*Q)^(2*l)*(xs+physicalCutMass 0 sc i.val)^l)^(1/((l:ℝ)-1)) ≤
        ((2*Q)^(2*l)*y^l)^(1/((l:ℝ)-1)) := by
    have hmass0 : 0 ≤ xs+physicalCutMass 0 sc i.val :=
      add_nonneg hxs.le (physicalCutMass_mem sc hsteps i.val).1
    have hlR : (2:ℝ)<l := by exact_mod_cast hl
    apply Real.rpow_le_rpow
      (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hQ0) _) (pow_nonneg hmass0 _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmass0 (hmassUpper i hi) _)
        (pow_nonneg (mul_nonneg (by norm_num) hQ0) _))
      (div_nonneg zero_le_one (by linarith))
  have hreverseL : ∀bb,∀i j:Fin ((sc).length+1),i.val < j.val→
      fineCoupling (physicalSelectedCellMass sc (Js bb)) (unit bb)
        (fun u t=>coarseLeft (x bb) 0 cut (width bb-cut) u t) i j≠0→
      physicalSideMovementMoment (n+1) sc (qc 0) i.val j.val ≤ reverse := by
    intro bb i j hij hp
    obtain ⟨_,hj⟩ := physicalFineCoupling_mem_selected sc (Js bb) (unit bb) _ hp
    exact ((hreverse bb).1 i j hij hp).trans
      (mul_le_mul_of_nonneg_left (hmassPower j (hsub bb hj)) (Real.rpow_nonneg hD0 _))
  have hreverseR : ∀bb,∀i j:Fin ((sc).length+1),j.val < i.val→
      fineCoupling (physicalSelectedCellMass sc (Js bb)) (unit bb)
        (fun u t=>coarseRight (x bb) (width bb) cut (width bb-cut) u t) i j≠0→
      physicalSideMovementMoment (n+1) sc (qc 0) i.val j.val ≤ reverse := by
    intro bb i j hji hp
    obtain ⟨hi,_⟩ := physicalFineCoupling_mem_selected sc (Js bb) (unit bb) _ hp
    exact ((hreverse bb).2 i j hji hp).trans
      (mul_le_mul_of_nonneg_left (hmassPower i (hsub bb hi)) (Real.rpow_nonneg hD0 _))
  have hn := physical_selected_bins_defect_le_variance_budget (n+1) B sc hsteps (qc 0)
    K Js unit x width hstart hend hcut hwidth hx hmass heta htauC0 hreverse0
    hLside hsideLog hv hS hvariance htrace hreverseL hreverseR
  dsimp only at hn
  rw [actualBinsVarianceBudget_native_expansion] at hn
  have ht : v*tauC=T := by dsimp only [tauC];field_simp [hvpos.ne']
  rw [ht] at hn
  exact hn

end NativeConditionalAssembly
end
end OAI.SKFluctuations.LaplaceWindowFormalization
