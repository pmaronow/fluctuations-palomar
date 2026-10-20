module

public import ComparisonNativeEndpointMixedUnionCovarianceRate
public import ComparisonNativeShellMixedTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonPhysicalRegularEndpointMixedUnionCovariance_eventually
    {ι : Type*} [Fintype ι]
    {N δcap U L E d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N)
    (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (hMdef : M=comparisonCap N δcap U L E d)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→deriv α.val.val r=M (α.val.val r))
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    {ag zg lo hi Ko Kbroad vmax : ℝ} (hag : 0<ag) (hagz : ag≤zg) (hzg : zg≤1)
    (hlo : 0≤lo) (hKo : 1≤Ko) (hband : hi+U≤Ko*(lo+U))
    (hKbroad : 1≤Kbroad) (hvmax : U≤vmax) (hcal : d^3*L*U≤E)
    (a z vSlice V weight : ι→ℝ) (ha : ∀i,0≤a i) (haz : ∀i,a i<z i) (hz : ∀i,z i≤1)
    (slices : ι→Set ℝ) (hslices : ∀i,MeasurableSet (slices i))
    (hScap : ∀i,slices i⊆Ioo (a i) (z i)) (hSgroup : ∀i,slices i⊆Ioo ag zg)
    (hneg : ∀i,∀r∈Ioo (a i) (z i),H r<0)
    (hcase : ∀i,
      (slices i=Ioo (a i) (z i) ∧ ag≤a i ∧ z i≤zg ∧
        H (a i)=0 ∧ (H (z i)=0 ∨ z i=1) ∧ lo≤α.val.val (a i) ∧ α.val.val (z i)≤hi) ∨
      (((H (a i)=0 ∧ H (z i)=0) ∨ (a i=0 ∧ H (z i)=0) ∨ (H (a i)=0 ∧ z i=1)) ∧
        max (a i) ag < min (z i) zg ∧ U≤vSlice i ∧ vSlice i≤vmax ∧ V i∈Icc (0:ℝ) 1 ∧
        V i≤Kbroad*vSlice i ∧ (∀r∈slices i,α.val.val r≤V i) ∧
        vSlice i≤∫r in slices i,deriv α.val.val r))
    (hweight : ∀i,0≤weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (hclock : NativePullbackClockRegularity α.val.val b h ag zg)
    (w : ℝ→ℝ) (hw : Measurable w) (W : ℝ)
    (hW : 0≤W) (hwb : ∀r,‖w r‖≤W) (hw0 : ∀r,0≤w r)
    (selected : (j : ℕ)→Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 (as j)).length+1)))
    {v : ℝ}
    (hmasslim : Tendsto (fun j=>∑i,physicalSelectedCellMass
      (sampleClockSteps (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 (as j))
      (selected j) i) atTop (𝓝 v))
    {cutRadius : ℝ} (hcut : 0<cutRadius) (hcut1 : cutRadius≤1)
    (hleft : ∀j,∀i∈selected j,cutRadius≤comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 (as j) i.val))
    (hsupport : ∀j,∀ᵐ r,r∉Ioo ag zg→
      comparisonNativeUnitColumnWeight hc hk hkc hm hM
        (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) α (as j)
        (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r=0)
    (hcolumns : Tendsto (fun j=>∫r in Ioo ag zg,
      |comparisonNativeUnitColumnWeight hc hk hkc hm hM
        (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) α (as j)
        (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r-
        fixedSliceContactWeight slices weight {r | r∈Ioo ag zg ∧ H r=0} w r|)
        atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    let R := Ko^2+(Kbroad+1)^2*(1+vmax/U)*Real.log ((1+U)/U)+1
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    ∀ᶠ j in atTop,
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α (as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1) r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j))+2*mesh j)/(α.val.val cutRadius)^2≤
      (54*R*(Real.log N)^2/
        ((n+1:ℝ)*laplaceComparisonStrength d lam zg*(α.val.val cutRadius)^2))*v+ε ∧
      (∑i,physicalSelectedCellMass (sampleClockSteps q 0 (as j)) (selected j) i*
        actualCutCovarianceEnergy (n+1) (sampleClockSteps q 0 (as j)) (q 0) i.val)≤
      (54*R*(Real.log N)^2/
        ((n+1:ℝ)*laplaceComparisonStrength d lam zg*(α.val.val cutRadius)^2))*v+ε := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  let domain := Ioo ag zg
  let A := {r | r∈domain ∧ H r=0}
  let fixed := fixedSliceContactWeight slices weight A w
  let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM
    q α (as j) (selected j) (fun _=>(0:Fin 1)) (fun _=>1)
  let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
  let Gamma := (Kbroad+1)^2*(1+vmax/U)*Real.log ((1+U)/U)
  let R := Ko^2+Gamma+1
  let mass := ∫r,deriv α.val.val r*fixed r
  let volumeError := fun j=>∫r in domain,
    |deriv α.val.val r*moving j r-deriv α.val.val r*fixed r|
  let μ := fun j=>comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  have hA : MeasurableSet A := by
    let He := fun r=>H (projIcc (0:ℝ) 1 zero_le_one r)
    have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
    have hHe : Continuous He :=
      (continuousOn_iff_continuous_domRestrict.mp hHC).comp continuous_projIcc
    have heq : A=domain∩He ⁻¹' {0} := by
      ext r
      have hr01 (hr : r∈domain) : r∈Icc (0:ℝ) 1 :=
        ⟨hag.le.trans hr.1.le,hr.2.le.trans hzg⟩
      simp only [A,mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_singleton_iff]
      constructor <;> intro hr <;> refine ⟨hr.1,?_⟩ <;>
        simpa only [He,projIcc_of_mem zero_le_one (hr01 hr.1)] using hr.2
    rw [heq]
    exact measurableSet_Ioo.inter (hHe.measurable (measurableSet_singleton 0))
  have hAsub : A⊆domain := fun _ hr=>hr.1
  have hfixedMeas : Measurable fixed := fixedSliceContactWeight_measurable slices weight hslices A hA w hw
  have hfixed0 r : 0≤fixed r := fixedSliceContactWeight_nonneg slices weight hweight A w hw0 r
  have hsumWeight : 0≤∑i,weight i := Finset.sum_nonneg (fun i _=>hweight i)
  let B := (∑i,weight i)+W+1
  have hfixedB r : ‖fixed r‖≤B :=
    (fixedSliceContactWeight_bound slices weight hweight A w hw0 hW hwb r).trans
      (by dsimp [B]; linarith)
  have hmoveMeas j : Measurable (moving j) :=
    comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j)
      (selected j) (fun _=>(0:Fin 1)) (fun _=>1)
  have hmoveB j r : ‖moving j r‖≤B := by
    have hcol : ∀i,nativeSelectedColumn (selected j) (fun _=>(0:Fin 1))
        (fun _=>1) i ∈ Icc (0:ℝ) 1 := by
      intro i
      unfold nativeSelectedColumn
      split_ifs <;> norm_num
    have ht := radiusCellEnergyDensity_mem_Icc_bound
      (comparisonSweepQuantile hc hk hkc hm hM α)
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) (as j) (ho j) _
      (show (0:ℝ)≤1 by norm_num) hcol r
    change moving j r ∈ Icc (0:ℝ) 1 at ht
    rw [Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact ht.2.trans (by dsimp [B]; linarith)
  have herror := comparison_inverse_weight_L1_tendsto hm hM α hag hzg fixed hfixedMeas
    moving hmoveMeas hfixedB hmoveB hcolumns
  have hdom j : μ j≤volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
      n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  have hfixedI : IntegrableOn (fun r=>deriv α.val.val r*fixed r) domain :=
    comparison_radiusWeight_integrableOn hm hM α hag hzg domain measurableSet_Ioo
      (Subset.refl _) fixed hfixedMeas hfixedB
  have hmoveI j : IntegrableOn (fun r=>deriv α.val.val r*moving j r) domain :=
    comparison_radiusWeight_integrableOn hm hM α hag hzg domain measurableSet_Ioo
      (Subset.refl _) (moving j) (hmoveMeas j) (hmoveB j)
  have hfixedSupport r (hr : r∉domain) : fixed r=0 := by
    have hcap i : r∉slices i := fun hc=>hr (hSgroup i hc)
    have hnA : r∉A := fun h=>hr h.1
    dsimp only [fixed,fixedSliceContactWeight]
    rw [indicator_of_notMem hnA,add_zero]
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (hcap i) _
  have hfixedGlobal (ν : Measure ℝ) :
      (∫r in domain,deriv α.val.val r*fixed r∂ν)=(∫r,deriv α.val.val r*fixed r∂ν) := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun r hr=>by rw [hfixedSupport r hr,mul_zero])
  have hmoveGlobal j (ν : Measure ℝ) (hν : ν≤volume) :
      (∫r in domain,deriv α.val.val r*moving j r∂ν)=(∫r,deriv α.val.val r*moving j r∂ν) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_mono hν (hsupport j)] with r hr hrd
    rw [show moving j r=0 from hr hrd,mul_zero]
  have hmassNative j : (∫r in domain,deriv α.val.val r*moving j r)=
      ∑i,physicalSelectedCellMass (sampleClockSteps q 0 (as j)) (selected j) i := by
    rw [hmoveGlobal j volume le_rfl]
    rw [comparisonNativeUnitColumnWeight_mass hc hk hkc hm hM q α (as j) (ho j) (hend j)]
    rw [←selected_mass_grouping]
    apply Finset.sum_congr rfl
    intro i _
    unfold physicalSelectedCellMass
    split_ifs <;> simp_all
  have hmass : mass≤v := by
    apply le_of_forall_pos_le_add
    intro t ht
    have he := (tendsto_order.mp herror).2 (t/2) (by positivity)
    have hl := (tendsto_order.mp hmasslim).2 (v+t/2) (by linarith)
    obtain ⟨j,hj,hvj⟩ := (he.and hl).exists
    have hn := dominated_setIntegral_difference_le domain domain (Subset.refl _)
      volume le_rfl (fun r=>deriv α.val.val r*moving j r)
      (fun r=>deriv α.val.val r*fixed r) (hmoveI j) hfixedI
    rw [hfixedGlobal volume] at hn
    have habs : (∫r in domain,|deriv α.val.val r*fixed r-deriv α.val.val r*moving j r|)=
        volumeError j := by simp only [volumeError,abs_sub_comm]
    rw [habs,hmassNative] at hn
    exact hn.trans (by linarith)
  have hT : 0≤Real.log ((1+U)/U) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hU).mpr
    linarith
  have hvmax0 : 0≤vmax := hU.le.trans hvmax
  have hGamma : 0≤Gamma := by dsimp [Gamma]; positivity
  have hR : 0≤R := by dsimp [R]; positivity
  have hC : 0≤C := by
    have hp := laplaceComparisonStrength_pos d hlam zg
    dsimp [C]
    positivity
  have hcutMass : 0<α.val.val cutRadius := by
    have ht := inverseConstraint_strictMonoOn hc hk hkc α.property
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) ⟨hcut.le,hcut1⟩ hcut
    simpa only [α.property.1] using ht
  let err := ε*(α.val.val cutRadius)^2/8
  have herr : 0<err := div_pos (mul_pos hε (sq_pos_of_pos hcutMass)) (by norm_num)
  have hfixedTrace := comparisonPhysicalRegularEndpointMixedSamplerTrace_eventually hc hk hkc hm hM
    hN hlog hU hL hE hd hnd hlam hld hMdef n dphys e b h hb hlb hh hh0 α H J
    hH hJ hD hbang hzero hag hagz hzg hlo hKo hband hKbroad hvmax hcal a z vSlice V weight
    ha haz hz slices hslices hScap hSgroup hneg hcase hweight as mesh ho hend hmesh hmesh0
    hlim hclock w hw W hW hwb hw0 herr
  have herrorSmall := (tendsto_order.mp herror).2 err herr
  have hmeshSmall := (tendsto_order.mp hlim).2 (ε*(α.val.val cutRadius)^2/8)
    (by positivity : 0<ε*(α.val.val cutRadius)^2/8)
  filter_upwards [hfixedTrace,herrorSmall,hmeshSmall] with j hj he hmj
  have htraceFixed : (∫r,deriv α.val.val r*fixed r∂μ j)≤C*R*mass+err := hj
  have hmovingTrace := dominated_setIntegral_difference_le domain domain (Subset.refl _)
    (μ j) (hdom j) (fun r=>deriv α.val.val r*fixed r)
    (fun r=>deriv α.val.val r*moving j r) hfixedI (hmoveI j)
  rw [hfixedGlobal (μ j),hmoveGlobal j (μ j) (hdom j)] at hmovingTrace
  have hcov := comparisonNativeWeightedCovarianceEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j) (hend j) (hmesh j) (hmesh0 j)
    (selected j) (fun _=>(0:Fin 1)) (fun _=>1) (fun _=>by norm_num)
    (show (0:ℝ)≤1 by norm_num) (fun _=>le_rfl) hcut hcut1 (hleft j)
  dsimp only at hcov
  rw [nativeWeightedCovarianceEnergy_one] at hcov
  simp only [mul_one] at hcov
  have htrace : (∫r,deriv α.val.val r*moving j r∂μ j)≤
      C*R*v+2*err := by
    have hmassScaled := mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hR)
    nlinarith [hmovingTrace,htraceFixed]
  have hfinal : (2*(∫r,deriv α.val.val r*moving j r∂μ j)+2*mesh j)/
      (α.val.val cutRadius)^2≤(2*C*R/(α.val.val cutRadius)^2)*v+ε := by
    apply (div_le_iff₀ (sq_pos_of_pos hcutMass)).mpr
    dsimp only [err] at htrace
    have hmeshBound : 2*mesh j≤ε*(α.val.val cutRadius)^2/4 := by nlinarith
    field_simp [hcutMass.ne']
    nlinarith
  have hcEq : (2*C*R/(α.val.val cutRadius)^2)*v=
      (54*R*(Real.log N)^2/
        ((n+1:ℝ)*laplaceComparisonStrength d lam zg*(α.val.val cutRadius)^2))*v := by
    dsimp [C]
    field_simp [hcutMass.ne',(laplaceComparisonStrength_pos d hlam zg).ne']
    ring
  rw [hcEq] at hfinal
  exact ⟨hfinal,hcov.trans hfinal⟩

end
end OAI.SKFluctuations.LaplaceWindowFormalization
