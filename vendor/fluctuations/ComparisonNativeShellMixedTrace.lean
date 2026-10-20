module

public import ComparisonNativeEndpointMixedTrace
public import ComparisonNativeRegularContactTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2600000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonPhysicalRegularEndpointMixedSamplerTrace_eventually
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
    (a z v V weight : ι→ℝ) (ha : ∀i,0≤a i) (haz : ∀i,a i<z i) (hz : ∀i,z i≤1)
    (slices : ι→Set ℝ) (hslices : ∀i,MeasurableSet (slices i))
    (hScap : ∀i,slices i⊆Ioo (a i) (z i)) (hSgroup : ∀i,slices i⊆Ioo ag zg)
    (hneg : ∀i,∀r∈Ioo (a i) (z i),H r<0)
    (hcase : ∀i,
      (slices i=Ioo (a i) (z i) ∧ ag≤a i ∧ z i≤zg ∧
        H (a i)=0 ∧ (H (z i)=0 ∨ z i=1) ∧ lo≤α.val.val (a i) ∧ α.val.val (z i)≤hi) ∨
      (((H (a i)=0 ∧ H (z i)=0) ∨ (a i=0 ∧ H (z i)=0) ∨ (H (a i)=0 ∧ z i=1)) ∧
        max (a i) ag < min (z i) zg ∧ U≤v i ∧ v i≤vmax ∧ V i∈Icc (0:ℝ) 1 ∧
        V i≤Kbroad*v i ∧ (∀r∈slices i,α.val.val r≤V i) ∧
        v i≤∫r in slices i,deriv α.val.val r))
    (hweight : ∀i,0≤weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (hclock : NativePullbackClockRegularity α.val.val b h ag zg)
    (w : ℝ→ℝ) (hw : Measurable w) (W : ℝ)
    (hW : 0≤W) (hwb : ∀r,‖w r‖≤W) (hw0 : ∀r,0≤w r)
    {ε : ℝ} (hε : 0<ε) :
    let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
    let R := Ko^2+(Kbroad+1)^2*(1+vmax/U)*Real.log ((1+U)/U)+1
    let fixed := fixedSliceContactWeight slices weight {r | r∈Ioo ag zg ∧ H r=0} w
    ∀ᶠ j in atTop,
      (∫r,deriv α.val.val r*fixed r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
          (as j) (ho j))≤C*R*(∫r,deriv α.val.val r*fixed r)+ε := by
  dsimp only
  let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
  let Gamma := (Kbroad+1)^2*(1+vmax/U)*Real.log ((1+U)/U)
  let R := Ko^2+Gamma+1
  let A := {r | r∈Ioo ag zg ∧ H r=0}
  let fixed := fixedSliceContactWeight slices weight A w
  let totalWeight := ∑i,weight i
  have htw : 0≤totalWeight := Finset.sum_nonneg (fun i _=>hweight i)
  let err := ε/(2*(totalWeight+1))
  have herr : 0<err := div_pos hε (by positivity)
  have hlogpos : 0<Real.log N := by linarith
  have hT : 0≤Real.log ((1+U)/U) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hU).mpr
    linarith
  have hvmax0 : 0≤vmax := hU.le.trans hvmax
  have hGamma : 0≤Gamma := by dsimp [Gamma]; positivity
  have hR : 1≤R := by dsimp [R]; nlinarith [sq_nonneg Ko]
  have hKoR : Ko^2≤R := by dsimp [R]; linarith
  have hGammaR : Gamma≤R := by dsimp [R]; nlinarith [sq_nonneg Ko]
  have hC : 0≤C := by
    have hgpos := laplaceComparisonStrength_pos d hlam zg
    dsimp [C]
    positivity
  have hcommon (r : ℝ) : (9*Real.log N)/
      ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam r))=
      27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam r) := by
    field_simp [hlogpos.ne',(laplaceComparisonStrength_pos d hlam r).ne']
    ring
  have hcaps : ∀i,∀ᶠ j in atTop,
      (∫r in slices i,deriv α.val.val r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
          (as j) (ho j))≤C*R*(∫r in slices i,deriv α.val.val r)+err := by
    intro i
    have hmass : 0≤∫r in slices i,deriv α.val.val r :=
      integral_nonneg (fun r=>α.val.property.2.deriv_nonneg)
    rcases hcase i with ho | hbroad
    · have hMa : 0<M (α.val.val (a i)) := by
        rw [congrFun hMdef (α.val.val (a i))]
        exact (comparisonCap_first_term (δ:=δcap) (by linarith) hU hL hE hd.le
          (α.val.property.1 (a i)).1).1
      have hr := comparisonPhysicalLeftContactCapUnitTrace_eventually hc hk hkc hm hM
        hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
        (ha i) (haz i) (hz i) ho.2.2.2.1 ho.2.2.2.2.1 (hneg i)
        as mesh (by assumption) hend hmesh hmesh0 hlim hMa herr
      have hratio : M (α.val.val (z i))/M (α.val.val (a i))≤Ko^2 := by
        rw [congrFun hMdef (α.val.val (z i)),congrFun hMdef (α.val.val (a i))]
        exact comparisonCap_common_mass_band_ratio (by linarith) hU hL hE hd.le hlo
          hKo hband ho.2.2.2.2.2.1 ho.2.2.2.2.2.2 (α.val.property.1 (z i)).1
      have hg := (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).1
        ⟨(ha i).trans (haz i).le,hz i⟩ ⟨hag.le.trans hagz,hzg⟩ ho.2.2.1
      have hcoef : (9*Real.log N)/
          ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam (z i)))≤C := by
        rw [hcommon]
        exact div_le_div_of_nonneg_left (by positivity)
          (mul_pos (by positivity) (laplaceComparisonStrength_pos d hlam zg))
          (mul_le_mul_of_nonneg_left hg (by positivity))
      have hc0 : 0≤(9*Real.log N)/
          ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam (z i))) := by
        have hgpos := laplaceComparisonStrength_pos d hlam (z i)
        positivity
      have hprod := mul_le_mul (hratio.trans hKoR) hcoef hc0 (hR.trans' (by norm_num))
      have hcapMass : (∫r in slices i,deriv α.val.val r)=
          α.val.val (z i)-α.val.val (a i) := by
        rw [ho.1]
        have hsub : Icc (a i) (z i)⊆Icc (0:ℝ) 1 := Icc_subset_Icc (ha i) (hz i)
        have hac : AbsolutelyContinuousOnInterval α.val.val (a i) (z i) := by
          apply LipschitzOnWith.absolutelyContinuousOnInterval
          simpa only [uIcc_of_le (haz i).le] using
            (inverseIntegralConstraints_lipschitz hm hM α.property).mono hsub
        rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (haz i).le]
        exact hac.integral_deriv_eq_sub
      filter_upwards [hr] with j hj
      rw [←ho.1,←hcapMass] at hj
      have hscaled := mul_le_mul_of_nonneg_right hprod hmass
      nlinarith
    · have ht := comparisonPhysicalLocalizedBroadCapUnitTrace_eventually hc hk hkc hm hM
        hN hlog hU hL hE hd hnd hlam hld hMdef n dphys e b h hb hlb hh hh0 α H J
        hH hJ hD hbang (ha i) (haz i) (hz i) hag hzg hbroad.2.1 hbroad.1 (hneg i)
        hKbroad hbroad.2.2.1 hbroad.2.2.2.2.1 hbroad.2.2.2.2.2.1 hcal
        (slices i) (hslices i) (hScap i) (hSgroup i) hbroad.2.2.2.2.2.2.1
        hbroad.2.2.2.2.2.2.2 as mesh (by assumption) hend hmesh hmesh0 hlim herr
      have hprofile : (Kbroad+1)^2*(1+v i/U)*Real.log ((1+U)/U)≤Gamma := by
        apply mul_le_mul_of_nonneg_right _ hT
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact add_le_add le_rfl (div_le_div_of_nonneg_right hbroad.2.2.2.1 hU.le)
      have hscaled := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hprofile.trans hGammaR) hC) hmass
      filter_upwards [ht] with j hj
      dsimp only [C] at hscaled ⊢
      nlinarith
  have hcontact := comparisonPhysicalRegularContactTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
    as mesh ho hend hmesh hmesh0 hlim hag hagz hzg hclock w hw W hW hwb hw0 (show 0<ε/2 by positivity)
  have hA : MeasurableSet A := by
    let He := fun r=>H (projIcc (0:ℝ) 1 zero_le_one r)
    have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
    have hHe : Continuous He :=
      (continuousOn_iff_continuous_domRestrict.mp hHC).comp continuous_projIcc
    have heq : A=Ioo ag zg∩He ⁻¹' {0} := by
      ext r
      have hr01 (hr : r∈Ioo ag zg) : r∈Icc (0:ℝ) 1 :=
        ⟨hag.le.trans hr.1.le,hr.2.le.trans hzg⟩
      simp only [A,mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_singleton_iff]
      constructor <;> intro hr <;> refine ⟨hr.1,?_⟩ <;>
        simpa only [He,projIcc_of_mem zero_le_one (hr01 hr.1)] using hr.2
    rw [heq]
    exact measurableSet_Ioo.inter (hHe.measurable (measurableSet_singleton 0))
  have hAsub : A⊆Ioo ag zg := fun _ hr=>hr.1
  have hvolDecomp := (comparison_fixedSliceContactWeight_integral hm hM α hag hzg
    slices weight hslices hSgroup A hA hAsub w hw hwb volume le_rfl).2
  have hcontactMass0 : 0≤∫r in A,deriv α.val.val r*w r :=
    integral_nonneg (fun r=>mul_nonneg α.val.property.2.deriv_nonneg (hw0 r))
  have hsumcaps := Filter.eventually_all.mpr hcaps
  filter_upwards [hsumcaps,hcontact] with j hj hcont
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  have hdom : μ≤volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM n dphys e d lam b h α
      (as j) (ho j)).trans Measure.restrict_le_self
  have hdecomp := (comparison_fixedSliceContactWeight_integral hm hM α hag hzg
    slices weight hslices hSgroup A hA hAsub w hw hwb μ hdom).2
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    mul_le_mul_of_nonneg_left (hj i) (hweight i))
  have hs' : (∑i,weight i*(∫r in slices i,deriv α.val.val r∂μ))≤
      C*R*(∑i,weight i*(∫r in slices i,deriv α.val.val r))+err*totalWeight := by
    convert hs using 1
    dsimp only [totalWeight]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herrbound : err*totalWeight≤ε/2 := by
    dsimp only [err]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<2*(totalWeight+1))).mpr
    nlinarith
  rw [hcommon] at hcont
  have hcontactScaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hR hcontactMass0) hC
  change (∫r,deriv α.val.val r*fixed r∂μ)≤_
  rw [hdecomp]
  rw [hvolDecomp]
  dsimp only [C,A,R,Gamma] at hs' hcont hcontactScaled ⊢
  nlinarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
