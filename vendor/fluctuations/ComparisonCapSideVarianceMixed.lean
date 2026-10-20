module

public import ComparisonCapSideTraceBroadAggregate
public import ComparisonCapSideVarianceFilled

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2600000
def fixedSliceContactWeight {ι : Type*} [Fintype ι]
    (slices : ι→Set ℝ) (weight : ι→ℝ) (A : Set ℝ) (w : ℝ→ℝ) (r : ℝ) : ℝ :=
  (∑i,(slices i).indicator (fun _=>weight i) r)+A.indicator w r

theorem fixedSliceContactWeight_measurable {ι : Type*} [Fintype ι]
    (slices : ι→Set ℝ) (weight : ι→ℝ) (hslices : ∀i,MeasurableSet (slices i))
    (A : Set ℝ) (hA : MeasurableSet A)
    (w : ℝ→ℝ) (hw : Measurable w) : Measurable (fixedSliceContactWeight slices weight A w) := by
  exact (Finset.measurable_sum _ (fun i _=>measurable_const.indicator (hslices i))).add
    (hw.indicator hA)

theorem fixedSliceContactWeight_nonneg {ι : Type*} [Fintype ι]
    (slices : ι→Set ℝ) (weight : ι→ℝ) (hweight : ∀i,0≤weight i) (A : Set ℝ)
    (w : ℝ→ℝ) (hw : ∀r,0≤w r) (r : ℝ) :
    0≤fixedSliceContactWeight slices weight A w r :=
  add_nonneg (Finset.sum_nonneg (fun i _=>indicator_nonneg (fun _ _=>hweight i) r))
    (indicator_nonneg (fun s _=>hw s) r)

theorem fixedSliceContactWeight_bound {ι : Type*} [Fintype ι]
    (slices : ι→Set ℝ) (weight : ι→ℝ) (hweight : ∀i,0≤weight i) (A : Set ℝ)
    (w : ℝ→ℝ) (hw : ∀r,0≤w r) {W : ℝ} (hW : 0≤W)
    (hwb : ∀r,‖w r‖≤W) (r : ℝ) :
    ‖fixedSliceContactWeight slices weight A w r‖≤(∑i,weight i)+W := by
  rw [Real.norm_eq_abs,abs_of_nonneg (fixedSliceContactWeight_nonneg slices weight hweight A w hw r)]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    by_cases hr : r∈slices i <;> simp [hr,hweight i]
  · by_cases hr : r∈A
    · simp only [indicator_of_mem hr]
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hwb r)
    · simpa only [indicator_of_notMem hr] using hW

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

include hm hM in
theorem comparison_fixedSliceContactWeight_integral {ι : Type*} [Fintype ι]
    (α : inverseIntegralConstraints 0 0 k M)
    {ag zg : ℝ} (hag : 0<ag) (hzg : zg≤1)
    (slices : ι→Set ℝ) (weight : ι→ℝ) (hslices : ∀i,MeasurableSet (slices i))
    (hsub : ∀i,slices i⊆Ioo ag zg)
    (A : Set ℝ) (hA : MeasurableSet A) (hAsub : A⊆Ioo ag zg)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hwb : ∀r,‖w r‖≤W)
    (μ : Measure ℝ) (hμ : μ≤volume) :
    Integrable (fun r=>deriv α.val.val r*fixedSliceContactWeight slices weight A w r) μ ∧
    (∫r,deriv α.val.val r*fixedSliceContactWeight slices weight A w r∂μ)=
      (∑i,weight i*(∫r in slices i,deriv α.val.val r∂μ))+
      (∫r in A,deriv α.val.val r*w r∂μ) := by
  have hiCap i := comparison_radiusWeight_integrableOn hm hM α hag hzg
    (slices i) (hslices i) (hsub i)
    (fun _=>weight i) measurable_const (fun _=>le_rfl : ∀r : ℝ,‖weight i‖≤‖weight i‖)
  have hiContact := comparison_radiusWeight_integrableOn hm hM α hag hzg
    A hA hAsub w hw hwb
  have heCap i : (fun r=>deriv α.val.val r*(slices i).indicator (fun _=>weight i) r)=
      (slices i).indicator (fun r=>deriv α.val.val r*weight i) := by
    funext r
    by_cases hr : r∈slices i <;> simp [hr]
  have heContact : (fun r=>deriv α.val.val r*A.indicator w r)=
      A.indicator (fun r=>deriv α.val.val r*w r) := by
    funext r
    by_cases hr : r∈A <;> simp [hr]
  have hIc i : Integrable (fun r=>deriv α.val.val r*
      (slices i).indicator (fun _=>weight i) r) μ := by
    rw [heCap]
    exact ((hiCap i).integrable_indicator (hslices i)).mono_measure hμ
  have hIA : Integrable (fun r=>deriv α.val.val r*A.indicator w r) μ := by
    rw [heContact]
    exact (hiContact.integrable_indicator hA).mono_measure hμ
  have heq : (fun r=>deriv α.val.val r*fixedSliceContactWeight slices weight A w r)=
      (fun r=>∑i,deriv α.val.val r*(slices i).indicator (fun _=>weight i) r)+
      (fun r=>deriv α.val.val r*A.indicator w r) := by
    funext r
    simp only [fixedSliceContactWeight,mul_add,Finset.mul_sum,Pi.add_apply]
  rw [heq]
  constructor
  · exact (integrable_finsetSum _ (fun i _=>hIc i)).add hIA
  · change (∫r,(∑i,deriv α.val.val r*(slices i).indicator
      (fun _=>weight i) r)+deriv α.val.val r*A.indicator w r∂μ)=_
    rw [integral_add (integrable_finsetSum _ (fun i _=>hIc i)) hIA,
      integral_finsetSum _ (fun i _=>hIc i),heContact,integral_indicator hA]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [heCap,integral_indicator (hslices i),integral_mul_const,mul_comm]

theorem comparisonPhysicalMixedSamplerTrace_eventually
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
        H (a i)=0 ∧ H (z i)=0 ∧ lo≤α.val.val (a i) ∧ α.val.val (z i)≤hi) ∨
      (((H (a i)=0 ∧ H (z i)=0) ∨ (a i=0 ∧ H (z i)=0) ∨ (H (a i)=0 ∧ z i=1)) ∧
        max (a i) ag < min (z i) zg ∧ U≤v i ∧ v i≤vmax ∧ V i∈Icc (0:ℝ) 1 ∧
        V i≤Kbroad*v i ∧ (∀r∈slices i,α.val.val r≤V i) ∧
        v i≤∫r in slices i,deriv α.val.val r))
    (hweight : ∀i,0≤weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc ag zg))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc ag zg))
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
    <;> ring
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
      have hr := comparisonPhysicalCapUnitTrace_eventually hc hk hkc hm hM
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
  have hcontact := comparisonPhysicalWeightedContactTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
    as mesh ho hend hmesh hmesh0 hlim hag hagz hzg Kb Kh hparent hfield w hw W
    (fun r _ _=>hwb r) (fun r _ _=>hw0 r) (show 0<ε/2 by positivity)
  have hA : MeasurableSet A := by
    let He := fun r=>H (projIcc (0:ℝ) 1 zero_le_one r)
    have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
      simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
    have hHe : Continuous He :=
      (continuousOn_iff_continuous_restrict.mp hHC).comp continuous_projIcc
    have heq : A=Ioo ag zg∩He ⁻¹' {0} := by
      ext r
      have hr01 (hr : r∈Ioo ag zg) : r∈Icc (0:ℝ) 1 :=
        ⟨hag.le.trans hr.1.le,hr.2.le.trans hzg⟩
      simp only [A,mem_setOf_eq,mem_inter_iff,mem_preimage,mem_singleton_iff]
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

theorem comparisonPhysicalMixedSideVarianceFilled_eventually
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
        H (a i)=0 ∧ H (z i)=0 ∧ lo≤α.val.val (a i) ∧ α.val.val (z i)≤hi) ∨
      (((H (a i)=0 ∧ H (z i)=0) ∨ (a i=0 ∧ H (z i)=0) ∨ (H (a i)=0 ∧ z i=1)) ∧
        max (a i) ag < min (z i) zg ∧ U≤v i ∧ v i≤vmax ∧ V i∈Icc (0:ℝ) 1 ∧
        V i≤Kbroad*v i ∧ (∀r∈slices i,α.val.val r≤V i) ∧
        v i≤∫r in slices i,deriv α.val.val r))
    (hweight : ∀i,0≤weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc ag zg))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc ag zg))
    (w : ℝ→ℝ) (hw : Measurable w) (W : ℝ)
    (hW : 0≤W) (hwb : ∀r,‖w r‖≤W) (hw0 : ∀r,0≤w r)
    (Ks : ℕ→ℕ)
    (selected : (j : ℕ)→Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 (as j)).length+1)))
    (unit : (j : ℕ)→Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 (as j)).length+1)→Fin (Ks j))
    (x : ℕ→ℕ→ℝ) (widths : ℕ→ℝ) {δ width : ℝ}
    (hδ : 0<δ) (hwidth : 2*δ≤width) (hwidths : ∀j,2*δ≤widths j)
    (hwidthlim : Tendsto widths atTop (𝓝 width))
    (hstart : ∀j,x j 0=0) (hxend : ∀j,x j (Ks j)=widths j)
    (hx : ∀j,∀u : Fin (Ks j),x j u.val<x j (u.val+1))
    (hunitMass : ∀j,∀u : Fin (Ks j),physicalSelectedUnitMass
      (sampleClockSteps (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 (as j))
      (selected j) (unit j) u=x j (u.val+1)-x j u.val)
    {cutRadius : ℝ} (hcut : 0<cutRadius) (hcut1 : cutRadius≤1)
    (hleft : ∀j,∀i∈selected j,cutRadius≤comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 (as j) i.val))
    (hsupport : ∀j,∀ᵐ r,r∉Ioo ag zg→
      comparisonNativeUnitColumnWeight hc hk hkc hm hM
        (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) α (as j)
        (selected j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r=0)
    (hcolumns : Tendsto (fun j=>∫r in Ioo ag zg,
      |comparisonNativeUnitColumnWeight hc hk hkc hm hM
        (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) α (as j)
        (selected j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r-
        fixedSliceContactWeight slices weight {r | r∈Ioo ag zg ∧ H r=0} w r|)
        atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    ∀ᶠ j in atTop,
      ((2*(∫r,deriv α.val.val r*
        comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
          (selected j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j))+
        4*mesh j/δ)/α.val.val cutRadius ≤
        (108*(Ko^2+(Kbroad+1)^2*(1+vmax/U)*Real.log ((1+U)/U)+1)*(Real.log N)^2/
          ((n+1:ℝ)*laplaceComparisonStrength d lam zg*α.val.val cutRadius))*
            Real.log (width/δ)+ε) ∧
      actualBinSideVariance (n+1) (Ks j) (sampleClockSteps q 0 (as j)) (q 0)
        (selected j) (unit j) (x j) δ (widths j)≤
      (108*(Ko^2+(Kbroad+1)^2*(1+vmax/U)*Real.log ((1+U)/U)+1)*(Real.log N)^2/
        ((n+1:ℝ)*laplaceComparisonStrength d lam zg*α.val.val cutRadius))*
          Real.log (width/δ)+ε := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  let domain := Ioo ag zg
  let A := {r | r∈domain ∧ H r=0}
  let fixed := fixedSliceContactWeight slices weight A w
  let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM
    q α (as j) (selected j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
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
      (continuousOn_iff_continuous_restrict.mp hHC).comp continuous_projIcc
    have heq : A=domain∩He ⁻¹' {0} := by
      ext r
      have hr01 (hr : r∈domain) : r∈Icc (0:ℝ) 1 :=
        ⟨hag.le.trans hr.1.le,hr.2.le.trans hzg⟩
      simp only [A,mem_setOf_eq,mem_inter_iff,mem_preimage,mem_singleton_iff]
      constructor <;> intro hr <;> refine ⟨hr.1,?_⟩ <;>
        simpa only [He,projIcc_of_mem zero_le_one (hr01 hr.1)] using hr.2
    rw [heq]
    exact measurableSet_Ioo.inter (hHe.measurable (measurableSet_singleton 0))
  have hAsub : A⊆domain := fun _ hr=>hr.1
  have hfixedMeas : Measurable fixed := fixedSliceContactWeight_measurable slices weight hslices A hA w hw
  have hfixed0 r : 0≤fixed r := fixedSliceContactWeight_nonneg slices weight hweight A w hw0 r
  have hsumWeight : 0≤∑i,weight i := Finset.sum_nonneg (fun i _=>hweight i)
  let B := (∑i,weight i)+W+2/δ
  have hfixedB r : ‖fixed r‖≤B :=
    (fixedSliceContactWeight_bound slices weight hweight A w hw0 hW hwb r).trans
      (by dsimp [B]; exact le_add_of_nonneg_right (div_nonneg (by norm_num) hδ.le))
  have hmoveMeas j : Measurable (moving j) :=
    comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j)
      (selected j) (unit j) _
  have hmoveB j r : ‖moving j r‖≤B := by
    have ht := comparisonNativeUnitColumnWeight_side_bound hc hk hkc hm hM q α (as j)
      (ho j) (selected j) (unit j) (x j) (hstart j) (hxend j) hδ (hwidths j) (hx j) r
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
  have hmassNative j : (∫r in domain,deriv α.val.val r*moving j r)≤2*Real.log (widths j/δ) := by
    rw [hmoveGlobal j volume le_rfl]
    exact comparisonNativeUnitColumnWeight_side_mass_le_log hc hk hkc hm hM
      q α (as j) (ho j) (hend j) (selected j) (unit j) (x j)
      (hstart j) (hxend j) hδ (hwidths j) (hx j) (hunitMass j)
  have hlogWidth : Tendsto (fun j=>2*Real.log (widths j/δ)) atTop
      (𝓝 (2*Real.log (width/δ))) := by
    have hratio : 0<width/δ := div_pos (by linarith) hδ
    exact ((Real.continuousAt_log hratio.ne').tendsto.comp
      (hwidthlim.div_const δ)).const_mul 2
  have hmass : mass≤2*Real.log (width/δ) := by
    apply le_of_forall_pos_le_add
    intro t ht
    have he := (tendsto_order.mp herror).2 (t/2) (by positivity)
    have hl := (tendsto_order.mp hlogWidth).2 (2*Real.log (width/δ)+t/2) (by linarith)
    obtain ⟨j,hj,hlogj⟩ := (he.and hl).exists
    have hn := dominated_setIntegral_difference_le domain domain (Subset.refl _)
      volume le_rfl (fun r=>deriv α.val.val r*moving j r)
      (fun r=>deriv α.val.val r*fixed r) (hmoveI j) hfixedI
    rw [hfixedGlobal volume] at hn
    have habs : (∫r in domain,|deriv α.val.val r*fixed r-deriv α.val.val r*moving j r|)=
        volumeError j := by simp only [volumeError,abs_sub_comm]
    rw [habs] at hn
    exact hn.trans (by linarith [hmassNative j])
  have hdecomp j := (comparison_fixedSliceContactWeight_integral hm hM α hag hzg
    slices weight hslices hSgroup A hA hAsub w hw hwb (μ j) (hdom j)).2
  have hvolDecomp := (comparison_fixedSliceContactWeight_integral hm hM α hag hzg
    slices weight hslices hSgroup A hA hAsub w hw hwb volume le_rfl).2
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
  let err := ε*α.val.val cutRadius/8
  have herr : 0<err := div_pos (mul_pos hε hcutMass) (by norm_num)
  have hfixedTrace := comparisonPhysicalMixedSamplerTrace_eventually hc hk hkc hm hM
    hN hlog hU hL hE hd hnd hlam hld hMdef n dphys e b h hb hlb hh hh0 α H J
    hH hJ hD hbang hzero hag hagz hzg hlo hKo hband hKbroad hvmax hcal a z v V weight
    ha haz hz slices hslices hScap hSgroup hneg hcase hweight as mesh ho hend hmesh hmesh0
    hlim Kb Kh hparent hfield w hw W hW hwb hw0 herr
  have herrorSmall := (tendsto_order.mp herror).2 err herr
  have hmeshSmall := (tendsto_order.mp hlim).2 (ε*α.val.val cutRadius*δ/8)
    (by positivity : 0<ε*α.val.val cutRadius*δ/8)
  filter_upwards [hfixedTrace,herrorSmall,hmeshSmall] with j hj he hmj
  have htraceFixed : (∫r,deriv α.val.val r*fixed r∂μ j)≤C*R*mass+err := hj
  have hmovingTrace := dominated_setIntegral_difference_le domain domain (Subset.refl _)
    (μ j) (hdom j) (fun r=>deriv α.val.val r*fixed r)
    (fun r=>deriv α.val.val r*moving j r) hfixedI (hmoveI j)
  rw [hfixedGlobal (μ j),hmoveGlobal j (μ j) (hdom j)] at hmovingTrace
  have hvar := physical_actual_bin_variance_le_native_integral hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j) (hend j) (hmesh j) (hmesh0 j)
    (selected j) (unit j) (x j) (hstart j) (hxend j) hδ (hwidths j) (hx j) hcut hcut1 (hleft j)
  have htrace : (∫r,deriv α.val.val r*moving j r∂μ j)≤
      C*R*(2*Real.log (width/δ))+2*err := by
    have hmassScaled := mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hR)
    nlinarith [hmovingTrace,htraceFixed]
  have hfinal : (2*(∫r,deriv α.val.val r*moving j r∂μ j)+4*mesh j/δ)/
      α.val.val cutRadius≤(4*C*R/α.val.val cutRadius)*Real.log (width/δ)+ε := by
    apply (div_le_iff₀ hcutMass).mpr
    dsimp only [err] at htrace
    have hmeshBound : 4*mesh j/δ≤ε*α.val.val cutRadius/2 := by
      apply (div_le_iff₀ hδ).mpr
      nlinarith
    field_simp [hcutMass.ne']
    nlinarith
  have hcEq : (4*C*R/α.val.val cutRadius)*Real.log (width/δ)=
      (108*(Ko^2+(Kbroad+1)^2*(1+vmax/U)*Real.log ((1+U)/U)+1)*(Real.log N)^2/
        ((n+1:ℝ)*laplaceComparisonStrength d lam zg*α.val.val cutRadius))*Real.log (width/δ) := by
    dsimp [C,R,Gamma]
    field_simp [hcutMass.ne',(laplaceComparisonStrength_pos d hlam zg).ne']
    <;> ring
  constructor
  · change (2*(∫r,deriv α.val.val r*moving j r∂μ j)+4*mesh j/δ)/
      α.val.val cutRadius≤_
    simpa only [hcEq] using hfinal
  · exact hvar.trans (by simpa only [hcEq] using hfinal)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
