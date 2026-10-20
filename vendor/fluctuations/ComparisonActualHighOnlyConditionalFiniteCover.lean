module

public import ComparisonActualHighOnlyWholeCapCover
public import ComparisonActualHighOnlyLocalCapThermalCover
public import ComparisonActualHighOnlyLocalOrdinaryCover
public import ComparisonActualHighOnlyConditionalErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}

namespace WholeCapBroadSampler
variable {cap : ShiftedCapInterval a P}
theorem actual_conditional_cover_ae (f : WholeCapBroadSampler cap) :
    ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),a.shiftedNativeModel.R u∈Ioo cap.left cap.right →
      u ≤ min a.massCoverBase 1 ∨∃i:Fin f.count,a.shiftedNativeModel.R u∈f.slice i := by
  let m:=a.shiftedNativeModel
  have hfinite : (Set.range (fun i:Fin f.count=>f.node (i.val+1))).Countable:=
    (Set.finite_range _).countable
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    hfinite.ae_notMem (volume.restrict (Icc (0:ℝ) 1))] with u hu hcuts hcap
  have huHigh : u∈Icc a.data.s 1:=⟨(m.R_high_mass (cap.hleft.trans_lt hcap.1)).le,hu.2⟩
  have hr:=m.R_bounds u
  have hs:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property
  have hA:=hs ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩ hr hcap.1
  have hB:=hs hr ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩ hcap.2
  rw [m.R_spec huHigh] at hA hB
  by_cases hlow:u≤a.massCoverBase
  · exact Or.inl (le_min hlow hu.2)
  · have hret : u∈Ioc (max (a.alpha.val.val cap.left) a.massCoverBase)
      (a.alpha.val.val cap.right):=⟨max_lt hA (lt_of_not_ge hlow),hB.le⟩
    obtain ⟨i,hi⟩:=nativeBroadSlice_cover a.massCoverBase
      (max (a.alpha.val.val cap.left) a.massCoverBase) (a.alpha.val.val cap.right) f.hgap hret
    refine Or.inr ⟨i,?_⟩
    exact (m.massSlice_quantile_mem (f.nodes_mem i).1 (f.nodes_mem i).2 hu).mpr
      ⟨hi.1,lt_of_le_of_ne hi.2 (fun he=>hcuts ⟨i,he.symm⟩)⟩
end WholeCapBroadSampler

abbrev ConditionalSmallCap {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ) :=
  {i:ι // a.alpha.val.val (c i).right ≤ 8*a.massCoverBase ∧
    (A∩Ioo (c i).left (c i).right).Nonempty}
abbrev conditionalSmallCapUnion {ι : Type*} (c : ι→ShiftedCapInterval a P) (A : Set ℝ) : Set ℝ :=
  ⋃i:ConditionalSmallCap c A,Ioo (c i.val).left (c i.val).right

theorem local_finite_cap_conditional_cover_ae {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) :
    ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),
      a.shiftedNativeModel.R u∈A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet) →
      a.shiftedNativeModel.R u∈A∩P.contactSet ∨
      a.shiftedNativeModel.R u∈relevantComparableCapUnion c A ∨
      (∃p:RelevantBroadSlice c A,a.shiftedNativeModel.R u∈actualBroadSlice c p.val) ∨
      a.shiftedNativeModel.R u∈conditionalSmallCapUnion c A ∨ u ≤ min a.massCoverBase 1 := by
  let m:=a.shiftedNativeModel
  have hae : ∀ᵐ u ∂volume.restrict (Icc (0:ℝ) 1),∀i:BroadCapIndex c,
      m.R u∈Ioo (c i.val).left (c i.val).right →
        u ≤ min a.massCoverBase 1 ∨∃j,m.R u∈(actualBroadCapSampler c i).slice j:=
    ae_all_iff.mpr (fun i=>(actualBroadCapSampler c i).actual_conditional_cover_ae)
  filter_upwards [ae_restrict_mem measurableSet_Icc,hae] with u hu hcover hfull
  rcases hfull.2 with hcap|hcontact
  · obtain ⟨i,hi⟩:=mem_iUnion.mp hcap
    by_cases hb : 8*max (a.alpha.val.val (c i).left) a.massCoverBase<a.alpha.val.val (c i).right
    · rcases hcover ⟨i,hb⟩ hi with hl|⟨j,hj⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr hl)))
      · exact Or.inr (Or.inr (Or.inl ⟨⟨⟨⟨i,hb⟩,j⟩,⟨m.R u,hfull.1,hj⟩⟩,hj⟩))
    · by_cases hsmall:a.alpha.val.val (c i).right≤8*a.massCoverBase
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_iUnion.mpr
          ⟨⟨i,hsmall,⟨a.shiftedNativeModel.R u,hfull.1,hi⟩⟩,hi⟩))))
      · exact Or.inr (Or.inl (mem_iUnion.mpr
          ⟨⟨i,⟨hb,lt_of_not_ge hsmall⟩,⟨m.R u,hfull.1,hi⟩⟩,hi⟩))
  · exact Or.inl ⟨hfull.1,hcontact⟩

theorem local_finite_cap_conditional_error_cover {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval a P)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)).indicator
      (fun _=>1) (a.R u)*a.comparisonErrorDensity u) ≤
      (∫u in 0..1,(A∩P.contactSet).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u)+
      (∫u in 0..1,(relevantComparableCapUnion c A).indicator
        (fun _=>1) (a.R u)*a.comparisonErrorDensity u)+
      (∫u in 0..1,(conditionalSmallCapUnion c A).indicator
        (fun _=>1) (a.R u)*a.comparisonErrorDensity u)+
      (∑p : RelevantBroadSlice c A,
        ∫u in 0..1,(actualBroadSlice c p.val).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u)+
      (∫u in 0..min (a.massCoverBase) 1,a.comparisonErrorDensity u) := by
  let full := A ∩ ((⋃i,Ioo (c i).left (c i).right) ∪ P.contactSet)
  let contact := A ∩ P.contactSet
  let comp := relevantComparableCapUnion c A
  let small := conditionalSmallCapUnion c A
  let low : Set ℝ := {u |u ≤ min (a.massCoverBase) 1}
  let b := fun p : RelevantBroadSlice c A => fun u =>
    (actualBroadSlice c p.val).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u
  have hfull : MeasurableSet full := hA.inter
    ((MeasurableSet.iUnion (fun _=>measurableSet_Ioo)).union (P.contactSet_measurable))
  have hcontact : MeasurableSet contact := hA.inter (P.contactSet_measurable)
  have hcomp : MeasurableSet comp := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hsmall : MeasurableSet small := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hiSmall := a.error_mask_intervalIntegrable small hsmall
  have hiF := a.error_mask_intervalIntegrable full hfull
  have hiC := a.error_mask_intervalIntegrable contact hcontact
  have hiComp := a.error_mask_intervalIntegrable comp hcomp
  have hT : IntervalIntegrable a.comparisonErrorDensity volume 0 1:=by
    simpa only [indicator_univ,one_mul] using
      a.error_mask_intervalIntegrable univ MeasurableSet.univ
  have hiLow : IntervalIntegrable (fun u=>low.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u)
      volume 0 1:=intervalIntegrable_bounded_measurable_mul
        (measurable_const.indicator measurableSet_Iic) zero_le_one
        (fun u _=>by by_cases H:u∈low <;> simp [H]) hT
  have hiB p : IntervalIntegrable (b p) volume 0 1 :=
    a.error_mask_intervalIntegrable _ measurableSet_Ioo
  have hiSum : IntervalIntegrable (fun u=>∑p,b p u) volume 0 1 := by
    have heq : (fun u=>∑p,b p u)=∑p,b p := by funext u; simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun p _=>hiB p)
  have hpoint : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      full.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u ≤
        contact.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u+
        comp.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u+
        small.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u+(∑p,b p u)+low.indicator (fun _=>1) u*a.comparisonErrorDensity u := by
    have hc := local_finite_cap_conditional_cover_ae c A
    rw [←restrict_Ioc_eq_restrict_Icc] at hc
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hc] with u hu hc
    simp only [a.shiftedNativeModel_radius] at hc
    have hT := a.comparisonErrorDensity_nonneg (Ioc_subset_Icc_self hu)
    have hn (S : Set ℝ) : 0 ≤ S.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u :=
      mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) hT
    have hbn p : 0 ≤ b p u := hn _
    have hsum : 0 ≤ ∑p,b p u := Finset.sum_nonneg (fun p _=>hbn p)
    have hnLow : 0≤low.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u:=
      mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) hT
    by_cases hf : a.R u ∈ full
    · simp only [indicator_of_mem hf,one_mul]
      rcases hc hf with hcontact | hcomp | ⟨p,hp⟩ | hsmall | hlow
      · have hh : contact.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u=a.comparisonErrorDensity u := by
          rw [indicator_of_mem hcontact,one_mul]
        rw [hh]
        linarith [hn comp,hn small,hnLow]
      · have hh : comp.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u=a.comparisonErrorDensity u := by
          rw [indicator_of_mem hcomp,one_mul]
        rw [hh]
        linarith [hn contact,hn small,hnLow]
      · have hh : b p u=a.comparisonErrorDensity u := by dsimp [b]; simp only [indicator_of_mem hp,one_mul]
        have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun p=>b p u)
          (fun p _=>hbn p) (Finset.mem_univ p)
        rw [hh] at hs
        linarith [hn contact,hn comp,hn small,hnLow]
      · have hh : small.indicator (fun _=>(1:ℝ)) (a.R u)*a.comparisonErrorDensity u=a.comparisonErrorDensity u := by
          rw [indicator_of_mem hsmall,one_mul]
        rw [hh]
        linarith [hn contact,hn comp,hnLow]
      · have hh : low.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u=a.comparisonErrorDensity u := by
          rw [indicator_of_mem (show u∈low from hlow),one_mul]
        rw [hh]
        linarith [hn contact,hn comp,hn small]
    · simp only [indicator_of_notMem hf,zero_mul]
      linarith [hn contact,hn comp,hn small,hnLow]
  have hb : (∫u in 0..1,full.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u) ≤
      ∫u in 0..1,contact.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u+
        comp.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u+
        small.indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u+(∑p,b p u)+
        low.indicator (fun _=>1) u*a.comparisonErrorDensity u := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiF)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((((hiC.add hiComp).add hiSmall).add hiSum).add hiLow)) hpoint
  rw [intervalIntegral.integral_add (((hiC.add hiComp).add hiSmall).add hiSum) hiLow,
    intervalIntegral.integral_add ((hiC.add hiComp).add hiSmall) hiSum,
    intervalIntegral.integral_add (hiC.add hiComp) hiSmall,
    intervalIntegral.integral_add hiC hiComp,
    intervalIntegral.integral_finsetSum (fun p _=>hiB p),
    ] at hb
  have hv : min (a.massCoverBase) 1∈Icc (0:ℝ) 1:=
    ⟨(lt_min (massCoverBase_pos (a:=a)) zero_lt_one).le,min_le_right _ _⟩
  have heq : (fun u=>low.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u)=
      ({u |u ≤ min (a.massCoverBase) 1}).indicator a.comparisonErrorDensity:=by
    funext u
    change low.indicator (fun _=>(1:ℝ)) u*a.comparisonErrorDensity u=
      low.indicator a.comparisonErrorDensity u
    by_cases H:u∈low
    · rw [indicator_of_mem H,indicator_of_mem H,one_mul]
    · rw [indicator_of_notMem H,indicator_of_notMem H,zero_mul]
  rw [heq,intervalIntegral.integral_indicator hv] at hb
  exact hb

theorem conditional_comparable_cap_left_positive {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) (i : RelevantComparableCap c A) :
    0 < (c i.val).left := by
  by_contra hn
  have hl : (c i.val).left=0 := le_antisymm (le_of_not_gt hn) (c i.val).hleft
  have H := le_of_not_gt i.property.1.1
  have hbase : a.data.s ≤ a.massCoverBase := le_max_right _ _
  rw [hl,a.alpha.property.1,max_eq_right hbase] at H
  exact i.property.1.2.not_ge H

theorem conditional_small_cap_endpoint_le_U {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ)
    (hsU : a.data.s ≤ a.data.U) (i : ConditionalSmallCap c A) :
    a.alpha.val.val (c i.val).right ≤ 8*a.data.U := by
  simpa only [massCoverBase,max_eq_left hsU] using i.property.1

theorem conditional_small_cap_endpoint_le_wall {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ)
    (hUs : a.data.U ≤ a.data.s) (i : ConditionalSmallCap c A) :
    a.alpha.val.val (c i.val).right ≤ 16*a.data.s := by
  have H : a.alpha.val.val (c i.val).right ≤ 8*a.data.s := by
    simpa only [massCoverBase,max_eq_right hUs] using i.property.1
  exact H.trans (by nlinarith [a.data.hs.1])

theorem conditional_small_cap_union_mass_le_U {ι : Type*}
    (c : ι→ShiftedCapInterval a P) (A : Set ℝ) (hsU : a.data.s ≤ a.data.U)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (hsmall : a.R u∈conditionalSmallCapUnion c A) :
    u ≤ min (8*a.data.U) 1 := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hsmall
  let m:=a.shiftedNativeModel
  have huHigh : u∈Icc a.data.s 1 :=
    ⟨(m.R_high_mass ((c i.val).hleft.trans_lt hi.1)).le,hu.2⟩
  have hr:=m.R_bounds u
  have H := inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property
    hr ⟨(c i.val).hleft.trans (c i.val).hlt.le,(c i.val).hright⟩ hi.2
  rw [m.R_spec huHigh] at H
  exact le_min (H.le.trans (conditional_small_cap_endpoint_le_U c A hsU i)) hu.2

theorem conditional_initial_cap_card_le_one {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval a P)
    (hdisjoint : Pairwise fun i j=>Disjoint (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right)) :
    Fintype.card {i : ι // (c i).left=0} ≤ 1 := by
  have hsub : Subsingleton {i : ι // (c i).left=0} := by
    constructor
    intro i j
    apply Subtype.ext
    by_contra hne
    have hi : 0 < (c i.val).right := by simpa only [i.property] using (c i.val).hlt
    have hj : 0 < (c j.val).right := by simpa only [j.property] using (c j.val).hlt
    let r := min (c i.val).right (c j.val).right/2
    have hr : 0 < r := by dsimp only [r]; exact half_pos (lt_min hi hj)
    have hri : r∈Ioo (c i.val).left (c i.val).right := by
      rw [i.property]
      exact ⟨hr,by dsimp only [r]; linarith [min_le_left (c i.val).right (c j.val).right]⟩
    have hrj : r∈Ioo (c j.val).left (c j.val).right := by
      rw [j.property]
      exact ⟨hr,by dsimp only [r]; linarith [min_le_right (c i.val).right (c j.val).right]⟩
    exact Set.disjoint_left.mp (hdisjoint hne) hri hrj
  have H := Fintype.card_le_of_injective (fun _ : {i : ι // (c i).left=0} => ())
    (fun i j _=>hsub.elim i j)
  simpa only [Fintype.card_unit] using H

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
