module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskGeometry
public import ComparisonActualHighWallThetaZeroEq7InnerScalarCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

theorem eq7_inner_finite_mask_cover_at_mass
    {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    {h u : ℝ} (hu : u ∈ Icc Q.data.s h) (hu1 : u < 1)
    (hnode : ∀ j : comparisonMassDyadicIndices
      (comparisonSmallMass Q.data.N Q.data.E),
      u ≠ Q.eq7InnerDyadMass j)
    (hbroad : ∀ i : Eq7InnerBroadCapIndex c,
      Q.shiftedNativeModel.R u ∈ Ioo (c i.val).left (c i.val).right →
      u ≤ Q.positiveOriginMassCoverBase ∨
        ∃ k : Fin (eq7InnerBroadSampler c i).count,
          Q.shiftedNativeModel.R u ∈ (eq7InnerBroadSampler c i).slice k)
    (hcapcontact : Q.shiftedNativeModel.R u ∈
      (⋃i, Ioo (c i).left (c i).right) ∪ P.contactSet) :
    u ≤ Q.eq7InnerPrefixEnd ∨
      (∃ p : Eq7InnerRelevantBroadSlice c h,
        Q.shiftedNativeModel.R u ∈ eq7InnerBroadSlice c p.val) ∨
      (∃ j : Eq7InnerLowDyad Q h,
        Q.shiftedNativeModel.R u ∈ eq7InnerLowSupport c j) ∨
      (∃ j : Eq7InnerPostDyad Q h,
        Q.shiftedNativeModel.R u ∈ eq7InnerPostSupport c j) := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  have hU : 0 < U := Q.data.hU
  have hMass : u ∈ Icc Q.data.s 1 := ⟨hu.1,hu1.le⟩
  by_cases hpre : u ≤ Q.eq7InnerPrefixEnd
  · exact Or.inl hpre
  have habove : Q.eq7InnerPrefixEnd < u := lt_of_not_ge hpre
  have hsu : Q.data.s < u := Q.eq7_inner_s_le_prefix_end.trans_lt habove
  have hbu : Q.data.s+U < u := Q.eq7_inner_wall_start_lt_of_above_prefix
    hu1.le habove
  have hUu : U ≤ u :=
    ((le_max_left U Q.data.s).trans Q.eq7_inner_base_le_prefix_end).trans habove.le
  rcases hcapcontact with hcaps | hcontact
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hcaps
    by_cases hBroad : eq7InnerCapBroad c i
    · let bi : Eq7InnerBroadCapIndex c := ⟨i,hBroad⟩
      rcases hbroad bi hi with hbase | ⟨k,hk⟩
      · exact False.elim ((not_le_of_gt habove)
          (hbase.trans Q.eq7_inner_base_le_prefix_end))
      · let p : Eq7InnerBroadSliceIndex c := ⟨bi,k⟩
        let pr : Eq7InnerRelevantBroadSlice c h :=
          ⟨p,⟨u,hu,hk⟩⟩
        exact Or.inr (Or.inl ⟨pr,hk⟩)
    · let l := Q.alpha.val.val (c i).left
      let r := Q.alpha.val.val (c i).right
      have hcap := Q.eq7_inner_cap_mass_between (c i) hMass hi
      have hls : Q.data.s ≤ l := by
        have H := Q.alpha.val.property.2 (c i).hleft
        simpa only [l,Q.alpha.property.1] using H
      have hl1 : l ≤ 1 := (Q.alpha.val.property.1 (c i).left).2
      have hr1 : r ≤ 1 := (Q.alpha.val.property.1 (c i).right).2
      have hcomp : r ≤ 8*max l Q.positiveOriginMassCoverBase :=
        le_of_not_gt hBroad
      by_cases hsU : Q.data.s < U
      · have hbase : Q.positiveOriginMassCoverBase = U := by
          dsimp only [positiveOriginMassCoverBase,U]
          exact max_eq_left hsU.le
        by_cases hearly : l < Q.data.s+2*U
        · have hr24 : r < 24*U :=
            eq7_early_comparable_right_le_24U hU hsU hearly hcomp
          have hp : u ≤ Q.eq7InnerPrefixEnd := by
            have H : u ≤ min (24*U) 1 :=
              le_min (hcap.2.trans hr24).le hu1.le
            change u ≤ if Q.data.s < U then min (24*U) 1 else min (Q.data.s+2*U) 1
            rw [ite_eq_left hsU]
            exact H
          exact False.elim ((not_le_of_gt habove) hp)
        · have hwall : Q.data.s+U ≤ l := by
            have H := le_of_not_gt hearly
            linarith only [H,hU]
          have hUl : U ≤ l := by linarith only [hwall,Q.data.hs.1]
          have hcomp' : r ≤ 8*l := by
            simpa only [hbase,max_eq_left hUl] using hcomp
          obtain ⟨j,hj,hjNext,hrz,hql,hqz⟩ :=
            eq7_post_wall_comparable_cap_dyad_scalar hU hUl hl1 hwall
              (hcap.1.trans hcap.2) hr1 hcomp'
          let jh : Eq7InnerDyad Q h :=
            ⟨j,hj.trans (hcap.1.le.trans hu.2)⟩
          let jp : Eq7InnerPostDyad Q h :=
            ⟨jh,Or.inl hsU,hqz⟩
          let ip : Eq7InnerPostCapIndex c jp := ⟨i,hBroad,hql,hrz⟩
          exact Or.inr (Or.inr (Or.inr
            ⟨jp,Q.eq7_inner_post_cap_mem c jp ip hMass hi⟩))
      · have hUs : U ≤ Q.data.s := le_of_not_gt hsU
        have hbase : Q.positiveOriginMassCoverBase = Q.data.s := by
          dsimp only [positiveOriginMassCoverBase,U]
          exact max_eq_right hUs
        have hcomp' : r ≤ 8*l := by
          simpa only [hbase,max_eq_left hls] using hcomp
        by_cases hshort : (c i).left = Q.data.rmin ∧ r-l ≤ U
        · have hwallMass : l=Q.data.s := by
            dsimp only [l]
            rw [hshort.1]
            exact Q.alpha.property.1
          have hp : u ≤ Q.eq7InnerPrefixEnd := by
            have huBound : u ≤ Q.data.s+2*U := by
              linarith only [hcap.2,hshort.2,hwallMass,hU]
            have H : u ≤ min (Q.data.s+2*U) 1 := le_min huBound hu1.le
            change u ≤ if Q.data.s < U then min (24*U) 1 else min (Q.data.s+2*U) 1
            rw [ite_eq_right hsU]
            exact H
          exact False.elim ((not_le_of_gt habove) hp)
        have hwidth : (c i).left ≠ Q.data.rmin ∨ U ≤ r-l := by
          by_cases hinitial : (c i).left = Q.data.rmin
          · right
            have H : ¬r-l ≤ U := fun hw => hshort ⟨hinitial,hw⟩
            exact (lt_of_not_ge H).le
          · exact Or.inl hinitial
        have hUl : U ≤ l := hUs.trans hls
        obtain ⟨j,hj,hjNext⟩ := comparison_mass_dyadic_cover hU hUl hl1
        have hrz : r ≤ min (16*(U*(2:ℝ)^(j.val:ℕ))) 1 :=
          le_min (by linarith only [hcomp',hjNext]) hr1
        let jh : Eq7InnerDyad Q h :=
          ⟨j,hj.trans (hcap.1.le.trans hu.2)⟩
        by_cases hvlow : Q.eq7InnerDyadMass j ≤ 2*Q.data.s
        · have hsz : Q.data.s ≤ Q.eq7InnerDyadRight j := by
            dsimp only [eq7InnerDyadRight,eq7InnerDyadMass]
            exact hls.trans (hcap.1.le.trans (hcap.2.le.trans hrz))
          let jl : Eq7InnerLowDyad Q h := ⟨jh,hUs,hvlow,hsz⟩
          let il : Eq7InnerLowCapIndex c jl :=
            ⟨i,hBroad,hj,hrz,hwidth⟩
          exact Or.inr (Or.inr (Or.inl
            ⟨jl,Q.eq7_inner_low_cap_mem c jl il hMass hi⟩))
        · have hvhigh : 2*Q.data.s < Q.eq7InnerDyadMass j :=
            lt_of_not_ge hvlow
          have hwall : Q.data.s+U ≤ l := by
            have hb : Q.data.s+U ≤ 2*Q.data.s := by linarith only [hUs]
            exact hb.trans (hvhigh.le.trans hj)
          have hql : Q.eq7InnerWallStart j ≤ l := by
            dsimp only [eq7InnerWallStart]
            exact max_le hwall hj
          have hqz : Q.eq7InnerWallStart j < Q.eq7InnerDyadRight j := by
            dsimp only [eq7InnerWallStart,eq7InnerDyadRight,eq7InnerDyadMass]
            exact hql.trans_lt (hcap.1.trans (hcap.2.trans_le hrz))
          let jp : Eq7InnerPostDyad Q h :=
            ⟨jh,Or.inr hvhigh,hqz⟩
          let ip : Eq7InnerPostCapIndex c jp := ⟨i,hBroad,hql,hrz⟩
          exact Or.inr (Or.inr (Or.inr
            ⟨jp,Q.eq7_inner_post_cap_mem c jp ip hMass hi⟩))
  · obtain ⟨j,hj,hjNext⟩ := comparison_mass_dyadic_cover hU hUu hu1.le
    have hvu : Q.eq7InnerDyadMass j < u := by
      have H : U*(2:ℝ)^(j.val:ℕ) < u :=
        lt_of_le_of_ne hj (Ne.symm (hnode j))
      exact H
    have huz : u < Q.eq7InnerDyadRight j := by
      dsimp only [eq7InnerDyadRight,eq7InnerDyadMass]
      exact lt_min (by linarith only [hjNext,hUu,hU]) hu1
    let jh : Eq7InnerDyad Q h := ⟨j,hj.trans hu.2⟩
    by_cases hsU : Q.data.s < U
    · have hq : Q.eq7InnerWallStart j < u := by
        dsimp only [eq7InnerWallStart]
        exact max_lt hbu hvu
      have hqz : Q.eq7InnerWallStart j < Q.eq7InnerDyadRight j :=
        hq.trans huz
      let jp : Eq7InnerPostDyad Q h := ⟨jh,Or.inl hsU,hqz⟩
      exact Or.inr (Or.inr (Or.inr
        ⟨jp,Q.eq7_inner_post_contact_mem c jp hMass hq huz hcontact⟩))
    · have hUs : U ≤ Q.data.s := le_of_not_gt hsU
      by_cases hvlow : Q.eq7InnerDyadMass j ≤ 2*Q.data.s
      · have hsz : Q.data.s ≤ Q.eq7InnerDyadRight j := hsu.le.trans huz.le
        let jl : Eq7InnerLowDyad Q h := ⟨jh,hUs,hvlow,hsz⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨jl,Q.eq7_inner_low_contact_mem c jl hMass hsu huz hcontact⟩))
      · have hvhigh : 2*Q.data.s < Q.eq7InnerDyadMass j :=
          lt_of_not_ge hvlow
        have hq : Q.eq7InnerWallStart j < u := by
          dsimp only [eq7InnerWallStart]
          have hb : Q.data.s+U ≤ 2*Q.data.s := by linarith only [hUs]
          exact max_lt (hb.trans_lt hvhigh |>.trans hvu) hvu
        have hqz : Q.eq7InnerWallStart j < Q.eq7InnerDyadRight j :=
          hq.trans huz
        let jp : Eq7InnerPostDyad Q h := ⟨jh,Or.inr hvhigh,hqz⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨jp,Q.eq7_inner_post_contact_mem c jp hMass hq huz hcontact⟩))

theorem eq7_inner_finite_mask_cover_ae
    {ι : Type*} [Fintype ι] (c : ι → ShiftedCapInterval Q P)
    (h : ℝ) :
    ∀ᵐu ∂volume.restrict (Icc (0:ℝ) 1),
      u ∈ Icc Q.data.s h →
      Q.shiftedNativeModel.R u ∈
        (⋃i, Ioo (c i).left (c i).right) ∪ P.contactSet →
      u ≤ Q.eq7InnerPrefixEnd ∨
        (∃p : Eq7InnerRelevantBroadSlice c h,
          Q.shiftedNativeModel.R u ∈ eq7InnerBroadSlice c p.val) ∨
        (∃j : Eq7InnerLowDyad Q h,
          Q.shiftedNativeModel.R u ∈ eq7InnerLowSupport c j) ∨
        (∃j : Eq7InnerPostDyad Q h,
          Q.shiftedNativeModel.R u ∈ eq7InnerPostSupport c j) := by
  have hsamplers : ∀ᵐu ∂volume.restrict (Icc (0:ℝ) 1),
      ∀i : Eq7InnerBroadCapIndex c,
        Q.shiftedNativeModel.R u ∈ Ioo (c i.val).left (c i.val).right →
        u ≤ Q.positiveOriginMassCoverBase ∨
          ∃k : Fin (eq7InnerBroadSampler c i).count,
            Q.shiftedNativeModel.R u ∈ (eq7InnerBroadSampler c i).slice k :=
    ae_all_iff.mpr (fun i => by
      filter_upwards [(eq7InnerBroadSampler c i).actual_cover_ae] with u hu
      intro hc
      rcases hu hc with hlow | hslice
      · exact Or.inl (hlow.trans (min_le_left _ _))
      · exact Or.inr hslice)
  have hnodeAll : ∀ᵐu : ℝ,
      ∀j : comparisonMassDyadicIndices
        (comparisonSmallMass Q.data.N Q.data.E),
        u ≠ Q.eq7InnerDyadMass j :=
    ae_all_iff.mpr (fun j => volume.ae_ne (Q.eq7InnerDyadMass j))
  filter_upwards [hsamplers,ae_restrict_of_ae hnodeAll,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ)),
    ae_restrict_mem measurableSet_Icc] with u hsamp hnode hu1 hu0
  intro hregion hcapcontact
  have huOne : u < 1 := lt_of_le_of_ne hu0.2 hu1
  exact eq7_inner_finite_mask_cover_at_mass c hregion huOne hnode
    hsamp hcapcontact

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
