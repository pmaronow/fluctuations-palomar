module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

theorem eq7_inner_base_le_prefix_end :
    Q.positiveOriginMassCoverBase ≤ Q.eq7InnerPrefixEnd := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  have hU0 : 0 < U := Q.data.hU
  have hU1 : U ≤ 1 := Q.data.hsmall.trans Q.data.hd1
  by_cases hsU : Q.data.s < U
  · have hbase : Q.positiveOriginMassCoverBase = U := by
      dsimp only [positiveOriginMassCoverBase,U]
      exact max_eq_left hsU.le
    rw [hbase]
    dsimp only [eq7InnerPrefixEnd]
    rw [ite_eq_left (show Q.data.s < comparisonSmallMass Q.data.N Q.data.E from hsU)]
    exact le_min (by linarith only [hU0]) hU1
  · have hUs : U ≤ Q.data.s := le_of_not_gt hsU
    have hbase : Q.positiveOriginMassCoverBase = Q.data.s := by
      dsimp only [positiveOriginMassCoverBase,U]
      exact max_eq_right hUs
    rw [hbase]
    dsimp only [eq7InnerPrefixEnd]
    rw [ite_eq_right (show ¬Q.data.s < comparisonSmallMass Q.data.N Q.data.E from hsU)]
    exact le_min (by linarith only [hU0]) Q.data.hs1

theorem eq7_inner_s_le_prefix_end :
    Q.data.s ≤ Q.eq7InnerPrefixEnd :=
  (le_max_right _ _).trans Q.eq7_inner_base_le_prefix_end

theorem eq7_inner_prefix_end_le_one : Q.eq7InnerPrefixEnd ≤ 1 := by
  dsimp only [eq7InnerPrefixEnd]
  split_ifs <;> exact min_le_right _ _

theorem eq7_inner_wall_start_lt_of_above_prefix
    {u : ℝ} (hu1 : u ≤ 1)
    (hprefix : Q.eq7InnerPrefixEnd < u) :
    Q.data.s+comparisonSmallMass Q.data.N Q.data.E < u := by
  let U := comparisonSmallMass Q.data.N Q.data.E
  have hU : 0 < U := Q.data.hU
  by_cases hsU : Q.data.s < U
  · have h24 : 24*U < u := by
      by_contra hh
      have hu24 : u ≤ 24*U := le_of_not_gt hh
      have hmin : u ≤ min (24*U) 1 := le_min hu24 hu1
      have hp : Q.eq7InnerPrefixEnd = min (24*U) 1 := by
        dsimp only [eq7InnerPrefixEnd]
        exact ite_eq_left hsU
      exact (not_le_of_gt hprefix) (hp.symm ▸ hmin)
    linarith only [h24,hsU,hU]
  · have h2 : Q.data.s+2*U < u := by
      by_contra hh
      have hu2 : u ≤ Q.data.s+2*U := le_of_not_gt hh
      have hmin : u ≤ min (Q.data.s+2*U) 1 := le_min hu2 hu1
      have hp : Q.eq7InnerPrefixEnd = min (Q.data.s+2*U) 1 := by
        dsimp only [eq7InnerPrefixEnd]
        exact ite_eq_right hsU
      exact (not_le_of_gt hprefix) (hp.symm ▸ hmin)
    linarith only [h2,hU]

theorem eq7_inner_cap_mass_between
    (cap : ShiftedCapInterval Q P) {u : ℝ}
    (hu : u ∈ Icc Q.data.s 1)
    (hr : Q.shiftedNativeModel.R u ∈ Ioo cap.left cap.right) :
    Q.alpha.val.val cap.left < u ∧
      u < Q.alpha.val.val cap.right := by
  have hR := Q.shiftedNativeModel.R_bounds u
  have hleft : cap.left ∈ Icc Q.data.rmin 1 :=
    ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩
  have hright : cap.right ∈ Icc Q.data.rmin 1 :=
    ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩
  have hmono := inverseConstraint_strictMonoOn Q.data.hc Q.data.hk
    Q.data.hkc Q.alpha.property
  have hl := hmono hleft hR hr.1
  have hz := hmono hR hright hr.2
  rw [Q.shiftedNativeModel.R_spec hu] at hl hz
  exact ⟨hl,hz⟩

theorem eq7_inner_mass_between_radii
    {a u z : ℝ} (ha : a ∈ Icc Q.data.s 1)
    (hu : u ∈ Icc Q.data.s 1) (hz : z ∈ Icc Q.data.s 1)
    (hau : a < u) (huz : u < z) :
    Q.shiftedNativeModel.R u ∈
      Ioo (Q.shiftedNativeModel.R a) (Q.shiftedNativeModel.R z) :=
  ⟨Q.shiftedNativeModel.R_strictMonoOn ha hu hau,
    Q.shiftedNativeModel.R_strictMonoOn hu hz huz⟩

theorem Potential.eq7_mem_retainedSupport_of_cap
    (P : Q.Potential) {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    {ag zg r : ℝ} (i : ι) (hlo : ag ≤ (c i).left)
    (hhi : (c i).right ≤ zg)
    (hr : r ∈ Ioo (c i).left (c i).right) :
    r ∈ P.retainedSupport c ag zg := by
  change r ∈ Ioo ag zg ∧
    ((∃t : ι, r ∈ Ioo (c t).left (c t).right) ∨ P.H r=0)
  exact ⟨⟨hlo.trans_lt hr.1,hr.2.trans_le hhi⟩,Or.inl ⟨i,hr⟩⟩

theorem Potential.eq7_mem_retainedSupport_of_contact
    (P : Q.Potential) {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    {ag zg r : ℝ} (hr : r ∈ P.contactSet)
    (hband : r ∈ Ioo ag zg) :
    r ∈ P.retainedSupport c ag zg := by
  change r ∈ Ioo ag zg ∧
    ((∃t : ι, r ∈ Ioo (c t).left (c t).right) ∨ P.H r=0)
  exact ⟨hband,Or.inr hr.2⟩

theorem eq7_inner_low_cap_mem
    {ι : Type*} (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerLowDyad Q h) (i : Eq7InnerLowCapIndex c j)
    {u : ℝ} (hu : u ∈ Icc Q.data.s 1)
    (hr : Q.shiftedNativeModel.R u ∈ Ioo (c i.val).left (c i.val).right) :
    Q.shiftedNativeModel.R u ∈ eq7InnerLowSupport c j := by
  let z := Q.eq7InnerDyadRight j.val.val
  have hcap := Q.eq7_inner_cap_mass_between (c i.val) hu hr
  have hls : Q.data.s ≤ Q.alpha.val.val (c i.val).left := by
    have H := Q.alpha.val.property.2 (c i.val).hleft
    simpa only [Q.alpha.property.1] using H
  have hz : z ∈ Icc Q.data.s 1 :=
    ⟨j.property.2.2,min_le_right _ _⟩
  have hs : Q.data.s ∈ Icc Q.data.s 1 := ⟨le_rfl,Q.data.hs1⟩
  have hrad := Q.eq7_inner_mass_between_radii hs hu hz
    (hls.trans_lt hcap.1) (hcap.2.trans_le i.property.2.2.1)
  rw [Q.shiftedNativeModel.R_left] at hrad
  change Q.shiftedNativeModel.R u ∈ Ioo Q.data.rmin
      (Q.shiftedNativeModel.R z) ∧
    ((∃t : Eq7InnerLowCapIndex c j,
      Q.shiftedNativeModel.R u ∈ Ioo (c t.val).left (c t.val).right) ∨
      P.H (Q.shiftedNativeModel.R u)=0)
  exact ⟨hrad,Or.inl ⟨i,hr⟩⟩

theorem eq7_inner_post_cap_mem
    {ι : Type*} (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerPostDyad Q h) (i : Eq7InnerPostCapIndex c j)
    {u : ℝ} (hu : u ∈ Icc Q.data.s 1)
    (hr : Q.shiftedNativeModel.R u ∈ Ioo (c i.val).left (c i.val).right) :
    Q.shiftedNativeModel.R u ∈ eq7InnerPostSupport c j := by
  let q := Q.eq7InnerWallStart j.val.val
  let z := Q.eq7InnerDyadRight j.val.val
  have hcap := Q.eq7_inner_cap_mass_between (c i.val) hu hr
  have hqS : Q.data.s < q := by
    dsimp only [q,eq7InnerWallStart]
    have hU := Q.data.hU
    exact (by linarith : Q.data.s < Q.data.s+
      comparisonSmallMass Q.data.N Q.data.E).trans_le (le_max_left _ _)
  have hq : q ∈ Icc Q.data.s 1 :=
    ⟨hqS.le,(j.property.2).le.trans (min_le_right _ _)⟩
  have hz : z ∈ Icc Q.data.s 1 :=
    ⟨hqS.le.trans (j.property.2).le,min_le_right _ _⟩
  have hrad := Q.eq7_inner_mass_between_radii hq hu hz
    ((i.property.2.1).trans_lt hcap.1)
    (hcap.2.trans_le i.property.2.2)
  change Q.shiftedNativeModel.R u ∈ Ioo (Q.shiftedNativeModel.R q)
      (Q.shiftedNativeModel.R z) ∧
    ((∃t : Eq7InnerPostCapIndex c j,
      Q.shiftedNativeModel.R u ∈ Ioo (c t.val).left (c t.val).right) ∨
      P.H (Q.shiftedNativeModel.R u)=0)
  exact ⟨hrad,Or.inl ⟨i,hr⟩⟩

theorem eq7_inner_low_contact_mem
    {ι : Type*} (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerLowDyad Q h) {u : ℝ}
    (hu : u ∈ Icc Q.data.s 1) (hsu : Q.data.s < u)
    (huz : u < Q.eq7InnerDyadRight j.val.val)
    (hcontact : Q.shiftedNativeModel.R u ∈ P.contactSet) :
    Q.shiftedNativeModel.R u ∈ eq7InnerLowSupport c j := by
  have hs : Q.data.s ∈ Icc Q.data.s 1 := ⟨le_rfl,Q.data.hs1⟩
  have hz : Q.eq7InnerDyadRight j.val.val ∈ Icc Q.data.s 1 :=
    ⟨j.property.2.2,min_le_right _ _⟩
  have hrad := Q.eq7_inner_mass_between_radii hs hu hz hsu huz
  rw [Q.shiftedNativeModel.R_left] at hrad
  exact P.eq7_mem_retainedSupport_of_contact
    (fun i : Eq7InnerLowCapIndex c j => c i.val) hcontact hrad

theorem eq7_inner_post_contact_mem
    {ι : Type*} (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (j : Eq7InnerPostDyad Q h) {u : ℝ}
    (hu : u ∈ Icc Q.data.s 1)
    (hqu : Q.eq7InnerWallStart j.val.val < u)
    (huz : u < Q.eq7InnerDyadRight j.val.val)
    (hcontact : Q.shiftedNativeModel.R u ∈ P.contactSet) :
    Q.shiftedNativeModel.R u ∈ eq7InnerPostSupport c j := by
  let q := Q.eq7InnerWallStart j.val.val
  let z := Q.eq7InnerDyadRight j.val.val
  have hqS : Q.data.s < q := by
    dsimp only [q,eq7InnerWallStart]
    have hU := Q.data.hU
    exact (by linarith : Q.data.s < Q.data.s+
      comparisonSmallMass Q.data.N Q.data.E).trans_le (le_max_left _ _)
  have hq : q ∈ Icc Q.data.s 1 :=
    ⟨hqS.le,hqu.le.trans hu.2⟩
  have hz : z ∈ Icc Q.data.s 1 :=
    ⟨hu.1.trans huz.le,min_le_right _ _⟩
  have hrad := Q.eq7_inner_mass_between_radii hq hu hz hqu huz
  exact P.eq7_mem_retainedSupport_of_contact
    (fun i : Eq7InnerPostCapIndex c j => c i.val) hcontact hrad

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
