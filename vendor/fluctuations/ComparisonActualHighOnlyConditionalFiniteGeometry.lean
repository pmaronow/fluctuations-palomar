module

public import ComparisonActualHighOnlyConditionalFiniteCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.conditional_contact_high_ordinary {ι : Type*}
    (P : a.Potential) (c : ι→ShiftedCapInterval a P) (A : Set ℝ)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hcontact : r∈P.contactSet)
    (hU : a.data.U ≤ a.alpha.val.val r) (hhigh : 4*a.data.s < a.alpha.val.val r) :
    ∃j : comparisonMassDyadicIndices a.data.U,
      2*a.data.s < a.data.U*(2:ℝ)^(j:ℕ) ∧ r∈P.ordinaryGroup c A 16 j := by
  let m:=a.shiftedNativeModel
  have hmI : a.alpha.val.val r∈Icc a.data.s 1 :=
    (inverseConstraintMap a.alpha (⟨r,Ioo_subset_Icc_self hr⟩)).property
  have hm1 : a.alpha.val.val r<1 := by
    have H:=inverseConstraint_strictMonoOn m.hc m.hk m.hkc a.alpha.property
      (Ioo_subset_Icc_self hr) ⟨zero_le_one,le_rfl⟩ hr.2
    simpa only [a.alpha.property.2.1] using H
  obtain ⟨j,hj,hjNext⟩ := comparison_mass_dyadic_cover a.data.hU hU
    (a.alpha.val.property.1 r).2
  let v:=a.data.U*(2:ℝ)^(j:ℕ)
  have hv := comparison_mass_dyadic_scale a.data.hU j
  have hvHigh : a.data.s < v/2 := by dsimp only [v]; linarith
  have hmin : a.alpha.val.val r < min (16*v) 1 :=
    lt_min (by dsimp only [v]; linarith [hjNext]) hm1
  have hlo : v/2∈Icc a.data.s 1 := ⟨hvHigh.le,by dsimp only [v]; linarith [hv.2.2]⟩
  have hhi : min (16*v) 1∈Icc a.data.s 1 := ⟨hmI.1.trans hmin.le,min_le_right _ _⟩
  have Hlow := m.R_strictMonoOn hlo hmI (by dsimp only [v]; linarith [hj])
  have Hhigh := m.R_strictMonoOn hmI hhi hmin
  rw [m.R_inverse (Ioo_subset_Icc_self hr)] at Hlow Hhigh
  exact ⟨j,by dsimp only [v] at hvHigh; linarith,Or.inl ⟨hcontact,Hlow,Hhigh⟩⟩

theorem Potential.conditional_contact_region_dichotomy {ι : Type*}
    (P : a.Potential) (c : ι→ShiftedCapInterval a P) (A : Set ℝ)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hcontact : r∈P.contactSet) :
    (a.data.s < a.data.U ∧ a.alpha.val.val r ≤ min (16*a.data.U) 1) ∨
      (a.data.U ≤ a.data.s ∧ a.alpha.val.val r ≤ min (32*a.data.s) 1) ∨
      ∃j : comparisonMassDyadicIndices a.data.U,
        2*a.data.s < a.data.U*(2:ℝ)^(j:ℕ) ∧ r∈P.ordinaryGroup c A 16 j := by
  have hm1 := (a.alpha.val.property.1 r).2
  by_cases hsU : a.data.s < a.data.U
  · by_cases hlow : a.alpha.val.val r ≤ 16*a.data.U
    · exact Or.inl ⟨hsU,le_min hlow hm1⟩
    · exact Or.inr (Or.inr (P.conditional_contact_high_ordinary c A hr hcontact
        (by linarith [a.data.hU]) (by linarith [a.data.hs.1])))
  · have hUs : a.data.U ≤ a.data.s := le_of_not_gt hsU
    by_cases hlow : a.alpha.val.val r ≤ 32*a.data.s
    · exact Or.inr (Or.inl ⟨hUs,le_min hlow hm1⟩)
    · exact Or.inr (Or.inr (P.conditional_contact_high_ordinary c A hr hcontact
        (by linarith [a.data.hs.1]) (by linarith [a.data.hs.1])))

theorem conditional_low_dyad_eq_U (hsU : a.data.s < a.data.U)
    (j : comparisonMassDyadicIndices a.data.U)
    (hlow : a.data.U*(2:ℝ)^(j:ℕ) ≤ 2*a.data.s) :
    a.data.U*(2:ℝ)^(j:ℕ)=a.data.U := by
  have hj0 : (j:ℕ)=0 := by
    by_contra hn
    have hpos : 1 ≤ (j:ℕ) := Nat.one_le_iff_ne_zero.mpr hn
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hpos
    have H := mul_le_mul_of_nonneg_left hp a.data.hU.le
    norm_num only [pow_one] at H
    linarith
  rw [hj0,pow_zero,mul_one]

theorem Potential.conditional_comparable_region_dichotomy {ι : Type*} [Fintype ι]
    (P : a.Potential) (c : ι→ShiftedCapInterval a P) (A : Set ℝ)
    (i : RelevantComparableCap c A) :
    (a.data.s < a.data.U ∧ a.alpha.val.val (c i.val).right ≤ min (16*a.data.U) 1) ∨
      (a.data.U ≤ a.data.s ∧ 0<(c i.val).left ∧
        a.alpha.val.val (c i.val).right ≤ min (32*a.data.s) 1) ∨
      ∃j : comparisonMassDyadicIndices a.data.U,
        2*a.data.s < a.data.U*(2:ℝ)^(j:ℕ) ∧
        Ioo (c i.val).left (c i.val).right ⊆ P.ordinaryGroup c A 16 j := by
  have HA r (_hr : r∈A) : (0:ℝ) ≤ a.alpha.val.val r ∧ a.alpha.val.val r ≤ 1 :=
    a.alpha.val.property.1 r
  obtain ⟨j,hjl,hjr⟩ := relevant_comparable_cap_dyadic_scale c A HA i
  let v:=a.data.U*(2:ℝ)^(j.val:ℕ)
  by_cases hhigh : 2*a.data.s < v
  · exact Or.inr (Or.inr ⟨j.val,hhigh,fun r hr=>Or.inr (mem_iUnion.mpr
      ⟨⟨i.val,i.property.2,hjl,hjr⟩,hr⟩)⟩)
  · have hlow : v ≤ 2*a.data.s := le_of_not_gt hhigh
    by_cases hsU : a.data.s < a.data.U
    · have HV := conditional_low_dyad_eq_U hsU j.val hlow
      exact Or.inl ⟨hsU,by simpa only [HV] using hjr⟩
    · exact Or.inr (Or.inl ⟨le_of_not_gt hsU,conditional_comparable_cap_left_positive c A i,
        hjr.trans (min_le_min (by dsimp only [v] at hlow; linarith) le_rfl)⟩)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
