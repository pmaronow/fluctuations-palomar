module

public import ComparisonNativeDyadicContactCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set
open scoped Topology
set_option autoImplicit false

theorem eq7_early_comparable_right_le_24U
    {s U l r : ℝ} (hU : 0 < U) (hsU : s < U)
    (hl : l < s+2*U) (hcomp : r ≤ 8*max l (max U s)) :
    r < 24*U := by
  have hbase : max U s = U := max_eq_left hsU.le
  rw [hbase] at hcomp
  have hl3 : l < 3*U := by linarith only [hl,hsU]
  have hU3 : U < 3*U := by linarith only [hU]
  have hmax : max l U < 3*U := max_lt hl3 hU3
  linarith only [hcomp,hmax]

theorem eq7_post_wall_comparable_cap_dyad_scalar
    {U s l r : ℝ} (hU : 0 < U) (hUl : U ≤ l)
    (hl1 : l ≤ 1) (hwall : s+U ≤ l)
    (hlr : l < r) (hr1 : r ≤ 1) (hcomp : r ≤ 8*l) :
    ∃ j : comparisonMassDyadicIndices U,
      let v := U*(2:ℝ)^(j.val:ℕ)
      v ≤ l ∧ l < 2*v ∧
      r ≤ min (16*v) 1 ∧
      max (s+U) v ≤ l ∧
      max (s+U) v < min (16*v) 1 := by
  obtain ⟨j,hj,hjNext⟩ := comparison_mass_dyadic_cover hU hUl hl1
  refine ⟨j,hj,hjNext,?_ ,?_ ,?_⟩
  · exact le_min (by linarith only [hcomp,hjNext]) hr1
  · exact max_le hwall hj
  · have hq : max (s+U) (U*(2:ℝ)^(j.val:ℕ)) ≤ l := max_le hwall hj
    have hr : r ≤ min (16*(U*(2:ℝ)^(j.val:ℕ))) 1 :=
      le_min (by linarith only [hcomp,hjNext]) hr1
    exact hq.trans_lt (hlr.trans_le hr)

theorem eq7_post_wall_contact_dyad_scalar
    {U s u : ℝ} (hU : 0 < U) (hUu : U ≤ u)
    (hwall : s+U ≤ u) (hu1 : u < 1) :
    ∃ j : comparisonMassDyadicIndices U,
      let v := U*(2:ℝ)^(j.val:ℕ)
      v ≤ u ∧ u < 2*v ∧
      max (s+U) v ≤ u ∧
      u < min (16*v) 1 := by
  obtain ⟨j,hj,hjNext⟩ := comparison_mass_dyadic_cover hU hUu hu1.le
  refine ⟨j,hj,hjNext,max_le hwall hj,?_⟩
  exact lt_min (by linarith only [hjNext,hUu,hU]) hu1

theorem eq7_moderate_initial_cap_wall_dyad_scalar
    {U s r : ℝ} (hU : 0 < U) (hUs : U ≤ s)
    (hs1 : s ≤ 1) (hr1 : r ≤ 1) (hmoderate : r ≤ 8*s) :
    ∃ j : comparisonMassDyadicIndices U,
      let v := U*(2:ℝ)^(j.val:ℕ)
      v ≤ s ∧ s < 2*v ∧ r ≤ min (16*v) 1 := by
  obtain ⟨j,hj,hjNext⟩ := comparison_mass_dyadic_cover hU hUs hs1
  refine ⟨j,hj,hjNext,?_⟩
  exact le_min (by linarith only [hmoderate,hjNext]) hr1

end OAI.SKFluctuations.LaplaceWindowFormalization
