module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set
attribute [local instance] Classical.propDecidable

def capEndHeight (U : Set ℝ) (S : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r∈U then sSup (S '' ordConnectedComponent U r) else S r

theorem capEndHeight_bounds {U : Set ℝ} {S : ℝ → ℝ} {a b Y : ℝ}
    (hU : U⊆Icc a b) (hS : ∀r∈Icc a b,S r≤Y) {r : ℝ} (hr : r∈Icc a b) :
    S r ≤ capEndHeight U S r ∧ capEndHeight U S r ≤ Y := by
  by_cases hrU:r∈U
  · have hne : (S '' ordConnectedComponent U r).Nonempty :=
      (nonempty_ordConnectedComponent.mpr hrU).image S
    have hb : BddAbove (S '' ordConnectedComponent U r) :=
      ⟨Y,by rintro _ ⟨t,ht,rfl⟩; exact hS t (hU (ordConnectedComponent_subset ht))⟩
    simp only [capEndHeight,if_pos hrU]
    refine ⟨le_csSup hb ⟨r,self_mem_ordConnectedComponent.mpr hrU,rfl⟩,?_⟩
    apply csSup_le hne
    rintro _ ⟨t,ht,rfl⟩
    exact hS t (hU (ordConnectedComponent_subset ht))
  · simp only [capEndHeight,if_neg hrU]
    exact ⟨le_rfl,hS r hr⟩

theorem capEndHeight_const_on_component (U : Set ℝ) (S : ℝ → ℝ)
    {r t : ℝ} (hr : r∈U) (ht : t∈ordConnectedComponent U r) :
    capEndHeight U S t=capEndHeight U S r := by
  have htU := ordConnectedComponent_subset ht
  simp only [capEndHeight,if_pos hr,if_pos htU]
  rw [ordConnectedComponent_eq ht]

theorem capEndHeight_monotoneOn {U : Set ℝ} {S : ℝ → ℝ} {a b Y : ℝ}
    (hU : U⊆Icc a b) (hS : MonotoneOn S (Icc a b))
    (hSb : ∀r∈Icc a b,S r≤Y) : MonotoneOn (capEndHeight U S) (Icc a b) := by
  intro r hr t ht hrt
  have htlo := (capEndHeight_bounds hU hSb ht).1
  by_cases hrU:r∈U
  · by_cases htr : t∈ordConnectedComponent U r
    · exact le_of_eq (capEndHeight_const_on_component U S hrU htr).symm
    · have hne : (S '' ordConnectedComponent U r).Nonempty :=
        (nonempty_ordConnectedComponent.mpr hrU).image S
      have hle : capEndHeight U S r≤S t := by
        simp only [capEndHeight,if_pos hrU]
        apply csSup_le hne
        rintro _ ⟨z,hz,rfl⟩
        have hzt : z≤t := by
          by_contra hno
          have htz : t≤z := (lt_of_not_ge hno).le
          have hmem : t∈uIcc r z := by rw [uIcc_of_le (hrt.trans htz)]; exact ⟨hrt,htz⟩
          exact htr ((inferInstance : OrdConnected (ordConnectedComponent U r)).uIcc_subset
            (self_mem_ordConnectedComponent.mpr hrU) hz hmem)
        exact hS (hU (ordConnectedComponent_subset hz)) ht hzt
      exact hle.trans htlo
  · simpa only [capEndHeight,if_neg hrU] using (hS hr ht hrt).trans htlo

theorem capEndHeight_sub_le {U : Set ℝ} {S : ℝ → ℝ} {a b Y L : ℝ}
    (hU : U⊆Icc a b) (hSb : ∀r∈Icc a b,S r≤Y) (hL : 0≤L)
    (hcap : ∀r∈U,∀t∈ordConnectedComponent U r,S t≤S r+L)
    {r : ℝ} (hr : r∈Icc a b) : capEndHeight U S r-S r≤L := by
  by_cases hrU:r∈U
  · have hne : (S '' ordConnectedComponent U r).Nonempty :=
      (nonempty_ordConnectedComponent.mpr hrU).image S
    have hle : capEndHeight U S r≤S r+L := by
      simp only [capEndHeight,if_pos hrU]
      apply csSup_le hne
      rintro _ ⟨t,ht,rfl⟩
      exact hcap r hrU t ht
    linarith
  · simpa only [capEndHeight,if_neg hrU,sub_self] using hL

end OAI.SKFluctuations.WholeUnitSideKernel
