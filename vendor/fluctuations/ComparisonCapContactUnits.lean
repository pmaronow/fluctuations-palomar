module

public import ComparisonCapHeightEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set
attribute [local instance] Classical.propDecidable

def wholeUnit (U : Set ℝ) (r : ℝ) : Set ℝ :=
  if r∈U then ordConnectedComponent U r else {r}

theorem self_mem_wholeUnit (U : Set ℝ) (r : ℝ) : r∈wholeUnit U r := by
  by_cases hr:r∈U <;> simp [wholeUnit,hr]

theorem wholeUnit_ordConnected (U : Set ℝ) (r : ℝ) : OrdConnected (wholeUnit U r) := by
  by_cases hr:r∈U
  · simpa only [wholeUnit,ite_eq_left hr] using
      (inferInstance : OrdConnected (ordConnectedComponent U r))
  · simpa only [wholeUnit,ite_eq_right hr] using (inferInstance : OrdConnected ({r}:Set ℝ))

theorem wholeUnit_eq_of_mem (U : Set ℝ) {r t : ℝ} (ht : t∈wholeUnit U r) :
    wholeUnit U t=wholeUnit U r := by
  by_cases hr:r∈U
  · have ht' : t∈ordConnectedComponent U r := by simpa [wholeUnit,hr] using ht
    have htU := ordConnectedComponent_subset ht'
    simp only [wholeUnit,ite_eq_left hr,ite_eq_left htU]
    exact (ordConnectedComponent_eq ht').symm
  · have he : t=r := by simpa [wholeUnit,hr] using ht
    rw [he]

theorem wholeUnit_disjoint_of_ne (U : Set ℝ) {r t : ℝ}
    (hne : wholeUnit U r≠wholeUnit U t) : Disjoint (wholeUnit U r) (wholeUnit U t) := by
  apply disjoint_left.mpr
  intro z hz hzt
  exact hne ((wholeUnit_eq_of_mem U hz).symm.trans (wholeUnit_eq_of_mem U hzt))

theorem disjoint_ordConnected_sets_ordered {A B : Set ℝ} (hA : OrdConnected A)
    (hB : OrdConnected B) (hd : Disjoint A B) {r t : ℝ}
    (hr : r∈A) (ht : t∈B) (hrt : r≤t) {z w : ℝ} (hz : z∈A) (hw : w∈B) : z<w := by
  by_contra hno
  have hwz : w≤z := le_of_not_gt hno
  by_cases htz:t≤z
  · exact disjoint_left.mp hd (hA.out' hr hz ⟨hrt,htz⟩) ht
  · by_cases hwr:w≤r
    · exact disjoint_left.mp hd hr (hB.out' hw ht ⟨hwr,hrt⟩)
    · have hrw : r≤w := (lt_of_not_ge hwr).le
      exact disjoint_left.mp hd (hA.out' hr hz ⟨hrw,hwz⟩) hw

theorem different_wholeUnits_ordered (U : Set ℝ) {r t z w : ℝ}
    (hrt : r≤t) (hne : wholeUnit U r≠wholeUnit U t)
    (hz : z∈wholeUnit U r) (hw : w∈wholeUnit U t) : z<w :=
  disjoint_ordConnected_sets_ordered (wholeUnit_ordConnected U r)
    (wholeUnit_ordConnected U t) (wholeUnit_disjoint_of_ne U hne)
    (self_mem_wholeUnit U r) (self_mem_wholeUnit U t) hrt hz hw

theorem reversed_wholeUnit_samples_same_cap (U : Set ℝ) {r t z w : ℝ}
    (hrt : r≤t) (hz : z∈wholeUnit U r) (hw : w∈wholeUnit U t) (hwz : w<z) :
    wholeUnit U r=wholeUnit U t ∧ r∈U ∧
      z∈ordConnectedComponent U r ∧ w∈ordConnectedComponent U r := by
  have he : wholeUnit U r=wholeUnit U t := by
    by_contra hne
    exact (different_wholeUnits_ordered U hrt hne hz hw).not_gt hwz
  rw [←he] at hw
  have hrU : r∈U := by
    by_contra hr
    have hz' : z=r := by simpa [wholeUnit,hr] using hz
    have hw' : w=r := by simpa [wholeUnit,hr] using hw
    rw [hz',hw'] at hwz
    exact lt_irrefl _ hwz
  refine ⟨he,hrU,?_,?_⟩
  · simpa [wholeUnit,hrU] using hz
  · simpa [wholeUnit,hrU] using hw

theorem capEndHeight_const_on_wholeUnit (U : Set ℝ) (S : ℝ→ℝ)
    {r t : ℝ} (ht : t∈wholeUnit U r) : capEndHeight U S t=capEndHeight U S r := by
  by_cases hr:r∈U
  · exact capEndHeight_const_on_component U S hr (by simpa [wholeUnit,hr] using ht)
  · have he : t=r := by simpa [wholeUnit,hr] using ht
    rw [he]

end OAI.SKFluctuations.WholeUnitSideKernel
