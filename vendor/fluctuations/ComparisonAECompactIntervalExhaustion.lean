module

public import ComparisonScalarClosureIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory
open scoped Topology

theorem comparison_ae_on_open_interval_of_compact_interiors
    {a b : ℝ} {P : ℝ → Prop}
    (H : ∀s∈Ioo a b,∀t∈Ioo a b,s < t → ∀ᵐr∂volume.restrict (Icc s t),P r) :
    ∀ᵐr∂volume.restrict (Ioo a b),P r := by
  have HQ (q r : ℚ) : ∀ᵐu∂volume,
      (a < (q:ℝ) ∧ (q:ℝ) < (r:ℝ) ∧ (r:ℝ) < b) → u∈Icc (q:ℝ) (r:ℝ) → P u := by
    by_cases hqr : a < (q:ℝ) ∧ (q:ℝ) < (r:ℝ) ∧ (r:ℝ) < b
    · have Hp := (ae_restrict_iff' measurableSet_Icc).mp
        (H q ⟨hqr.1,hqr.2.1.trans hqr.2.2⟩ r
          ⟨hqr.1.trans hqr.2.1,hqr.2.2⟩ hqr.2.1)
      exact Hp.mono fun _ hu _=>hu
    · exact Eventually.of_forall fun _ h=>False.elim (hqr h)
  have Hall : ∀ᵐu∂volume,∀q r : ℚ,
      (a < (q:ℝ) ∧ (q:ℝ) < (r:ℝ) ∧ (r:ℝ) < b) → u∈Icc (q:ℝ) (r:ℝ) → P u :=
    ae_all_iff.mpr fun q=>ae_all_iff.mpr (HQ q)
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [Hall] with u hu hui
  obtain ⟨q,haq,hqu⟩ := exists_rat_btwn hui.1
  obtain ⟨r,hur,hrb⟩ := exists_rat_btwn hui.2
  exact hu q r ⟨haq,hqu.trans hur,hrb⟩ ⟨hqu.le,hur.le⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
