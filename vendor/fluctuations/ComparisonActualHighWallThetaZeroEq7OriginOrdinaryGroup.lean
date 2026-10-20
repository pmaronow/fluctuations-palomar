module

public import ComparisonActualHighWallThetaZeroOrdinaryPhysicalBudgetPositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

open ActualThetaZeroOverlapMinimum

theorem eventually_actual_theta_zero_eq7_origin_ordinary_group_budget
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (ι : Type*) [Fintype ι]
        (c : ι → ShiftedCapInterval Q P) (v Lside cut : ℝ),
      0 < v → comparisonSmallMass Q.data.N Q.data.E ≤ Q.data.s →
      Q.data.s ≤ min (16*v) 1 →
      (∀t,∀r∈Ioo (c t).left (c t).right,
        wholeUnit P.negativeSet r=Ioo (c t).left (c t).right) →
      (∀t, (P.H (c t).left=0 ∨ (c t).left=Q.data.rmin) ∧
        (P.H (c t).right=0 ∨ (c t).right=1)) →
      (∀t, (c t).left=Q.data.rmin →
        comparisonSmallMass Q.data.N Q.data.E ≤
          Q.alpha.val.val (c t).right-Q.alpha.val.val (c t).left) →
      Pairwise (fun t u => Disjoint
        (Ioo (c t).left (c t).right)
        (Ioo (c u).left (c u).right)) →
      (∀t, v ≤ Q.alpha.val.val (c t).left) →
      (∀t, Q.alpha.val.val (c t).right ≤ min (16*v) 1) →
      0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,
        (P.retainedSupport c Q.data.rmin
          (Q.shiftedNativeModel.R (min (16*v) 1))).indicator
            (fun _ => 1) (Q.shiftedNativeModel.R u)*
              Q.shiftedNativeModel.thermal u) ≤
      Q.ordinaryOptimizedBudgetPositiveOrigin ell Qraw 16 Lside cut
        (16*v) Q.data.s (Q.xs+min (16*v) 1) v 16
        (Q.shiftedNativeModel.R (min (16*v) 1)) := by
  obtain ⟨Qraw,hQraw,Hphysical⟩ :=
    eventually_actual_theta_zero_ordinary_optimized_budget_positive_origin
      ell hell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hphysical] with n hn
  intro Q P ι inst c v Lside cut hv hsU hsz hwhole hcontacts
    hinitialU hdisjoint hleft hright hLside hcut hlogcut
  let z := min (16*v) 1
  let zg := Q.shiftedNativeModel.R z
  have hzMass : z ∈ Icc Q.data.s 1 := ⟨hsz,min_le_right _ _⟩
  have hagz : Q.data.rmin ≤ zg := by
    have H := Q.shiftedNativeModel.R_monotone hsz
    rw [Q.shiftedNativeModel.R_left] at H
    exact H
  have hzg : zg ≤ 1 := (Q.shiftedNativeModel.R_bounds z).2
  have hcapLeft : ∀t, Q.data.rmin ≤ (c t).left := fun t => (c t).hleft
  have hcapRight : ∀t, (c t).right ≤ zg := by
    intro t
    have H := Q.shiftedNativeModel.R_monotone (hright t)
    rw [Q.shiftedNativeModel.R_inverse
      ⟨(c t).hleft.trans (c t).hlt.le,(c t).hright⟩] at H
    exact H
  have hratio : z+comparisonSmallMass Q.data.N Q.data.E ≤
      16*(v+comparisonSmallMass Q.data.N Q.data.E) := by
    have Hz : z ≤ 16*v := min_le_left _ _
    linarith only [Hz,Q.data.hU]
  have hwidth : Q.alpha.val.val zg-Q.alpha.val.val Q.data.rmin ≤ 16*v := by
    rw [Q.shiftedNativeModel.R_spec hzMass,Q.alpha.property.1]
    have Hz : z ≤ 16*v := min_le_left _ _
    linarith only [Hz,Q.data.hs.1]
  have hspan : ∀t,
      Q.alpha.val.val (c t).right-Q.alpha.val.val (c t).left ≤ 16*v := by
    intro t
    have Hz : z ≤ 16*v := min_le_left _ _
    have HL : 0 ≤ Q.alpha.val.val (c t).left :=
      (Q.alpha.val.property.1 (c t).left).1
    linarith only [hright t,Hz,HL]
  have hsourceLeft : ∀t,
      v ≤ Q.alpha.val.val (c t).left+
        comparisonSmallMass Q.data.N Q.data.E := by
    intro t
    linarith only [hleft t,Q.data.hU]
  have hy : 0 < Q.xs+z :=
    add_pos_of_pos_of_nonneg Q.hxs (Q.data.hs.1.le.trans hsz)
  have H := hn Q P ι c Q.data.rmin zg v z 16 (16*v) Q.data.s
    (Q.xs+z) v 16 Lside cut hwhole hcontacts hinitialU hdisjoint
    le_rfl hagz hzg hcapLeft hcapRight hv.le (by norm_num)
    hratio hleft hright (by positivity) hwidth Q.data.hs.1
    (by rw [Q.alpha.property.1]) hy
    (by rw [Q.shiftedNativeModel.R_spec hzMass]) hv (by norm_num)
    hsourceLeft hspan hLside hcut hlogcut
  simpa only [z,zg] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
