module

public import ComparisonActualHighWallThetaZeroEq7WallCutGeometry
public import ComparisonActualHighWallThetaZeroOrdinaryPhysicalBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 22000000
attribute [local instance] Classical.propDecidable

open ActualThetaZeroOverlapMinimum

theorem eventually_actual_theta_zero_eq7_wall_started_ordinary_budget
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (ι : Type*) [Fintype ι]
        (c : ι → ShiftedCapInterval Q P) (v Lside cut : ℝ),
      0 < v → Q.eq7WallCutMass ≤ 1 →
      max Q.eq7WallCutMass v < min (16*v) 1 →
      (∀t,∀r∈Ioo (c t).left (c t).right,
        wholeUnit P.negativeSet r=Ioo (c t).left (c t).right) →
      (∀t, P.H (c t).left=0 ∧
        (P.H (c t).right=0 ∨ (c t).right=1)) →
      Pairwise (fun t u => Disjoint
        (Ioo (c t).left (c t).right)
        (Ioo (c u).left (c u).right)) →
      (∀t, max Q.eq7WallCutMass v ≤ Q.alpha.val.val (c t).left) →
      (∀t, Q.alpha.val.val (c t).right ≤ min (16*v) 1) →
      0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,
        (P.retainedSupport c
          (Q.shiftedNativeModel.R (max Q.eq7WallCutMass v))
          (Q.shiftedNativeModel.R (min (16*v) 1))).indicator
            (fun _ => 1) (Q.shiftedNativeModel.R u)*
              Q.shiftedNativeModel.thermal u) ≤
      Q.ordinaryOptimizedBudget ell Qraw 16 Lside cut (16*v)
        (max Q.eq7WallCutMass v) (Q.xs+min (16*v) 1) v 16
        (Q.shiftedNativeModel.R (min (16*v) 1)) := by
  obtain ⟨Qraw,hQraw,Hphysical⟩ :=
    eventually_actual_theta_zero_ordinary_optimized_budget
      ell hell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hphysical] with n hn
  intro Q P ι inst c v Lside cut hv hcut1 hwindow hwhole hcontacts
    hdisjoint hleft hright hLside hcut hlogcut
  let b := Q.eq7WallCutMass
  let q := max b v
  let z := min (16*v) 1
  let ag := Q.shiftedNativeModel.R q
  let zg := Q.shiftedNativeModel.R z
  have hU := Q.data.hU
  have hbS : Q.data.s < b := by
    dsimp only [b,eq7WallCutMass]
    linarith only [hU]
  have hqS : Q.data.s < q := hbS.trans_le (le_max_left _ _)
  have hqpos : 0 < q := Q.data.hs.1.trans hqS
  have hz1 : z ≤ 1 := min_le_right _ _
  have hqz : q < z := hwindow
  have hqMass : q ∈ Icc Q.data.s 1 :=
    ⟨hqS.le, hqz.le.trans hz1⟩
  have hzMass : z ∈ Icc Q.data.s 1 :=
    ⟨hqS.le.trans hqz.le, hz1⟩
  have hag : Q.data.rmin < ag := by
    have H := Q.shiftedNativeModel.R_strictMonoOn
      ⟨le_rfl,Q.data.hs1⟩ hqMass hqS
    rw [Q.shiftedNativeModel.R_left] at H
    exact H
  have hagz : ag ≤ zg :=
    Q.shiftedNativeModel.R_monotone hqz.le
  have hzg : zg ≤ 1 := (Q.shiftedNativeModel.R_bounds z).2
  have hcapLeft : ∀ t, ag ≤ (c t).left := by
    intro t
    have H := Q.shiftedNativeModel.R_monotone (hleft t)
    rw [Q.shiftedNativeModel.R_inverse
      ⟨(c t).hleft,(c t).hlt.le.trans (c t).hright⟩] at H
    exact H
  have hcapRight : ∀ t, (c t).right ≤ zg := by
    intro t
    have H := Q.shiftedNativeModel.R_monotone (hright t)
    rw [Q.shiftedNativeModel.R_inverse
      ⟨(c t).hleft.trans (c t).hlt.le,(c t).hright⟩] at H
    exact H
  have hloCaps : ∀t, v ≤ Q.alpha.val.val (c t).left := by
    intro t
    exact (le_max_right _ _).trans (hleft t)
  have hratio : z+comparisonSmallMass Q.data.N Q.data.E ≤
      16*(v+comparisonSmallMass Q.data.N Q.data.E) := by
    have Hz : z ≤ 16*v := min_le_left _ _
    linarith only [Hz,hU]
  have hwidth : Q.alpha.val.val zg-Q.alpha.val.val ag ≤ 16*v := by
    rw [Q.shiftedNativeModel.R_spec hzMass,
      Q.shiftedNativeModel.R_spec hqMass]
    have Hz : z ≤ 16*v := min_le_left _ _
    have Hq : 0 ≤ q := hqpos.le
    linarith only [Hz,Hq]
  have hsourceLeft : ∀ t,
      v ≤ Q.alpha.val.val (c t).left+
        comparisonSmallMass Q.data.N Q.data.E := by
    intro t
    have Hv : v ≤ q := le_max_right _ _
    linarith only [Hv,hleft t,hU]
  have hsourceSpan : ∀ t,
      Q.alpha.val.val (c t).right-Q.alpha.val.val (c t).left ≤ 16*v := by
    intro t
    have Hz : z ≤ 16*v := min_le_left _ _
    have Hleft : 0 ≤ Q.alpha.val.val (c t).left :=
      (Q.alpha.val.property.1 (c t).left).1
    linarith only [hright t,Hz,Hleft]
  have hy : 0 < Q.xs+z := by
    have hz0 : 0 ≤ z := hqpos.le.trans hqz.le
    exact add_pos_of_pos_of_nonneg Q.hxs hz0
  have H := hn Q P ι c ag zg v z 16 (16*v) q (Q.xs+z)
    v 16 Lside cut hwhole hcontacts hdisjoint hag hagz hzg
    hcapLeft hcapRight hv.le (by norm_num) hratio hloCaps hright
    (by positivity) hwidth hqpos (by rw [Q.shiftedNativeModel.R_spec hqMass])
    hy (by rw [Q.shiftedNativeModel.R_spec hzMass]) hv (by norm_num)
    hsourceLeft hsourceSpan hLside hcut hlogcut
  simpa only [b,q,z,ag,zg] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
