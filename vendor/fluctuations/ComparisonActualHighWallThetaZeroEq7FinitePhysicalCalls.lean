module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs
public import ComparisonActualHighWallThetaZeroEq7OriginOrdinaryGroup
public import ComparisonActualHighWallThetaZeroEq7WallStartedOrdinary
public import ComparisonActualHighWallThetaZeroBroadSliceSourcePositiveOrigin
public import ComparisonActualHighWallThetaZeroCapFamily

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

open ActualThetaZeroOverlapMinimum

theorem eventually_eq7_inner_low_piece_physical_draft
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet))
        (h : ℝ) (j : Eq7InnerLowDyad Q h) (Lside cut : ℝ),
      0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,
        (eq7InnerLowSupport (P.capFamily F) j).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤
      Q.ordinaryOptimizedBudgetPositiveOrigin ell Qraw 16 Lside cut
        (16*Q.eq7InnerDyadMass j.val.val) Q.data.s
        (Q.xs+Q.eq7InnerDyadRight j.val.val)
        (Q.eq7InnerDyadMass j.val.val) 16
        (Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)) := by
  obtain ⟨Qraw,hQraw,Hsource⟩ :=
    eventually_actual_theta_zero_eq7_origin_ordinary_group_budget ell hell
      Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hsource] with n hn
  intro Q P F h j Lside cut hLside hcut hlogcut
  let c := fun i : Eq7InnerLowCapIndex (P.capFamily F) j =>
    P.capFamily F i.val
  have hv : 0 < Q.eq7InnerDyadMass j.val.val := by
    exact (comparison_mass_dyadic_scale Q.data.hU j.val.val).1
  have hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right := by
    intro t r hr
    exact P.capFamily_wholeUnit F t.val hr
  have hcontacts : ∀t,
      (P.H (c t).left=0 ∨ (c t).left=Q.data.rmin) ∧
      (P.H (c t).right=0 ∨ (c t).right=1) := by
    intro t
    exact P.capFamily_contacts F t.val
  have hinitial : ∀t, (c t).left=Q.data.rmin →
      comparisonSmallMass Q.data.N Q.data.E ≤
        Q.alpha.val.val (c t).right-Q.alpha.val.val (c t).left := by
    intro t ht
    rcases t.property.2.2.2 with hnot | hw
    · exact False.elim (hnot ht)
    · exact hw
  have hdisjoint : Pairwise (fun t u => Disjoint
      (Ioo (c t).left (c t).right)
      (Ioo (c u).left (c u).right)) := by
    intro t u htu
    exact P.capFamily_disjoint F (fun he => htu (Subtype.ext he))
  have H := hn Q P _ c (Q.eq7InnerDyadMass j.val.val) Lside cut hv
    j.property.1 j.property.2.2 hwhole hcontacts hinitial hdisjoint
    (fun t => t.property.2.1) (fun t => t.property.2.2.1)
    hLside hcut hlogcut
  simpa only [c,eq7InnerLowSupport,eq7InnerDyadRight] using H

theorem eventually_eq7_inner_post_piece_physical_draft
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet))
        (h : ℝ) (j : Eq7InnerPostDyad Q h) (Lside cut : ℝ),
      0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,
        (eq7InnerPostSupport (P.capFamily F) j).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤
      Q.ordinaryOptimizedBudget ell Qraw 16 Lside cut
        (16*Q.eq7InnerDyadMass j.val.val)
        (Q.eq7InnerWallStart j.val.val)
        (Q.xs+Q.eq7InnerDyadRight j.val.val)
        (Q.eq7InnerDyadMass j.val.val) 16
        (Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)) := by
  obtain ⟨Qraw,hQraw,Hsource⟩ :=
    eventually_actual_theta_zero_eq7_wall_started_ordinary_budget ell hell
      Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hsource] with n hn
  intro Q P F h j Lside cut hLside hcut hlogcut
  let c := fun i : Eq7InnerPostCapIndex (P.capFamily F) j =>
    P.capFamily F i.val
  have hv : 0 < Q.eq7InnerDyadMass j.val.val := by
    exact (comparison_mass_dyadic_scale Q.data.hU j.val.val).1
  have hq : Q.eq7InnerWallStart j.val.val < Q.eq7InnerDyadRight j.val.val :=
    j.property.2
  have hcut1 : Q.eq7WallCutMass ≤ 1 := by
    change Q.data.s+comparisonSmallMass Q.data.N Q.data.E ≤ 1
    exact (le_max_left _ _).trans (hq.le.trans (min_le_right _ _))
  have hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right := by
    intro t r hr
    exact P.capFamily_wholeUnit F t.val hr
  have hcontacts : ∀t,
      P.H (c t).left=0 ∧
      (P.H (c t).right=0 ∨ (c t).right=1) := by
    intro t
    have hc := P.capFamily_contacts F t.val
    refine ⟨?_,hc.2⟩
    rcases hc.1 with hzero | hinitial
    · exact hzero
    · have hleft := t.property.2.1
      rw [hinitial,Q.alpha.property.1] at hleft
      have hqstart : Q.data.s+comparisonSmallMass Q.data.N Q.data.E ≤
          Q.eq7InnerWallStart j.val.val := le_max_left _ _
      exfalso
      linarith only [hleft,hqstart,Q.data.hU]
  have hdisjoint : Pairwise (fun t u => Disjoint
      (Ioo (c t).left (c t).right)
      (Ioo (c u).left (c u).right)) := by
    intro t u htu
    exact P.capFamily_disjoint F (fun he => htu (Subtype.ext he))
  have H := hn Q P _ c (Q.eq7InnerDyadMass j.val.val) Lside cut
    hv hcut1 (by simpa only [eq7WallCutMass,eq7InnerWallStart,eq7InnerDyadRight] using hq)
    hwhole hcontacts hdisjoint
    (fun t => t.property.2.1) (fun t => t.property.2.2)
    hLside hcut hlogcut
  simpa only [c,eq7InnerPostSupport,eq7InnerWallStart,eq7WallCutMass,
    eq7InnerDyadRight] using H

theorem eventually_eq7_inner_broad_slice_physical_draft
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet))
        (p : Eq7InnerBroadSliceIndex (P.capFamily F)) (Lside cut : ℝ),
      0 ≤ Lside → 0 < cut →
      2*cut < comparisonSmallMass Q.data.N Q.data.E →
      Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,
        (eq7InnerBroadSlice (P.capFamily F) p).indicator
          (fun _ => (1:ℝ)) (Q.shiftedNativeModel.R u)*
          Q.shiftedNativeModel.thermal u) ≤
      Q.criticalBroadMassBudget ell Qraw Lside cut
        ((eq7InnerBroadSampler (P.capFamily F) p.1).scale p.2)
        (∫r in eq7InnerBroadSlice (P.capFamily F) p,
          deriv Q.alpha.val.val r) := by
  obtain ⟨Qraw,hQraw,Hsource⟩ :=
    eventually_actual_theta_zero_broad_slice_thermal_positive_origin
      ell hell hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hsource] with n hn
  intro Q P F p Lside cut hLside hcut hcutU hlogcut
  let c := P.capFamily F p.1.val
  let f := eq7InnerBroadSampler (P.capFamily F) p.1
  have hcontacts := P.capFamily_contacts F p.1.val
  have H := hn Q P c f p.2 Lside cut hcontacts
    hLside hcut hcutU hlogcut
  simpa only [c,f,eq7InnerBroadSlice] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
