module

public import ComparisonSignedCavityActualGLawRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

def nativeOriginalGCenterShift {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K b C C' : ℕ→ℝ) (a c e f : T.Slot) : ℝ :=
  if U≤T.splitIndex a c ∧ U≤T.splitIndex a e ∧ U≤T.splitIndex a f ∧ e≠f then
    (1/2:ℝ)*fullScalarCutConnected4 T U K a c e f*b (T.splitIndex e f)*
      (C' (T.splitIndex e f)-C (T.splitIndex e f)) else 0

theorem native_original_high_G_atom_center_difference {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K b C C' : ℕ→ℝ)
    (a c e f : T.Slot) (σ : T.Assignment) :
    nativeOriginalHighGAtom T U K b C a c e f σ-
      nativeOriginalHighGAtom T U K b C' a c e f σ=
      nativeOriginalGCenterShift T U K b C C' a c e f := by
  unfold nativeOriginalHighGAtom nativeOriginalGCenterShift
  split_ifs <;> ring

theorem native_original_three_marked_test_preserves (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : ClockTree.MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0) :
    z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))) x=
      T.disorderExpect (fullWeight n) (fullFeature n) v q P x := by
  rw [r.tree.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho z hz
      v q (fun σ=>P (p.restrict (r.restrict σ))) x,
    p.tree.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho r hr
      v q (fun σ=>P (p.restrict σ)) x,
    T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho p hp v q P x]

theorem native_original_G_placement_center_difference (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C C' : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : ClockTree.MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (z : ClockTree.MarkedPlacement r.tree) (hz : z∈r.tree.markedAttach 0) :
    z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*
        nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x-
    z.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*
        nativeOriginalHighGAtom z.tree U K b C' (z.embed (r.embed (p.embed a)))
          (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) x=
    nativeOriginalGCenterShift z.tree U K b C C' (z.embed (r.embed (p.embed a)))
      (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark*
      T.disorderExpect (fullWeight n) (fullFeature n) v q P x := by
  let Q:=fun σ=>P (p.restrict (r.restrict (z.restrict σ)))
  let A:=nativeOriginalHighGAtom z.tree U K b C (z.embed (r.embed (p.embed a)))
    (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark
  let B:=nativeOriginalHighGAtom z.tree U K b C' (z.embed (r.embed (p.embed a)))
    (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark
  let d:=nativeOriginalGCenterShift z.tree U K b C C' (z.embed (r.embed (p.embed a)))
    (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark
  have Hlin : z.tree.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>Q σ*A σ) x-
      z.tree.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>Q σ*B σ) x=
    z.tree.disorderExpect (fullWeight n) (fullFeature n) v q (fun σ=>Q σ*(A σ-B σ)) x := by
    unfold ClockTree.disorderExpect
    simp only [mul_sub,Finset.sum_sub_distrib]
  have Htest : (fun σ=>Q σ*(A σ-B σ))=(fun σ=>d*Q σ) := by
    funext σ
    dsimp only [A,B,d]
    rw [native_original_high_G_atom_center_difference]
    ring
  rw [Htest,z.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho] at Hlin
  change _=d*T.disorderExpect (fullWeight n) (fullFeature n) v q P x
  rw [Hlin]
  congr 1
  exact native_original_three_marked_test_preserves n v q x T ho P p hp r hr z hz

theorem native_original_full_centered_mean_zero (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>P σ-T.disorderExpect (fullWeight n) (fullFeature n) v q P x) x=0 := by
  unfold ClockTree.disorderExpect
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
  rw [(T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x).2]
  ring

theorem native_original_longitudinal_centered_center_independent (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C C' : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot) :
    let mean:=T.disorderExpect (fullWeight n) (fullFeature n) v q P x
    nativeOriginalLongitudinalPairing n v q x U K b C T (fun σ=>P σ-mean) a=
      nativeOriginalLongitudinalPairing n v q x U K b C' T (fun σ=>P σ-mean) a := by
  dsimp only
  unfold nativeOriginalLongitudinalPairing
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  congr 1
  have H:=native_original_G_placement_center_difference n v q x U K b C C' T ho
    (fun σ=>P σ-T.disorderExpect (fullWeight n) (fullFeature n) v q P x) a p hp r hr z hz
  rw [native_original_full_centered_mean_zero n v q x T ho P,mul_zero] at H
  exact sub_eq_zero.mp H

end OAI.SKFluctuations.Cavity
