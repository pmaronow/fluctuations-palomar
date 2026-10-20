module

public import ComparisonSignedCavityFullStarFieldFreshTestFold
public import ComparisonSignedCavityStarFieldJointClassification

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 16000000

omit [Nonempty S] in
theorem native_full_star_field_fresh_disorder_test_factor
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (Q : (ι→ℝ)→T.Assignment→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldDisorderMean w φ g.tree (g.embed s) star v q
      (fun y σ=>Q y (g.restrict σ) (g.spin σ)) x=
    nativeStarFieldDisorderMean w φ T s star v q
      (fun y σ=>nativeStarFreshTestMean w φ as star
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) (Q y σ) y) x := by
  dsimp only
  unfold nativeStarFieldDisorderMean
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>native_full_star_field_fresh_test_factor
    T s star hstar aFresh hw φ ho _ Q (x+y))

omit [Nonempty S] in
theorem native_full_star_field_fresh_disorder_selector_factor
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (J : (ι→ℝ)→T.Assignment→ℝ)
    (U : (ι→ℝ)→T.Assignment→S) (F : S→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldDisorderMean w φ g.tree (g.embed s) star v q
      (fun y σ=>J y (g.restrict σ)*F (U y (g.restrict σ)) (g.spin σ)) x=
    nativeStarFieldDisorderMean w φ T s star v q
      (fun y σ=>J y σ*nativeStarPairFactor w φ as star
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) F y (U y σ)) x := by
  dsimp only
  unfold nativeStarFieldDisorderMean
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>native_full_star_field_fresh_selector_factor
    T s star hstar aFresh hw φ ho _ J U F (x+y))

theorem native_full_fresh_disorder_test_factor
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (Q : T.Assignment→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    g.tree.disorderExpect w φ v q (fun σ=>Q (g.restrict σ) (g.spin σ)) x=
    nativeStarFieldDisorderMean w φ T s star v q
      (fun y σ=>nativeStarFreshTestMean w φ as star
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) (Q σ) y) x := by
  dsimp only
  rw [←native_star_field_disorder_field_independent
    (nativeFreshAtSlot T aFresh s star).tree
    ((nativeFreshAtSlot T aFresh s star).embed s) star hw φ ho v q]
  exact native_full_star_field_fresh_disorder_test_factor
    T s star hstar aFresh hw φ ho v q (fun _ σ d=>Q σ d) x

theorem native_full_fresh_disorder_selector_factor
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (J : T.Assignment→ℝ) (U : T.Assignment→S) (F : S→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    g.tree.disorderExpect w φ v q
      (fun σ=>J (g.restrict σ)*F (U (g.restrict σ)) (g.spin σ)) x=
    nativeStarFieldDisorderMean w φ T s star v q
      (fun y σ=>J σ*nativeStarPairFactor w φ as star
        (cumulativeIncrements (q 0) (fun j=>q (j+1))) F y (U σ)) x := by
  dsimp only
  rw [←native_star_field_disorder_field_independent
    (nativeFreshAtSlot T aFresh s star).tree
    ((nativeFreshAtSlot T aFresh s star).embed s) star hw φ ho v q]
  exact native_full_star_field_fresh_disorder_selector_factor
    T s star hstar aFresh hw φ ho v q (fun _ σ=>J σ) (fun _ σ=>U σ) F x

end OAI.SKFluctuations.Hierarchy.ClockTree
