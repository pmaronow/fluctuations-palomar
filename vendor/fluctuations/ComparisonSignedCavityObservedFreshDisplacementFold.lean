module

public import ComparisonSignedCavityObservedWordDisorderFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] {as : List PositiveMass}

theorem native_star_field_fresh_displacement_fold
    (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (q : ℕ→ι→ℝ≥0) (A : S→S→ℝ)
    (J : (ι→ℝ)→T.cavityLeft.Assignment→ℝ)
    (U V : (ι→ℝ)→T.cavityLeft.Assignment→S) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldTestMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot (g.embed s)) star q
      (fun y σ=>J y (g.restRestrict σ)*
        (A (U y (g.restRestrict σ)) (g.restSpin σ)-A (V y (g.restRestrict σ)) (g.restSpin σ))) x=
    nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star q
      (fun y σ=>J y σ*(nativeStarPairFactor w φ as star q A y (U y σ)-
        nativeStarPairFactor w φ as star q A y (V y σ))) x := by
  dsimp only
  rw [native_star_field_fresh_test_factor T s star hstar aFresh hw φ ho q
    (fun y σ t=>J y σ*(A (U y σ) t-A (V y σ) t)) x]
  apply congrArg (fun L=>nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star q L x)
  funext y σ
  simp_rw [mul_sub]
  rw [native_star_fresh_paired_factor]

theorem native_star_field_disorder_fresh_displacement_fold
    (T : ClockTree (S×B) as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (A : S→S→ℝ)
    (J : (ι→ℝ)→T.cavityLeft.Assignment→ℝ)
    (U V : (ι→ℝ)→T.cavityLeft.Assignment→S) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldDisorderMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot (g.embed s)) star v q
      (fun y σ=>J y (g.restRestrict σ)*
        (A (U y (g.restRestrict σ)) (g.restSpin σ)-A (V y (g.restRestrict σ)) (g.restSpin σ))) x=
    nativeStarFieldDisorderMean w φ T.cavityLeft (T.cavityLeftSlot s) star v q
      (fun y σ=>J y σ*
        (nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1))) A y (U y σ)-
        nativeStarPairFactor w φ as star (cumulativeIncrements (q 0) (fun j=>q (j+1))) A y (V y σ))) x := by
  unfold nativeStarFieldDisorderMean
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>native_star_field_fresh_displacement_fold T s star hstar
    aFresh hw φ ho _ A J U V (x+y))

end OAI.SKFluctuations.Hierarchy.ClockTree
