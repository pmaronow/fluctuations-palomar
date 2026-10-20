module

public import ComparisonSignedCavityStarFieldTestFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeStarFreshTestMean (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (as : List PositiveMass) (star : ℕ) (q : ℕ→ι→ℝ≥0)
    (Q : S→ℝ) (x : ι→ℝ) : ℝ :=
  (single (S:=S) (as.drop star)).expect w φ (fun j=>q (star+j))
    (fun σ=>Q (singleEquiv (S:=S) (as.drop star) σ)) x

omit [Nonempty S] in
theorem nativeStarFreshTestMean_step (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (b : PositiveMass) (as : List PositiveMass) (star : ℕ) (q : ℕ→ι→ℝ≥0)
    (Q : S→ℝ) (x : ι→ℝ) :
    nativeStarFreshTestMean w φ (b::as) (star+1) q Q x=
      nativeStarFreshTestMean w φ as star (fun j=>q (j+1)) Q x := by
  unfold nativeStarFreshTestMean
  apply congrArg (fun z=>(single (S:=S) (as.drop star)).expect w φ z
    (fun σ=>Q (singleEquiv (S:=S) (as.drop star) σ)) x)
  funext j
  congr 1
  omega

omit [Nonempty S] in
theorem native_star_field_fresh_test_zero_factor
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (c : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (Q : (ι→ℝ)→T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    let g:=MarkedPlacement.fresh T c
    nativeStarFieldTestMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot (g.embed s)) 0 q
      (fun y σ=>Q y (g.restRestrict σ) (g.restSpin σ)) x=
    T.cavityLeft.expect w φ q (fun σ=>nativeStarFreshTestMean w φ as 0 q (Q x σ) x) x := by
  dsimp only
  rw [nativeStarFieldTestMean_zero]
  simp_rw [MarkedPlacement.restRestrict_fresh]
  change (T.cavityLeft.fork (single (S:=S×B) as).cavityLeft).expect w φ q
    (fun σ=>Q x σ.1 ((single (S:=S×B) as).cavityLeft.atSlot σ.2
      ((single (S:=S×B) as).cavityLeftSlot (singleSlot as)))) x=_
  rw [expect_fork]
  apply congrArg (fun P=>T.cavityLeft.expect w φ q P x)
  funext σ
  unfold nativeStarFreshTestMean
  simp only [List.drop_zero,Nat.zero_add]
  exact native_single_expect_atSlot_of_tree_eq (single (S:=S×B) as).cavityLeft
    (single_cavityLeft as) ((single (S:=S×B) as).cavityLeftSlot (singleSlot as))
    w φ q (Q x σ) x

omit [Nonempty S] in
theorem native_star_field_fresh_test_factor
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (Q : (ι→ℝ)→T.cavityLeft.Assignment→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldTestMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot (g.embed s)) star q
      (fun y σ=>Q y (g.restRestrict σ) (g.restSpin σ)) x=
    nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star q
      (fun y σ=>nativeStarFreshTestMean w φ as star q (Q y σ) y) x := by
  induction T generalizing a aFresh star q x with
  | leaf=>
    have HS:star=0:=by simpa only [List.length_nil,Nat.le_zero] using hstar
    subst star
    exact native_star_field_fresh_test_zero_factor leaf s (aFresh-1) w φ q Q x
  | @step b tail T ih=>
    cases star with
    | zero=>
      exact native_star_field_fresh_test_zero_factor (T.step b) s (aFresh-b.val) w φ q Q x
    | succ star=>
      have HS:star≤tail.length:=by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hstar
      dsimp only [nativeFreshAtSlot]
      change shiftedMean _ _ _
        (nativeStarFieldTestMean w φ (nativeFreshAtSlot T b.val s star).tree.cavityLeft
          ((nativeFreshAtSlot T b.val s star).tree.cavityLeftSlot
            ((nativeFreshAtSlot T b.val s star).embed s)) star (fun j=>q (j+1))
          (fun y σ=>Q y ((nativeFreshAtSlot T b.val s star).restRestrict σ)
            ((nativeFreshAtSlot T b.val s star).restSpin σ))) x=
        shiftedMean _ _ _ (nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star
          (fun j=>q (j+1)) (fun y σ=>nativeStarFreshTestMean w φ (b::tail) (star+1) q (Q y σ) y)) x
      congr 1
      funext y
      simp_rw [nativeStarFreshTestMean_step]
      exact ih s star HS b.val ho.2.2 (fun j=>q (j+1)) Q y
  | @fork tail T V ihT ihV=>
    cases star with
    | zero=>
      exact native_star_field_fresh_test_zero_factor (T.fork V) s (-aFresh) w φ q Q x
    | succ star=>
      cases s with
      | inl s=>
        dsimp only [nativeFreshAtSlot]
        simp_rw [MarkedPlacement.restRestrict_left,MarkedPlacement.restSpin_left]
        change (∑τ,V.cavityLeft.weight w φ q τ x*
          nativeStarFieldTestMean w φ (nativeFreshAtSlot T aFresh s (star+1)).tree.cavityLeft
            ((nativeFreshAtSlot T aFresh s (star+1)).tree.cavityLeftSlot
              ((nativeFreshAtSlot T aFresh s (star+1)).embed s)) (star+1) q
            (fun y σ=>Q y ((nativeFreshAtSlot T aFresh s (star+1)).restRestrict σ,τ)
              ((nativeFreshAtSlot T aFresh s (star+1)).restSpin σ)) x)=
          (∑τ,V.cavityLeft.weight w φ q τ x*
            nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) (star+1) q
              (fun y σ=>nativeStarFreshTestMean w φ tail (star+1) q (Q y (σ,τ)) y) x)
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT s (star+1) hstar aFresh ho q (fun y σ d=>Q y (σ,τ) d) x
      | inr s=>
        dsimp only [nativeFreshAtSlot]
        simp_rw [MarkedPlacement.restRestrict_right,MarkedPlacement.restSpin_right]
        change (∑τ,T.cavityLeft.weight w φ q τ x*
          nativeStarFieldTestMean w φ (nativeFreshAtSlot V aFresh s (star+1)).tree.cavityLeft
            ((nativeFreshAtSlot V aFresh s (star+1)).tree.cavityLeftSlot
              ((nativeFreshAtSlot V aFresh s (star+1)).embed s)) (star+1) q
            (fun y σ=>Q y (τ,(nativeFreshAtSlot V aFresh s (star+1)).restRestrict σ)
              ((nativeFreshAtSlot V aFresh s (star+1)).restSpin σ)) x)=
          (∑τ,T.cavityLeft.weight w φ q τ x*
            nativeStarFieldTestMean w φ V.cavityLeft (V.cavityLeftSlot s) (star+1) q
              (fun y σ=>nativeStarFreshTestMean w φ tail (star+1) q (Q y (τ,σ)) y) x)
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihV s (star+1) hstar aFresh ho q (fun y σ d=>Q y (τ,σ) d) x

omit [Nonempty S] in
theorem native_star_field_fresh_selector_factor
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (J : (ι→ℝ)→T.cavityLeft.Assignment→ℝ)
    (U : (ι→ℝ)→T.cavityLeft.Assignment→S) (F : S→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldTestMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot (g.embed s)) star q
      (fun y σ=>J y (g.restRestrict σ)*F (U y (g.restRestrict σ)) (g.restSpin σ)) x=
    nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star q
      (fun y σ=>J y σ*nativeStarPairFactor w φ as star q F y (U y σ)) x := by
  dsimp only
  rw [native_star_field_fresh_test_factor T s star hstar aFresh hw φ ho q
    (fun y σ d=>J y σ*F (U y σ) d) x]
  apply congrArg (fun L=>nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star q L x)
  funext y σ
  unfold nativeStarFreshTestMean nativeStarPairFactor
  exact native_expect_const_mul (single (as.drop star)) w φ _ _ (J y σ) y

end OAI.SKFluctuations.Hierarchy.ClockTree
