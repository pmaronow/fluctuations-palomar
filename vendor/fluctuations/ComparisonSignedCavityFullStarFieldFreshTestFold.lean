module

public import ComparisonSignedCavityStarFieldFreshTestFold

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem native_full_star_field_fresh_test_zero_factor
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (c : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (Q : (ι→ℝ)→T.Assignment→S→ℝ) (x : ι→ℝ) :
    let g:=MarkedPlacement.fresh T c
    nativeStarFieldTestMean w φ g.tree (g.embed s) 0 q
      (fun y σ=>Q y (g.restrict σ) (g.spin σ)) x=
    T.expect w φ q (fun σ=>nativeStarFreshTestMean w φ as 0 q (Q x σ) x) x := by
  dsimp only
  rw [nativeStarFieldTestMean_zero]
  change (T.fork (single (S:=S) as)).expect w φ q
    (fun σ=>Q x σ.1 (singleEquiv (S:=S) as σ.2)) x=_
  rw [expect_fork]
  apply congrArg (fun P=>T.expect w φ q P x)
  funext σ
  unfold nativeStarFreshTestMean
  simp only [Nat.zero_add]
  rfl

omit [Nonempty S] in
theorem native_full_star_field_fresh_test_factor
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (_hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (Q : (ι→ℝ)→T.Assignment→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldTestMean w φ g.tree (g.embed s) star q
      (fun y σ=>Q y (g.restrict σ) (g.spin σ)) x=
    nativeStarFieldTestMean w φ T s star q
      (fun y σ=>nativeStarFreshTestMean w φ as star q (Q y σ) y) x := by
  induction T generalizing a aFresh star q x with
  | leaf=>
    have HS:star=0:=by simpa only [List.length_nil,Nat.le_zero] using hstar
    subst star
    exact native_full_star_field_fresh_test_zero_factor leaf s (aFresh-1) w φ q Q x
  | @step b tail T ih=>
    cases star with
    | zero=>
      exact native_full_star_field_fresh_test_zero_factor (T.step b) s (aFresh-b.val) w φ q Q x
    | succ star=>
      have HS:star≤tail.length:=by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hstar
      dsimp only [nativeFreshAtSlot]
      change shiftedMean _ _ _
        (nativeStarFieldTestMean w φ (nativeFreshAtSlot T b.val s star).tree
          ((nativeFreshAtSlot T b.val s star).embed s) star (fun j=>q (j+1))
          (fun y σ=>Q y ((nativeFreshAtSlot T b.val s star).restrict σ)
            ((nativeFreshAtSlot T b.val s star).spin σ))) x=
        shiftedMean _ _ _ (nativeStarFieldTestMean w φ T s star
          (fun j=>q (j+1)) (fun y σ=>nativeStarFreshTestMean w φ (b::tail) (star+1) q (Q y σ) y)) x
      congr 1
      funext y
      simp_rw [nativeStarFreshTestMean_step]
      exact ih s star HS b.val ho.2.2 (fun j=>q (j+1)) Q y
  | @fork tail T V ihT ihV=>
    cases star with
    | zero=>
      exact native_full_star_field_fresh_test_zero_factor (T.fork V) s (-aFresh) w φ q Q x
    | succ star=>
      cases s with
      | inl s=>
        dsimp only [nativeFreshAtSlot]
        change (∑τ,V.weight w φ q τ x*
          nativeStarFieldTestMean w φ (nativeFreshAtSlot T aFresh s (star+1)).tree
            ((nativeFreshAtSlot T aFresh s (star+1)).embed s) (star+1) q
            (fun y σ=>Q y ((nativeFreshAtSlot T aFresh s (star+1)).restrict σ,τ)
              ((nativeFreshAtSlot T aFresh s (star+1)).spin σ)) x)=
          (∑τ,V.weight w φ q τ x*
            nativeStarFieldTestMean w φ T s (star+1) q
              (fun y σ=>nativeStarFreshTestMean w φ tail (star+1) q (Q y (σ,τ)) y) x)
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT s (star+1) hstar aFresh ho q (fun y σ d=>Q y (σ,τ) d) x
      | inr s=>
        dsimp only [nativeFreshAtSlot]
        change (∑τ,T.weight w φ q τ x*
          nativeStarFieldTestMean w φ (nativeFreshAtSlot V aFresh s (star+1)).tree
            ((nativeFreshAtSlot V aFresh s (star+1)).embed s) (star+1) q
            (fun y σ=>Q y (τ,(nativeFreshAtSlot V aFresh s (star+1)).restrict σ)
              ((nativeFreshAtSlot V aFresh s (star+1)).spin σ)) x)=
          (∑τ,T.weight w φ q τ x*
            nativeStarFieldTestMean w φ V s (star+1) q
              (fun y σ=>nativeStarFreshTestMean w φ tail (star+1) q (Q y (τ,σ)) y) x)
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihV s (star+1) hstar aFresh ho q (fun y σ d=>Q y (τ,σ) d) x

omit [Nonempty S] in
theorem native_full_star_field_fresh_selector_factor
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0)
    (J : (ι→ℝ)→T.Assignment→ℝ)
    (U : (ι→ℝ)→T.Assignment→S) (F : S→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldTestMean w φ g.tree (g.embed s) star q
      (fun y σ=>J y (g.restrict σ)*F (U y (g.restrict σ)) (g.spin σ)) x=
    nativeStarFieldTestMean w φ T s star q
      (fun y σ=>J y σ*nativeStarPairFactor w φ as star q F y (U y σ)) x := by
  dsimp only
  rw [native_full_star_field_fresh_test_factor T s star hstar aFresh hw φ ho q
    (fun y σ d=>J y σ*F (U y σ) d) x]
  apply congrArg (fun L=>nativeStarFieldTestMean w φ T s star q L x)
  funext y σ
  unfold nativeStarFreshTestMean nativeStarPairFactor
  exact native_expect_const_mul (single (as.drop star)) w φ _ _ (J y σ) y

end OAI.SKFluctuations.Hierarchy.ClockTree
