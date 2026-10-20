module

public import ComparisonSignedCavityActualProjectedRowOriginalLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

def nativeStarFieldTestMean (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) :
    {as : List PositiveMass} → (T : ClockTree S as) → T.Slot → ℕ →
      (ℕ → ι → ℝ≥0) → ((ι → ℝ) → T.Assignment → ℝ) → (ι → ℝ) → ℝ
  | _,.leaf,_,_,q,J,x=>leaf.expect w φ q (J x) x
  | _,.step b T,_,0,q,J,x=>(T.step b).expect w φ q (J x) x
  | _::as,.step b T,s,j+1,q,J,x=>
      shiftedMean (MeasureTheory.Measure.pi fun i=>ProbabilityTheory.gaussianReal 0 (q 0 i)) b.val
        (gaussianHierarchy w φ (clockSteps as (fun k=>q (k+1))))
        (nativeStarFieldTestMean w φ T s j (fun k=>q (k+1)) J) x
  | _,.fork T V,_,0,q,J,x=>(T.fork V).expect w φ q (J x) x
  | _,.fork T V,s,j+1,q,J,x=>match (s:T.Slot⊕V.Slot) with
    | Sum.inl s=>∑τ,V.weight w φ q τ x*
        nativeStarFieldTestMean w φ T s (j+1) q (fun y σ=>J y (σ,τ)) x
    | Sum.inr s=>∑σ,T.weight w φ q σ x*
        nativeStarFieldTestMean w φ V s (j+1) q (fun y τ=>J y (σ,τ)) x

omit [Nonempty S] in
theorem nativeStarFieldTestMean_zero (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot)
    (q : ℕ → ι → ℝ≥0) (J : (ι → ℝ) → T.Assignment → ℝ) (x : ι → ℝ) :
    nativeStarFieldTestMean w φ T s 0 q J x=T.expect w φ q (J x) x := by
  cases T <;> rfl

theorem native_star_field_test_field_independent
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (star : ℕ)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    nativeStarFieldTestMean w φ T s star q (fun _ σ=>P σ) x=T.expect w φ q P x := by
  induction T generalizing a star q x with
  | leaf=>rfl
  | step b T ih=>
    cases star with
    | zero=>rfl
    | succ star=>
      rw [expect_step hw φ b _ ho.2.2]
      change shiftedMean _ _ _ _ x=shiftedMean _ _ _ _ x
      congr 1
      funext y
      exact ih s star ho.2.2 (fun j=>q (j+1)) P y
  | fork T V ihT ihV=>
    cases star with
    | zero=>rfl
    | succ star=>
      cases s with
      | inl s=>
        rw [native_fork_expect_external_left]
        change (∑τ,V.weight w φ q τ x*
          nativeStarFieldTestMean w φ T s (star+1) q (fun _ σ=>P (σ,τ)) x)=_
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT s (star+1) ho q (fun σ=>P (σ,τ)) x
      | inr s=>
        rw [expect_fork]
        unfold expect
        change (∑σ,T.weight w φ q σ x*
          nativeStarFieldTestMean w φ V s (star+1) q (fun _ τ=>P (σ,τ)) x)=_
        apply Finset.sum_congr rfl
        intro σ _
        congr 1
        exact ihV s (star+1) ho q (fun τ=>P (σ,τ)) x

def nativeStarPairFactor (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (as : List PositiveMass) (star : ℕ) (q : ℕ → ι → ℝ≥0)
    (F : S → S → ℝ) (x : ι → ℝ) (u : S) : ℝ :=
  (single (S:=S) (as.drop star)).expect w φ (fun j=>q (star+j))
    (fun σ=>F u (singleEquiv (S:=S) (as.drop star) σ)) x

omit [Nonempty S] in
theorem nativeStarPairFactor_zero (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) (F : S → S → ℝ) (x : ι → ℝ) (u : S) :
    nativeStarPairFactor w φ as 0 q F x u=
      (single (S:=S) as).expect w φ q (fun σ=>F u (singleEquiv (S:=S) as σ)) x := by
  unfold nativeStarPairFactor
  rw [List.drop_zero]
  simp only [Nat.zero_add]

omit [Nonempty S] in
theorem nativeStarPairFactor_step (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (b : PositiveMass) (as : List PositiveMass) (star : ℕ) (q : ℕ → ι → ℝ≥0)
    (F : S → S → ℝ) (x : ι → ℝ) (u : S) :
    nativeStarPairFactor w φ (b::as) (star+1) q F x u=
      nativeStarPairFactor w φ as star (fun j=>q (j+1)) F x u := by
  unfold nativeStarPairFactor
  apply congrArg (fun z=>(single (S:=S) (as.drop star)).expect w φ z
    (fun σ=>F u (singleEquiv (S:=S) (as.drop star) σ)) x)
  funext j
  congr 1
  omega

variable {B : Type}

omit [Nonempty S] in
theorem native_expect_const_mul {as : List PositiveMass} (T : ClockTree S as)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (c : ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ=>c*P σ) x=c*T.expect w φ q P x := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

omit [Nonempty S] in
theorem native_star_field_test_fresh_zero_factor
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot) (c : ℝ)
    {w : S → ℝ} (_hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (_ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (J : (ι → ℝ) → T.cavityLeft.Assignment → ℝ)
    (F : S → S → ℝ) (x : ι → ℝ) :
    let g:=MarkedPlacement.fresh T c
    nativeStarFieldTestMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot (g.embed s)) 0 q
      (fun y σ=>J y (g.restRestrict σ)*
        F (T.cavityLeft.atSlot (g.restRestrict σ) (T.cavityLeftSlot s)) (g.restSpin σ)) x=
    T.cavityLeft.expect w φ q (fun σ=>J x σ*nativeStarPairFactor w φ as 0 q F x
      (T.cavityLeft.atSlot σ (T.cavityLeftSlot s))) x := by
  dsimp only
  rw [nativeStarFieldTestMean_zero]
  simp_rw [MarkedPlacement.restRestrict_fresh]
  change (T.cavityLeft.fork (single (S:=S×B) as).cavityLeft).expect w φ q
    (fun σ=>J x σ.1*F (T.cavityLeft.atSlot σ.1 (T.cavityLeftSlot s))
      ((single (S:=S×B) as).cavityLeft.atSlot σ.2
        ((single (S:=S×B) as).cavityLeftSlot (singleSlot as)))) x=_
  rw [expect_fork]
  apply congrArg (fun P=>T.cavityLeft.expect w φ q P x)
  funext σ
  change (single (S:=S×B) as).cavityLeft.expect w φ q
    (fun τ=>J x σ*F (T.cavityLeft.atSlot σ (T.cavityLeftSlot s))
      ((single (S:=S×B) as).cavityLeft.atSlot τ
        ((single (S:=S×B) as).cavityLeftSlot (singleSlot as)))) x=_
  rw [native_expect_const_mul]
  apply congrArg (fun y=>J x σ*y)
  rw [nativeStarPairFactor_zero]
  exact
    native_single_expect_atSlot_of_tree_eq (single (S:=S×B) as).cavityLeft
      (single_cavityLeft as) ((single (S:=S×B) as).cavityLeftSlot (singleSlot as))
      w φ q (F (T.cavityLeft.atSlot σ (T.cavityLeftSlot s))) x

omit [Nonempty S] in
theorem native_star_field_test_fresh_rest_factor
    {as : List PositiveMass} (T : ClockTree (S×B) as) (s : T.Slot)
    (star : ℕ) (hstar : star≤as.length) (aFresh : ℝ)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (J : (ι → ℝ) → T.cavityLeft.Assignment → ℝ)
    (F : S → S → ℝ) (x : ι → ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    nativeStarFieldTestMean w φ g.tree.cavityLeft (g.tree.cavityLeftSlot (g.embed s)) star q
      (fun y σ=>J y (g.restRestrict σ)*
        F (T.cavityLeft.atSlot (g.restRestrict σ) (T.cavityLeftSlot s)) (g.restSpin σ)) x=
    nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star q
      (fun y σ=>J y σ*nativeStarPairFactor w φ as star q F y
        (T.cavityLeft.atSlot σ (T.cavityLeftSlot s))) x := by
  induction T generalizing a aFresh star q x with
  | leaf=>
    have HS:star=0:=by simpa only [List.length_nil,Nat.le_zero] using hstar
    subst star
    exact native_star_field_test_fresh_zero_factor leaf s (aFresh-1) hw φ ho q J F x
  | @step b tail T ih=>
    cases star with
    | zero=>
      exact native_star_field_test_fresh_zero_factor (T.step b) s (aFresh-b.val) hw φ ho q J F x
    | succ star=>
      have HS:star≤tail.length:=by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hstar
      dsimp only [nativeFreshAtSlot]
      change shiftedMean _ _ _
        (nativeStarFieldTestMean w φ (nativeFreshAtSlot T b.val s star).tree.cavityLeft
          ((nativeFreshAtSlot T b.val s star).tree.cavityLeftSlot
            ((nativeFreshAtSlot T b.val s star).embed s)) star (fun j=>q (j+1))
          (fun y σ=>J y ((nativeFreshAtSlot T b.val s star).restRestrict σ)*
            F (T.cavityLeft.atSlot ((nativeFreshAtSlot T b.val s star).restRestrict σ)
              (T.cavityLeftSlot s)) ((nativeFreshAtSlot T b.val s star).restSpin σ))) x=
        shiftedMean _ _ _ (nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) star
          (fun j=>q (j+1)) (fun y σ=>J y σ*nativeStarPairFactor w φ (b::tail) (star+1) q F y
            (T.cavityLeft.atSlot σ (T.cavityLeftSlot s)))) x
      congr 1
      funext y
      simp_rw [nativeStarPairFactor_step]
      exact ih s star HS b.val ho.2.2 (fun j=>q (j+1)) J y
  | @fork tail T V ihT ihV=>
    cases star with
    | zero=>
      exact native_star_field_test_fresh_zero_factor (T.fork V) s (-aFresh) hw φ ho q J F x
    | succ star=>
      cases s with
      | inl s=>
        dsimp only [nativeFreshAtSlot]
        simp_rw [MarkedPlacement.restRestrict_left,MarkedPlacement.restSpin_left]
        change (∑τ,V.cavityLeft.weight w φ q τ x*
          nativeStarFieldTestMean w φ (nativeFreshAtSlot T aFresh s (star+1)).tree.cavityLeft
            ((nativeFreshAtSlot T aFresh s (star+1)).tree.cavityLeftSlot
              ((nativeFreshAtSlot T aFresh s (star+1)).embed s)) (star+1) q
            (fun y σ=>J y ((nativeFreshAtSlot T aFresh s (star+1)).restRestrict σ,τ)*
              F (T.cavityLeft.atSlot ((nativeFreshAtSlot T aFresh s (star+1)).restRestrict σ)
                (T.cavityLeftSlot s)) ((nativeFreshAtSlot T aFresh s (star+1)).restSpin σ)) x)=
          (∑τ,V.cavityLeft.weight w φ q τ x*
            nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot s) (star+1) q
              (fun y σ=>J y (σ,τ)*nativeStarPairFactor w φ tail (star+1) q F y
                (T.cavityLeft.atSlot σ (T.cavityLeftSlot s))) x)
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT s (star+1) hstar aFresh ho q (fun y σ=>J y (σ,τ)) x
      | inr s=>
        dsimp only [nativeFreshAtSlot]
        simp_rw [MarkedPlacement.restRestrict_right,MarkedPlacement.restSpin_right]
        change (∑τ,T.cavityLeft.weight w φ q τ x*
          nativeStarFieldTestMean w φ (nativeFreshAtSlot V aFresh s (star+1)).tree.cavityLeft
            ((nativeFreshAtSlot V aFresh s (star+1)).tree.cavityLeftSlot
              ((nativeFreshAtSlot V aFresh s (star+1)).embed s)) (star+1) q
            (fun y σ=>J y (τ,(nativeFreshAtSlot V aFresh s (star+1)).restRestrict σ)*
              F (V.cavityLeft.atSlot ((nativeFreshAtSlot V aFresh s (star+1)).restRestrict σ)
                (V.cavityLeftSlot s)) ((nativeFreshAtSlot V aFresh s (star+1)).restSpin σ)) x)=
          (∑τ,T.cavityLeft.weight w φ q τ x*
            nativeStarFieldTestMean w φ V.cavityLeft (V.cavityLeftSlot s) (star+1) q
              (fun y σ=>J y (τ,σ)*nativeStarPairFactor w φ tail (star+1) q F y
                (V.cavityLeft.atSlot σ (V.cavityLeftSlot s))) x)
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihV s (star+1) hstar aFresh ho q (fun y σ=>J y (τ,σ)) x

end OAI.SKFluctuations.Hierarchy.ClockTree
