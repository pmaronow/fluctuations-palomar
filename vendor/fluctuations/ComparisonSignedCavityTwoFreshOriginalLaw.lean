module

public import ComparisonSignedCavityActualFreshSourceMarginals
public import ComparisonSignedCavityForestRootGrouping

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι]
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

omit [Nonempty S] in
theorem native_three_fork_tail_expect_swap {as : List PositiveMass} (T : ClockTree S as)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (Q : T.Assignment→(single (S:=S) as).Assignment→(single (S:=S) as).Assignment→ℝ)
    (x : ι→ℝ) :
    ((T.fork (single as)).fork (single as)).expect w φ q
      (fun σ=>Q σ.1.1 σ.1.2 σ.2) x=
    ((T.fork (single as)).fork (single as)).expect w φ q
      (fun σ=>Q σ.1.1 σ.2 σ.1.2) x := by
  simp only [expect_fork]
  congr 1
  funext σ
  exact native_expect_nested_commute (single as) (single as) w φ q (Q σ) x

omit [Nonempty S] in
theorem native_two_fresh_zero_expect_swap {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (q : ℕ→ι→ℝ≥0) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    let u:=nativeFreshAtSlot T a s 0
    let v:=nativeFreshAtSlot u.tree a u.mark 0
    v.tree.expect w φ q (fun σ=>Q (u.restrict (v.restrict σ)) (u.spin (v.restrict σ)) (v.spin σ)) x=
    v.tree.expect w φ q (fun σ=>Q (u.restrict (v.restrict σ)) (v.spin σ) (u.spin (v.restrict σ))) x := by
  cases T with
  | leaf=>
    simpa only [nativeFreshAtSlot,MarkedPlacement.fresh] using
      native_three_fork_tail_expect_swap leaf w φ q
        (fun σ τ υ=>Q σ ((singleEquiv (S:=S) []) τ) ((singleEquiv (S:=S) []) υ)) x
  | @step b tail T=>
    simpa only [nativeFreshAtSlot,MarkedPlacement.fresh] using
      native_three_fork_tail_expect_swap (T.step b) w φ q
      (fun σ τ υ=>Q σ ((singleEquiv (S:=S) (b::tail)) τ) ((singleEquiv (S:=S) (b::tail)) υ)) x
  | fork T V=>
    simpa only [nativeFreshAtSlot,MarkedPlacement.fresh] using
      native_three_fork_tail_expect_swap (T.fork V) w φ q
      (fun σ τ υ=>Q σ ((singleEquiv (S:=S) as) τ) ((singleEquiv (S:=S) as) υ)) x

theorem native_two_fresh_expect_swap {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    let u:=nativeFreshAtSlot T a s star
    let v:=nativeFreshAtSlot u.tree a u.mark star
    v.tree.expect w φ q (fun σ=>Q (u.restrict (v.restrict σ)) (u.spin (v.restrict σ)) (v.spin σ)) x=
    v.tree.expect w φ q (fun σ=>Q (u.restrict (v.restrict σ)) (v.spin σ) (u.spin (v.restrict σ))) x := by
  induction T generalizing a star q x with
  | leaf=>
    have H : star=0:=by simpa only [List.length_nil,Nat.le_zero] using hstar
    subst star
    exact native_two_fresh_zero_expect_swap leaf a s w φ q Q x
  | @step b tail T ih=>
    cases star with
    | zero=>exact native_two_fresh_zero_expect_swap (T.step b) a s w φ q Q x
    | succ star=>
      dsimp only [nativeFreshAtSlot,MarkedPlacement.step]
      rw [expect_step hw φ b _ ho.2.2,expect_step hw φ b _ ho.2.2]
      congr 1
      funext y
      exact ih b.val s star (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hstar)
        ho.2.2 (fun j=>q (j+1)) Q y
  | @fork tail T V ihT ihV=>
    cases star with
    | zero=>exact native_two_fresh_zero_expect_swap (T.fork V) a s w φ q Q x
    | succ star=>
      cases s with
      | inl s=>
        dsimp only [nativeFreshAtSlot,MarkedPlacement.left]
        rw [expect_fork,expect_fork]
        conv_lhs=>rw [native_expect_nested_commute]
        conv_rhs=>rw [native_expect_nested_commute]
        congr 1
        funext η
        exact ihT a s (star+1) hstar ho q (fun σ u v=>Q (σ,η) u v) x
      | inr s=>
        dsimp only [nativeFreshAtSlot,MarkedPlacement.right]
        rw [expect_fork,expect_fork]
        congr 1
        funext η
        exact ihV a s (star+1) hstar ho q (fun σ u v=>Q (η,σ) u v) x

theorem native_two_fresh_disorder_expect_swap {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered a as) (v₀ : ι→ℝ) (q : ℕ→ι→ℝ)
    (Q : T.Assignment→S→S→ℝ) (x : ι→ℝ) :
    let u:=nativeFreshAtSlot T a s star
    let v:=nativeFreshAtSlot u.tree a u.mark star
    v.tree.disorderExpect w φ v₀ q
      (fun σ=>Q (u.restrict (v.restrict σ)) (u.spin (v.restrict σ)) (v.spin σ)) x=
    v.tree.disorderExpect w φ v₀ q
      (fun σ=>Q (u.restrict (v.restrict σ)) (v.spin σ) (u.spin (v.restrict σ))) x := by
  dsimp only
  let u:=nativeFreshAtSlot T a s star
  let v:=nativeFreshAtSlot u.tree a u.mark star
  rw [v.tree.disorderExpect_integral hw φ ho,v.tree.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  apply integral_congr_ae
  exact Eventually.of_forall fun y=>native_two_fresh_expect_swap T a s star hstar hw φ ho _ Q (x+y)

end OAI.SKFluctuations.Hierarchy.ClockTree
