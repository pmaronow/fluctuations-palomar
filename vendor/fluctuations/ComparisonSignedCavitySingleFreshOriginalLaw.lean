module

public import ComparisonSignedCavityTwoFreshOriginalLaw
public import ComparisonSignedCavityGeneratedResourcesForks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι]
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem native_single_fresh_expect_swap (as : List PositiveMass) (a : ℝ)
    (star : ℕ) (hstar : star ≤ as.length)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (A : S→S→ℝ) (x : ι→ℝ) :
    let T:=single (S:=S) as
    let g:=nativeFreshAtSlot T a (singleSlot as) star
    g.tree.expect w φ q (fun σ=>A (T.atSlot (g.restrict σ) (singleSlot as)) (g.spin σ)) x=
      g.tree.expect w φ q (fun σ=>A (g.spin σ) (T.atSlot (g.restrict σ) (singleSlot as))) x := by
  induction as generalizing a star q x with
  | nil=>
    have hz : star=0:=by simpa only [List.length_nil,Nat.le_zero] using hstar
    subst star
    dsimp only [single,nativeFreshAtSlot,MarkedPlacement.fresh]
    rw [expect_fork,expect_fork]
    exact native_expect_nested_commute leaf leaf w φ q A x
  | cons b as ih=>
    cases star with
    | zero=>
      dsimp only [single,nativeFreshAtSlot,MarkedPlacement.fresh]
      rw [expect_fork,expect_fork]
      simpa only [single,singleSlot,atSlot,singleEquiv,single_atSlot] using native_expect_nested_commute (single (S:=S) (b::as))
        (single (S:=S) (b::as)) w φ q
        (fun σ τ=>A (singleEquiv (S:=S) (b::as) σ) (singleEquiv (S:=S) (b::as) τ)) x
    | succ star=>
      dsimp only [single,nativeFreshAtSlot,MarkedPlacement.step]
      rw [expect_step hw φ b _ ho.2.2,expect_step hw φ b _ ho.2.2]
      congr 1
      funext y
      exact ih b.val star (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hstar)
        ho.2.2 (fun j=>q (j+1)) y

omit [Fintype S] [Nonempty S] in
theorem native_tree_eq_single_of_one_leaf {as : List PositiveMass} (T : ClockTree S as)
    (hT : T.leaves=1) : T=single as := by
  induction T with
  | leaf=>rfl
  | step b T ih=>exact congrArg (ClockTree.step b) (ih hT)
  | fork T R ihT ihR=>
    have HT:=T.leaves_pos
    have HR:=R.leaves_pos
    change T.leaves+R.leaves=1 at hT
    omega

theorem native_one_leaf_fresh_expect_swap {as : List PositiveMass} (T : ClockTree S as)
    (hT : T.leaves=1) (a : ℝ) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered a as) (q : ℕ→ι→ℝ≥0) (A : S→S→ℝ) (x : ι→ℝ) :
    let g:=nativeFreshAtSlot T a s star
    g.tree.expect w φ q (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) x=
      g.tree.expect w φ q (fun σ=>A (g.spin σ) (T.atSlot (g.restrict σ) s)) x := by
  obtain rfl:=native_tree_eq_single_of_one_leaf T hT
  rw [native_single_slot_eq as s]
  exact native_single_fresh_expect_swap as a star hstar hw φ ho q A x

end OAI.SKFluctuations.Hierarchy.ClockTree
