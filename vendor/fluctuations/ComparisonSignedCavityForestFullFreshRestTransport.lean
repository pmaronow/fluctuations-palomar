module

public import ComparisonSignedCavityForestObservedSameFreshLaw
public import CavityRestMarkedPlacement

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass}

namespace MarkedPlacement

theorem restRestrict_fresh (T : ClockTree (S×B) as) (c : ℝ)
    (σ : (fresh T c).tree.cavityLeft.Assignment) :
    (fresh T c).restRestrict σ=σ.1 := by
  apply T.cavityLeft.assignment_ext
  intro s
  obtain ⟨s,rfl⟩:=T.cavityLeftSlot.surjective s
  rw [restRestrict_at]
  rfl

theorem restRestrict_step (b : PositiveMass) {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (σ : (p.step b).tree.cavityLeft.Assignment) :
    (p.step b).restRestrict σ=p.restRestrict σ := rfl

theorem restSpin_step (b : PositiveMass) {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (σ : (p.step b).tree.cavityLeft.Assignment) :
    (p.step b).restSpin σ=p.restSpin σ := rfl

theorem restRestrict_left {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (V : ClockTree (S×B) as)
    (σ : (p.left V).tree.cavityLeft.Assignment) :
    (p.left V).restRestrict σ=(p.restRestrict σ.1,σ.2) := by
  apply (T.fork V).cavityLeft.assignment_ext
  intro s
  cases s with
  | inl s=>
    obtain ⟨s,rfl⟩:=T.cavityLeftSlot.surjective s
    exact ((p.left V).restRestrict_at σ (Sum.inl s)).trans (p.restRestrict_at σ.1 s).symm
  | inr s=>
    obtain ⟨s,rfl⟩:=V.cavityLeftSlot.surjective s
    exact (p.left V).restRestrict_at σ (Sum.inr s)

theorem restSpin_left {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (V : ClockTree (S×B) as)
    (σ : (p.left V).tree.cavityLeft.Assignment) :
    (p.left V).restSpin σ=p.restSpin σ.1 := rfl

theorem restRestrict_right (T : ClockTree (S×B) as) {V : ClockTree (S×B) as}
    (p : MarkedPlacement V) (σ : (p.right T).tree.cavityLeft.Assignment) :
    (p.right T).restRestrict σ=(σ.1,p.restRestrict σ.2) := by
  apply (T.fork V).cavityLeft.assignment_ext
  intro s
  cases s with
  | inl s=>
    obtain ⟨s,rfl⟩:=T.cavityLeftSlot.surjective s
    exact (p.right T).restRestrict_at σ (Sum.inl s)
  | inr s=>
    obtain ⟨s,rfl⟩:=V.cavityLeftSlot.surjective s
    exact ((p.right T).restRestrict_at σ (Sum.inr s)).trans (p.restRestrict_at σ.2 s).symm

theorem restSpin_right (T : ClockTree (S×B) as) {V : ClockTree (S×B) as}
    (p : MarkedPlacement V) (σ : (p.right T).tree.cavityLeft.Assignment) :
    (p.right T).restSpin σ=p.restSpin σ.2 := rfl

end MarkedPlacement

variable {ι : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem native_single_expect_atSlot_of_tree_eq
    (T : ClockTree S as) (hT : T=single (S:=S) as) (s : T.Slot)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (q : ℕ → ι → ℝ≥0)
    (Q : S → ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ=>Q (T.atSlot σ s)) x=
      (single (S:=S) as).expect w φ q (fun σ=>Q (singleEquiv (S:=S) as σ)) x := by
  subst T
  rw [native_single_slot_eq as s]
  simp only [single_atSlot]

omit [Nonempty S] in
theorem native_fresh_full_rest_expect_transport
    (T : ClockTree (S×B) as) (c : ℝ)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (q : ℕ → ι → ℝ≥0)
    (Q : T.cavityLeft.Assignment → S → ℝ) (x : ι → ℝ) :
    (MarkedPlacement.fresh T c).tree.cavityLeft.expect w φ q
      (fun σ=>Q ((MarkedPlacement.fresh T c).restRestrict σ)
        ((MarkedPlacement.fresh T c).restSpin σ)) x=
      (MarkedPlacement.fresh T.cavityLeft c).tree.expect w φ q
        (fun σ=>Q ((MarkedPlacement.fresh T.cavityLeft c).restrict σ)
          ((MarkedPlacement.fresh T.cavityLeft c).spin σ)) x := by
  simp_rw [MarkedPlacement.restRestrict_fresh]
  change (T.cavityLeft.fork (single (S:=S×B) as).cavityLeft).expect w φ q
    (fun σ=>Q σ.1 ((single (S:=S×B) as).cavityLeft.atSlot σ.2
      ((single (S:=S×B) as).cavityLeftSlot (singleSlot as)))) x=
    (T.cavityLeft.fork (single (S:=S) as)).expect w φ q
      (fun σ=>Q σ.1 (singleEquiv (S:=S) as σ.2)) x
  rw [expect_fork,expect_fork]
  apply congrArg (fun F=>T.cavityLeft.expect w φ q F x)
  funext σ
  exact native_single_expect_atSlot_of_tree_eq (single (S:=S×B) as).cavityLeft
    (single_cavityLeft as) ((single (S:=S×B) as).cavityLeftSlot (singleSlot as))
    w φ q (Q σ) x

theorem nativeFreshAtSlot_full_rest_expect_transport
    (T : ClockTree (S×B) as) (a : ℝ) (s : T.Slot) (j : ℕ)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (q : ℕ → ι → ℝ≥0)
    (Q : T.cavityLeft.Assignment → S → ℝ) (x : ι → ℝ) :
    let p:=nativeFreshAtSlot T a s j
    let r:=nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot s) j
    p.tree.cavityLeft.expect w φ q (fun σ=>Q (p.restRestrict σ) (p.restSpin σ)) x=
      r.tree.expect w φ q (fun σ=>Q (r.restrict σ) (r.spin σ)) x := by
  induction T generalizing a a₀ j q x with
  | leaf=>exact native_fresh_full_rest_expect_transport .leaf (a-1) w φ q Q x
  | step b T ih=>
    cases j with
    | zero=>exact native_fresh_full_rest_expect_transport (T.step b) (a-b.val) w φ q Q x
    | succ j=>
      change ((nativeFreshAtSlot T b.val s j).tree.cavityLeft.step b).expect w φ q
        (fun σ=>Q ((nativeFreshAtSlot T b.val s j).restRestrict σ)
          ((nativeFreshAtSlot T b.val s j).restSpin σ)) x=
        ((nativeFreshAtSlot T.cavityLeft b.val (T.cavityLeftSlot s) j).tree.step b).expect w φ q
          (fun σ=>Q ((nativeFreshAtSlot T.cavityLeft b.val (T.cavityLeftSlot s) j).restrict σ)
            ((nativeFreshAtSlot T.cavityLeft b.val (T.cavityLeftSlot s) j).spin σ)) x
      rw [expect_step hw φ b _ ho.2.2,expect_step hw φ b _ ho.2.2]
      congr 1
      funext y
      exact ih b.val s j ho.2.2 (fun k=>q (k+1)) Q y
  | fork T V ihT ihV=>
    cases j with
    | zero=>exact native_fresh_full_rest_expect_transport (T.fork V) (-a) w φ q Q x
    | succ j=>cases s with
      | inl s=>
        change (MarkedPlacement.left V (nativeFreshAtSlot T a s (j+1))).tree.cavityLeft.expect w φ q
          (fun σ=>Q ((MarkedPlacement.left V (nativeFreshAtSlot T a s (j+1))).restRestrict σ)
            ((MarkedPlacement.left V (nativeFreshAtSlot T a s (j+1))).restSpin σ)) x=
          ((nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot s) (j+1)).tree.fork V.cavityLeft).expect w φ q
            (fun σ=>Q ((nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot s) (j+1)).restrict σ.1,σ.2)
              ((nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot s) (j+1)).spin σ.1)) x
        simp_rw [MarkedPlacement.restRestrict_left,MarkedPlacement.restSpin_left]
        change ((nativeFreshAtSlot T a s (j+1)).tree.cavityLeft.fork V.cavityLeft).expect w φ q
          (fun σ=>Q ((nativeFreshAtSlot T a s (j+1)).restRestrict σ.1,σ.2)
            ((nativeFreshAtSlot T a s (j+1)).restSpin σ.1)) x=_
        rw [native_fork_expect_external_left,native_fork_expect_external_left]
        apply Finset.sum_congr rfl
        intro τ _
        congr 1
        exact ihT a s (j+1) ho q (fun σ d=>Q (σ,τ) d) x
      | inr s=>
        change (MarkedPlacement.right T (nativeFreshAtSlot V a s (j+1))).tree.cavityLeft.expect w φ q
          (fun σ=>Q ((MarkedPlacement.right T (nativeFreshAtSlot V a s (j+1))).restRestrict σ)
            ((MarkedPlacement.right T (nativeFreshAtSlot V a s (j+1))).restSpin σ)) x=
          (T.cavityLeft.fork (nativeFreshAtSlot V.cavityLeft a (V.cavityLeftSlot s) (j+1)).tree).expect w φ q
            (fun σ : T.cavityLeft.Assignment ×
                (nativeFreshAtSlot V.cavityLeft a (V.cavityLeftSlot s) (j+1)).tree.Assignment=>
              Q (σ.1,(nativeFreshAtSlot V.cavityLeft a (V.cavityLeftSlot s) (j+1)).restrict σ.2)
              ((nativeFreshAtSlot V.cavityLeft a (V.cavityLeftSlot s) (j+1)).spin σ.2)) x
        simp_rw [MarkedPlacement.restRestrict_right,MarkedPlacement.restSpin_right]
        change (T.cavityLeft.fork (nativeFreshAtSlot V a s (j+1)).tree.cavityLeft).expect w φ q
          (fun σ : T.cavityLeft.Assignment × (nativeFreshAtSlot V a s (j+1)).tree.cavityLeft.Assignment=>
            Q (σ.1,(nativeFreshAtSlot V a s (j+1)).restRestrict σ.2)
            ((nativeFreshAtSlot V a s (j+1)).restSpin σ.2)) x=_
        rw [expect_fork,expect_fork]
        unfold expect
        apply Finset.sum_congr rfl
        intro σ _
        congr 1
        exact ihV a s (j+1) ho q (fun τ d=>Q (σ,τ) d) x

theorem nativeFreshAtSlot_full_rest_disorder_transport
    (T : ClockTree (S×B) as) (a : ℝ) (s : T.Slot) (j : ℕ)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (Q : T.cavityLeft.Assignment → S → ℝ) (x : ι → ℝ) :
    let p:=nativeFreshAtSlot T a s j
    let r:=nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot s) j
    p.tree.cavityLeft.disorderExpect w φ v q (fun σ=>Q (p.restRestrict σ) (p.restSpin σ)) x=
      r.tree.disorderExpect w φ v q (fun σ=>Q (r.restrict σ) (r.spin σ)) x := by
  dsimp only
  rw [(nativeFreshAtSlot T a s j).tree.cavityLeft.disorderExpect_integral hw φ ho,
    (nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot s) j).tree.disorderExpect_integral hw φ ho]
  unfold zeroContinuation
  apply integral_congr_ae
  exact Eventually.of_forall (fun y=>nativeFreshAtSlot_full_rest_expect_transport T a s j hw φ ho _ Q (x+y))

end OAI.SKFluctuations.Hierarchy.ClockTree
