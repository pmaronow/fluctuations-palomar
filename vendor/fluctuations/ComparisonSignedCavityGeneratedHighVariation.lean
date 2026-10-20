module

public import ComparisonSignedCavityTransientForkCost

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass}

structure NativeHighSwitchState (S : Type*) (as : List PositiveMass) where
  tree : ClockTree S as
  target : tree.Slot

def NativeHighSwitchState.row (st : NativeHighSwitchState S as) (star : ℕ)
    (p : MarkedPlacement st.tree) : NativeHighSwitchState S as :=
  let g := nativeFreshAtSlot p.tree 0 (p.embed st.target) star
  ⟨g.tree,g.mark⟩

def nativeHighSwitchForkLedger (star U : ℕ)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (f : ℕ → ℝ) : ℕ → NativeHighSwitchState S as → ℝ
  | 0,st => st.tree.forkCost f
  | k+1,st => ((st.tree.markedAttach 0).map (fun p =>
      |p.coeff| *|Γ st p| *(if U ≤ p.tree.splitIndex (p.embed st.target) p.mark then
        nativeHighSwitchForkLedger star U Γ f k (st.row star p) else 0))).sum

def nativeHighSwitchForkVariation : ℕ → ℕ → ℝ
  | _,0 => 1
  | r,k+1 => (4*(r:ℝ)+1)*nativeHighSwitchForkVariation (r+2) k

theorem nativeHighSwitchForkVariation_nonneg (r k : ℕ) :
    0 ≤ nativeHighSwitchForkVariation r k := by
  induction k generalizing r with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (by positivity) (ih _)

theorem nativeHighSwitchForkLedger_le (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star<U)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀ st p,p∈st.tree.markedAttach 0 → |Γ st p| ≤ 1)
    (f : ℕ → ℝ) (hf : ∀ j,0 ≤ f j) (hlo : ∀ j,j<U → f j=0)
    (k : ℕ) (st : NativeHighSwitchState S as) {r : ℕ} (hr : st.tree.leaves≤r) :
    nativeHighSwitchForkLedger star U Γ f k st ≤
      nativeHighSwitchForkVariation r k*(st.tree.forkCost f+edgeBudget 0 as f) := by
  induction k generalizing st r with
  | zero =>
    simp only [nativeHighSwitchForkLedger,nativeHighSwitchForkVariation,one_mul]
    exact le_add_of_nonneg_right (edgeBudget_nonneg ho hf)
  | succ k ih =>
    let C := nativeHighSwitchForkVariation (r+2) k
    have hC : 0 ≤ C := nativeHighSwitchForkVariation_nonneg _ _
    have hB : 0 ≤ edgeBudget 0 as f := edgeBudget_nonneg ho hf
    have hF := st.tree.forkCost_nonneg hf
    have hrow (p : MarkedPlacement st.tree) (hp : p∈st.tree.markedAttach 0) :
        |Γ st p| *(if U ≤ p.tree.splitIndex (p.embed st.target) p.mark then
          nativeHighSwitchForkLedger star U Γ f k (st.row star p) else 0) ≤
          C*(p.tree.forkCost f+edgeBudget 0 as f) := by
      have hcost : (st.row star p).tree.forkCost f=p.tree.forkCost f :=
        nativeFreshAtSlot_high_forkCost p.tree 0 (p.embed st.target) hs f hlo
      have hleaves : (st.row star p).tree.leaves≤r+2 := by
        have h1 := st.tree.markedAttach_leaves 0 p hp
        have h2 := p.tree.markedAttach_leaves 0
          (nativeFreshAtSlot p.tree 0 (p.embed st.target) star)
          (nativeFreshAtSlot_mem p.tree 0 (p.embed st.target) star)
        change (nativeFreshAtSlot p.tree 0 (p.embed st.target) star).tree.leaves≤r+2
        omega
      have H := ih (st.row star p) hleaves
      rw [hcost] at H
      have hbudget : 0 ≤ C*(p.tree.forkCost f+edgeBudget 0 as f) :=
        mul_nonneg hC (add_nonneg (p.tree.forkCost_nonneg hf) hB)
      split_ifs
      · exact (mul_le_mul_of_nonneg_left H (abs_nonneg _)).trans
          (mul_le_of_le_one_left hbudget (hΓ st p hp))
      · simpa only [mul_zero] using hbudget
    have H1 : nativeHighSwitchForkLedger star U Γ f (k+1) st ≤
        ((st.tree.markedAttach 0).map (fun p => |p.coeff| *
          (C*(p.tree.forkCost f+edgeBudget 0 as f)))).sum := by
      unfold nativeHighSwitchForkLedger
      apply List.sum_le_sum
      intro p hp
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hrow p hp) (abs_nonneg p.coeff)
    have H2 : ((st.tree.markedAttach 0).map (fun p => |p.coeff| *
          (C*(p.tree.forkCost f+edgeBudget 0 as f)))).sum =
        C*(((st.tree.markedAttach 0).map (fun p => |p.coeff| *p.tree.forkCost f)).sum +
          (2*(st.tree.leaves:ℝ))*edgeBudget 0 as f) := by
      simp only [mul_left_comm _ C,List.sum_map_mul_left,mul_add,List.sum_map_add,
        List.sum_map_mul_right,st.tree.markedAttach_variation ho,sub_zero]
    have H3 : ((st.tree.markedAttach 0).map (fun p => |p.coeff| *p.tree.forkCost f)).sum +
        (2*(st.tree.leaves:ℝ))*edgeBudget 0 as f ≤
        (4*(r:ℝ)+1)*(st.tree.forkCost f+edgeBudget 0 as f) := by
      have H := st.tree.markedAttach_forkCost_le ho hf
      have hcast : (st.tree.leaves:ℝ)≤r := by exact_mod_cast hr
      have hp : (0:ℝ) ≤ st.tree.leaves := Nat.cast_nonneg _
      nlinarith
    exact H1.trans (H2.le.trans (by
      change C*_ ≤ nativeHighSwitchForkVariation r (k+1)*_
      rw [nativeHighSwitchForkVariation]
      nlinarith [mul_le_mul_of_nonneg_left H3 hC]))

theorem nativeHighSwitchForkLedger_le_edgeBudget (ho : MassOrdered 0 as)
    (star U : ℕ) (hs : star<U)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀ st p,p∈st.tree.markedAttach 0 → |Γ st p| ≤ 1)
    (f : ℕ → ℝ) (hf : ∀ j,0 ≤ f j) (hlo : ∀ j,j<U → f j=0)
    (k : ℕ) (st : NativeHighSwitchState S as) (hsource : st.tree.forkCost f=0) :
    nativeHighSwitchForkLedger star U Γ f k st ≤
      nativeHighSwitchForkVariation st.tree.leaves k*edgeBudget 0 as f := by
  simpa only [hsource,zero_add] using nativeHighSwitchForkLedger_le ho star U hs Γ hΓ
    f hf hlo k st (le_refl _)

end OAI.SKFluctuations.Hierarchy.ClockTree
