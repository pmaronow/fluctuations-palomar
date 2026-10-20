module

public import ComparisonSignedCavityWholeLawProfileBudgets
public import CavityOffDiagonalErrorBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 6500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
 theorem actual_profile_pair_wholeLaw_L2_le_forkCost {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (P : T.Assignment → ℝ) {C : ℝ} (hC : 0 ≤ C) (hP : T.disorderExpect w φ v q (fun σ=>P σ^2) x ≤ C^2)
    (E : ℕ → S → S → ℝ) {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (E j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (hne : r.mark ≠ r.embed p.mark) :
    |r.tree.disorderExpect w φ v q (profilePairTest P E p r) x| ≤
      C*r.tree.forkCost D := by
  let j:=r.tree.splitIndex (r.embed p.mark) r.mark
  let Pn:=fun σ=>P (p.restrict (r.restrict σ))
  let R:=fun σ=>E j (p.spin (r.restrict σ)) (r.spin σ)
  have hPn : r.tree.disorderExpect w φ v q (fun σ=>Pn σ^2) x ≤ C^2 := by
    have HE:=wholeLaw_double_marked_nat_moment_eq hw φ T ho v q x P 2 p hp r hr
    simp only [sq_abs] at HE
    rw [show (fun σ=>Pn σ^2)=(fun σ=>P (p.restrict (r.restrict σ))^2) from rfl,HE]
    exact hP
  have hR : r.tree.disorderExpect w φ v q (fun σ=>R σ^2) x ≤ (D j)^2 := by
    dsimp only [R]
    simp only [p.spin_at,r.restrict_at,r.spin_at]
    rw [r.tree.disorderExpect_pairAtSlot_actual hw φ ho v q x (r.embed p.mark) r.mark
      (Ne.symm hne) (fun σ τ=>(E j σ τ)^2)]
    exact hsecond j
  have HC:=r.tree.disorderExpect_mul_sq_le hw φ ho v q Pn R x
  have HRn:=wholeLaw_disorderExpect_nonneg hw φ r.tree ho v q (fun σ=>R σ^2) (fun _=>sq_nonneg _) x
  have HH : (r.tree.disorderExpect w φ v q (fun σ=>Pn σ*R σ) x)^2 ≤ (C*D j)^2 := by
    calc
      _ ≤ _:=HC
      _ ≤ C^2*r.tree.disorderExpect w φ v q (fun σ=>R σ^2) x:=mul_le_mul_of_nonneg_right hPn HRn
      _ ≤ C^2*(D j)^2:=mul_le_mul_of_nonneg_left hR (sq_nonneg _)
      _ = _:=by ring
  have HH':|r.tree.disorderExpect w φ v q (profilePairTest P E p r) x| ≤ C*D j := by
    change |r.tree.disorderExpect w φ v q (fun σ=>Pn σ*R σ) x| ≤ C*D j
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (hD j))).mp (by simpa only [sq_abs] using HH)
  exact HH'.trans (mul_le_mul_of_nonneg_left (r.tree.split_le_forkCost hD _ _ (Ne.symm hne)) hC)

 theorem disorderProfileJets_oneError_offDiagonal_wholeLaw_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hP : T.disorderExpect w φ v q (fun σ=>P σ^2) x ≤ C^2)
    (E : ℕ → S → S → ℝ) {d : ℝ} (hdiag : ∀ σ, E as.length σ σ = d)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (E j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2) :
    |disorderProfileJets w φ v q x [E] T P| ≤
      pairForkVariation r*C*(T.forkCost D + (∫ u, edgeDensity 0 as D u)) := by
  classical
  rw [T.disorderProfileJets_one_eq_offDiagonal hw φ ho v q P hdiag x]
  have H := T.signedPair_abs_le_pairAbsSum
    (fun p s => (1-s.hit p.mark)*s.tree.disorderExpect w φ v q (profilePairTest P E p s) x)
  have HB : T.pairAbsSum (fun p s => |(1-s.hit p.mark)*
      s.tree.disorderExpect w φ v q (profilePairTest P E p s) x|) ≤
      C*T.pairAbsSum (fun _ s => s.tree.forkCost D+edgeBudget 0 as D) := by
    rw [←T.pairAbsSum_const_mul]
    apply T.pairAbsSum_mono
    intro p hp s hs
    by_cases hne : s.mark = s.embed p.mark
    · simp only [MarkedPlacement.hit,ite_eq_left hne,sub_self,zero_mul,abs_zero]
      exact mul_nonneg hC (add_nonneg (s.tree.forkCost_nonneg hD) (edgeBudget_nonneg ho hD))
    · simp only [MarkedPlacement.hit,ite_eq_right hne,sub_zero,one_mul]
      exact (T.actual_profile_pair_wholeLaw_L2_le_forkCost hw φ ho v q x P hC hP E hD
        hsecond p hp s hs hne).trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (edgeBudget_nonneg ho hD)) hC)
  have HG := T.pairAbsSum_forkBudget_le ho hT hD (d:=0) le_rfl
  simp only [add_zero] at HG
  have HF := (H.trans HB).trans (mul_le_mul_of_nonneg_left HG hC)
  rw [edgeDensity_integral ho D]
  unfold disorderOffDiagonalProfileJet
  simp only [mul_assoc] at HF ⊢
  change |_/2| ≤ _
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  have hn : 0 ≤ pairForkVariation r*C*(T.forkCost D+edgeBudget 0 as D) :=
    mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) hC)
      (add_nonneg (T.forkCost_nonneg hD) (edgeBudget_nonneg ho hD))
  have HF' := HF
  rw [mul_left_comm C] at HF'
  linarith

end OAI.SKFluctuations.Hierarchy.ClockTree
