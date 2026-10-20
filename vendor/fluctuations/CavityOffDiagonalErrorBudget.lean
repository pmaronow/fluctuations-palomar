module

public import CavityDiagonalCancellation
public import CavitySplitDensity

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

private theorem actual_abs_expect_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    |T.disorderExpect w φ v q P x| ≤ T.disorderExpect w φ v q (fun σ => |P σ|) x := by
  unfold disorderExpect
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro σ _
  rw [abs_mul,abs_of_nonneg ((T.disorderWeight_probability hw φ ho v q x).1 σ)]

 theorem actual_profile_pair_abs_le_forkCost {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (P : T.Assignment → ℝ) {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C)
    (E : ℕ → S → S → ℝ) {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (E j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (hne : r.mark ≠ r.embed p.mark) :
    |r.tree.disorderExpect w φ v q (profilePairTest P E p r) x| ≤
      C*r.tree.forkCost D := by
  let j := r.tree.splitIndex (r.embed p.mark) r.mark
  have hpair := (pairClock as j).disorderExpect_abs_le_of_second_actual hw φ ho v q x
    (fun σ => E j (pairSpin as j σ).1 (pairSpin as j σ).2) (hD j) (hsecond j)
  have he : r.tree.disorderExpect w φ v q
      (fun σ => |E j (p.spin (r.restrict σ)) (r.spin σ)|) x ≤ D j := by
    simp only [p.spin_at,r.restrict_at,r.spin_at]
    rw [r.tree.disorderExpect_pairAtSlot_actual hw φ ho v q x
      (r.embed p.mark) r.mark (Ne.symm hne) (fun σ τ => |E j σ τ|)]
    exact hpair
  apply (actual_abs_expect_le hw φ r.tree ho v q _ x).trans
  have H : r.tree.disorderExpect w φ v q (fun σ => |profilePairTest P E p r σ|) x ≤
      C*r.tree.disorderExpect w φ v q
        (fun σ => |E j (p.spin (r.restrict σ)) (r.spin σ)|) x := by
    unfold disorderExpect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    have hw' := (r.tree.disorderWeight_probability hw φ ho v q x).1 σ
    have h := mul_le_mul_of_nonneg_right (hP (p.restrict (r.restrict σ)))
      (abs_nonneg (E j (p.spin (r.restrict σ)) (r.spin σ)))
    have hh := mul_le_mul_of_nonneg_left h hw'
    simpa only [profilePairTest,abs_mul,j,mul_assoc,mul_left_comm,mul_comm] using hh
  exact H.trans ((mul_le_mul_of_nonneg_left he hC).trans
    (mul_le_mul_of_nonneg_left (r.tree.split_le_forkCost hD _ _ (Ne.symm hne)) hC))

 theorem disorderProfileJets_oneError_offDiagonal_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C)
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
      exact (T.actual_profile_pair_abs_le_forkCost hw φ ho v q x P hC hP E hD
        hsecond p s hne).trans (mul_le_mul_of_nonneg_left
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
