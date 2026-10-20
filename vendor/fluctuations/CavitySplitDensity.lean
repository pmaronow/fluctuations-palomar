module

public import CavityAttachedTree

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem ClockTree.disorderExpect_abs_le_of_second_actual {w : S → ℝ}
    (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) (P : T.Assignment → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hsecond : T.disorderExpect w φ v q (fun σ => (P σ)^2) x ≤ D^2) :
    T.disorderExpect w φ v q (fun σ => |P σ|) x ≤ D := by
  have h := T.disorderExpect_mul_sq_le hw φ ho v q (fun σ => |P σ|) (fun _ => 1) x
  simp only [mul_one,one_pow,sq_abs,T.disorderExpect_one hw φ ho] at h
  have hn : 0 ≤ T.disorderExpect w φ v q (fun σ => |P σ|) x := by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q x).1 σ) (abs_nonneg _)
  nlinarith

theorem ClockTree.disorderProfileJets_oneError_actual_L2 {w : S → ℝ}
    (hw : ∀ s, 0 < w s) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as)
    (pre post : List (ℕ → S → S → ℝ)) (E : ℕ → S → S → ℝ)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) {C M d : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hP : ∀ σ, |P σ| ≤ C)
    (hpre : ∀ K ∈ pre, ∀ j σ τ, |K j σ τ| ≤ M)
    (hpost : ∀ K ∈ post, ∀ j σ τ, |K j σ τ| ≤ M)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j) (hd : 0 ≤ d)
    (hdiag : ∀ σ, |E as.length σ σ| ≤ d)
    (hsecond : ∀ j, (ClockTree.pairClock as j).disorderExpect w φ v q
      (fun σ => (E j (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)^2) x ≤ (D j)^2) :
    |ClockTree.disorderProfileJets w φ v q x (pre++E::post) T P| ≤
      ClockTree.errorJetVariation r pre.length post.length*C*M^(pre.length+post.length)*
        (T.forkCost D + (∫ u, ClockTree.edgeDensity 0 as D u) + d) := by
  let e := finiteJetEquiv ι
  have he (j : ℕ) : ClockTree.pairRootMean w (reindexFeature e φ) as
      (fun i => q 0 (e i)-v (e i)) (fun j i => q (j+1) (e i)-q j (e i)) j
      (fun σ τ => |E j σ τ|) ((coordinateEquiv e).symm x) ≤ D j := by
    rw [ClockTree.pairRootMean_eq_rootExpect hw (reindexFeature e φ) as ho,
      (ClockTree.pairClock as j).rootExpect_eq_disorderExpect hw (reindexFeature e φ) ho _
        (fun i => v (e i)) (fun j i => q j (e i)),
      (ClockTree.pairClock as j).disorderExpect_reindex e w φ v q,
      ContinuousLinearEquiv.apply_symm_apply]
    exact (ClockTree.pairClock as j).disorderExpect_abs_le_of_second_actual hw φ ho v q x
      (fun σ => E j (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) (hD j) (hsecond j)
  have H := ClockTree.rootProfileJets_oneError_abs_le hw (reindexFeature e φ) ho pre post E T hT P
    hC hM hP hpre hpost (fun i => q 0 (e i)-v (e i))
    (fun j i => q (j+1) (e i)-q j (e i)) hD hd hdiag ((coordinateEquiv e).symm x) he
  rw [T.rootProfileJets_eq_disorderProfileJets hw (reindexFeature e φ) ho (pre++E::post) P
    (fun i => v (e i)) (fun j i => q j (e i)),
    T.disorderProfileJets_reindex e w φ (pre++E::post) P v q,
    ContinuousLinearEquiv.apply_symm_apply,
    ← ClockTree.edgeDensity_integral ho D] at H
  exact H

end OAI.SKFluctuations.Hierarchy
