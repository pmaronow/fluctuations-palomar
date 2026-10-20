module

public import CavityTreeMoments
public import SKFluctuationsOAI.Probability.SKFluctuations.ClockPairRepresentation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
open GaussianCalculus
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem ClockTree.disorderExpect_pairAtSlot_actual {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (s t : T.Slot) (hst : s ≠ t) (P : S → S → ℝ) :
    T.disorderExpect w φ v q (fun σ => P (T.atSlot σ s) (T.atSlot σ t)) x =
      (ClockTree.pairClock as (T.splitIndex s t)).disorderExpect w φ v q
        (fun σ => P (ClockTree.pairSpin as (T.splitIndex s t) σ).1
          (ClockTree.pairSpin as (T.splitIndex s t) σ).2) x := by
  let e := finiteJetEquiv ι
  let z := (coordinateEquiv e).symm x
  have H := T.rootExpect_pairAtSlot hw (reindexFeature e φ) ho
    (fun i => q 0 (e i)-v (e i)) (fun j i => q (j+1) (e i)-q j (e i))
    s t hst P z
  rw [ClockTree.pairRootMean_eq_rootExpect hw (reindexFeature e φ) as ho] at H
  rw [T.rootExpect_eq_disorderExpect hw (reindexFeature e φ) ho _
      (fun i => v (e i)) (fun j i => q j (e i)),
    (ClockTree.pairClock as (T.splitIndex s t)).rootExpect_eq_disorderExpect
      hw (reindexFeature e φ) ho _ (fun i => v (e i)) (fun j i => q j (e i)),
    T.disorderExpect_reindex e w φ v q,
    (ClockTree.pairClock as (T.splitIndex s t)).disorderExpect_reindex e w φ v q,
    ContinuousLinearEquiv.apply_symm_apply] at H
  exact H

theorem ClockTree.disorderExpect_pair_product_actual {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    {k : ℕ} (hk : 0 < k) (s t : Fin k → T.Slot) (hst : ∀ i, s i ≠ t i)
    (P : T.Assignment → ℝ) (E : Fin k → S → S → ℝ)
    {C rho : ℝ} (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C)
    (he : ∀ i, (ClockTree.pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ => |E i (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (ClockTree.pairSpin as (T.splitIndex (s i) (t i)) σ).2|^k) x ≤ rho^k) :
    |T.disorderExpect w φ v q (fun σ => P σ*
      (∏ i, E i (T.atSlot σ (s i)) (T.atSlot σ (t i)))) x| ≤ C*rho^k := by
  apply T.disorderExpect_product_abs_le hw φ ho v q hk P
    (fun i σ => E i (T.atSlot σ (s i)) (T.atSlot σ (t i))) hC hP x
  intro i
  rw [T.disorderExpect_pairAtSlot_actual hw φ ho v q x (s i) (t i) (hst i)
    (fun a b => |E i a b|^k)]
  exact he i

end OAI.SKFluctuations.Hierarchy
