module

public import CavityDiagonalHigherJets

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Hierarchy.ClockTree

variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
attribute [local instance] Classical.propDecidable

omit [Fintype S] [Nonempty S] in
theorem profilePairTest_add {as : List PositiveMass} {T : ClockTree S as}
    (P Q : T.Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    profilePairTest (fun σ => P σ + Q σ) K p r =
      fun σ => profilePairTest P K p r σ + profilePairTest Q K p r σ := by
  funext σ
  simp only [profilePairTest, add_mul]

omit [Nonempty S] [Nonempty ι] in
theorem disorderProfileJets_add (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    (P Q : T.Assignment → ℝ) :
    disorderProfileJets w φ v q x Ks T (fun σ => P σ + Q σ) =
      disorderProfileJets w φ v q x Ks T P +
        disorderProfileJets w φ v q x Ks T Q := by
  induction Ks generalizing T with
  | nil =>
    simp only [disorderProfileJets, disorderExpect, mul_add, Finset.sum_add_distrib]
  | cons K Ks ih =>
    simp only [disorderProfileJets, profilePairTest_add, ih, mul_add,
      List.sum_map_add, add_div]

theorem disorderProfileJets_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as) :
    disorderProfileJets w φ v q x Ks T (fun _ => 0) = 0 := by
  simpa only [zero_mul] using
    disorderProfileJets_const_mul w φ v q x Ks T (fun _ => 1) 0

theorem disorderProfileJets_finset_sum (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    {α : Type*} (A : Finset α) (P : α → T.Assignment → ℝ) :
    disorderProfileJets w φ v q x Ks T (fun σ => ∑ a ∈ A, P a σ) =
      ∑ a ∈ A, disorderProfileJets w φ v q x Ks T (P a) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, disorderProfileJets_zero]
  | @insert a A ha ih =>
    simp only [Finset.sum_insert ha, disorderProfileJets_add, ih]

theorem disorderProfileJets_deltaExpansion (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    (P : T.Assignment → ℝ) :
    disorderProfileJets w φ v q x Ks T P =
      ∑ σ, P σ * disorderProfileJets w φ v q x Ks T
        (fun τ => if τ = σ then 1 else 0) := by
  classical
  have he : P = fun τ => ∑ σ, P σ * (if τ = σ then 1 else 0 : ℝ) := by
    funext τ
    simp
  conv_lhs => rw [he]
  rw [disorderProfileJets_finset_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact disorderProfileJets_const_mul w φ v q x Ks T
    (fun τ => if τ = σ then 1 else 0) (P σ)

theorem native_profileJets_hasDerivAt_testFamily {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ)
    (q K : ℕ → ι → ℝ) {l r : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i + s * K j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i + s * K 0 i)
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    (P : ℝ → T.Assignment → ℝ) (P' : T.Assignment → ℝ) (x : ι → ℝ)
    {t : ℝ} (ht : t ∈ Ioo l r)
    (hP : ∀ σ, HasDerivAt (fun s => P s σ) (P' σ) t) :
    HasDerivAt
      (fun s => disorderProfileJets w φ v (fun j i => q j i + s * K j i)
        x Ks T (P s))
      (disorderProfileJets w φ v (fun j i => q j i + t * K j i) x Ks T P' +
        disorderProfileJets w φ v (fun j i => q j i + t * K j i) x
          (Ks ++ [ReplicaTree.coordinateProfile φ K]) T (P t)) t := by
  classical
  have hδ (σ : T.Assignment) := hasDerivAt_finiteProfileJets hw φ ho v q K hp hr
    Ks T (fun τ => if τ = σ then 1 else 0) x ht
  have hd := HasDerivAt.sum (u := Finset.univ) (fun σ _ => (hP σ).mul (hδ σ))
  have he (s : ℝ) := disorderProfileJets_deltaExpansion w φ v
    (fun j i => q j i + s * K j i) x Ks T (P s)
  have hfirst := disorderProfileJets_deltaExpansion w φ v
    (fun j i => q j i + t * K j i) x Ks T P'
  have hsecond := disorderProfileJets_deltaExpansion w φ v
    (fun j i => q j i + t * K j i) x
    (Ks ++ [ReplicaTree.coordinateProfile φ K]) T (P t)
  simp only [Finset.sum_add_distrib] at hd
  rw [← hfirst, ← hsecond] at hd
  convert hd using 1
  funext s
  simp only [Finset.sum_apply, Pi.mul_apply]
  exact he s

theorem native_profileJets_continuous_testFamily {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ)
    (q : ℝ → ℕ → ι → ℝ) (hq : ∀ j, Continuous (fun t => q t j))
    (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    (P : ℝ → T.Assignment → ℝ) (x : ℝ → ι → ℝ) (hx : Continuous x)
    (hP : ∀ σ, Continuous (fun t => P t σ)) :
    Continuous (fun t => disorderProfileJets w φ v (q t) (x t) Ks T (P t)) := by
  classical
  have hδ (σ : T.Assignment) := disorderProfileJets_continuous hw φ ho v q hq x hx
    Ks T (fun τ => if τ = σ then 1 else 0)
  have hd := continuous_finsetSum Finset.univ (fun σ _ => (hP σ).mul (hδ σ))
  have he (t : ℝ) := disorderProfileJets_deltaExpansion w φ v (q t) (x t) Ks T (P t)
  change Continuous (fun t => ∑ σ, P t σ * disorderProfileJets w φ v
    (q t) (x t) Ks T (fun τ => if τ = σ then 1 else 0)) at hd
  simpa only [← he] using hd

end OAI.SKFluctuations.Hierarchy.ClockTree
