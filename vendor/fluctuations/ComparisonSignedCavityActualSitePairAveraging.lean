module

public import ComparisonSignedCavityActualSitePermutationLaw
public import ComparisonSignedCavityGeneratedResources

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy Hierarchy.ClockTree

theorem orderedOverlap_nativeSitePerm {n : ℕ} (π : Fin n≃Fin n) (σ τ : Spin n) :
    orderedOverlap n (nativeSiteSpinPerm π σ) (nativeSiteSpinPerm π τ)=orderedOverlap n σ τ := by
  unfold orderedOverlap
  congr 1
  exact π.symm.sum_comp (fun i=>spinValue (σ i)*spinValue (τ i))

namespace Hierarchy.ClockTree
theorem nativeGeneratedEdgeProduct_sitePerm
    {n : ℕ} (π : Fin n≃Fin n) {as : List PositiveMass} (T : ClockTree (Spin n) as)
    (C : ℕ→ℝ) (es : List (T.Slot×T.Slot)) (σ : T.Assignment) :
    nativeGeneratedEdgeProduct T (orderedOverlap n) C es (T.assignmentGauge (nativeSiteSpinPerm π) σ)=
      nativeGeneratedEdgeProduct T (orderedOverlap n) C es σ := by
  unfold nativeGeneratedEdgeProduct
  simp only [atSlot_assignmentGauge,orderedOverlap_nativeSitePerm]

theorem NativeResourceTerm.full_overlap_value_sitePerm
    {n : ℕ} (π : Fin n≃Fin n) {as : List PositiveMass} {T : ClockTree (Spin n) as}
    {i star : ℕ} (P : NativeResourceTerm i star T)
    (b h C : ℕ→ℝ) (σ : T.Assignment) :
    P.value (uniformWeight n) (finiteFeature n) 0 (Cavity.physicalCompletedClock n b h)
      (orderedOverlap n) C 0 (T.assignmentGauge (nativeSiteSpinPerm π) σ)=
    P.value (uniformWeight n) (finiteFeature n) 0 (Cavity.physicalCompletedClock n b h)
      (orderedOverlap n) C 0 σ := by
  unfold NativeResourceTerm.value NativeGeneratedTest.value
  rw [nativeGeneratedEdgeProduct_sitePerm]

end Hierarchy.ClockTree
namespace Cavity

theorem native_actual_site_pair_eq_overlap
    {n : ℕ} (hn : 0 < n) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (P : T.Assignment→ℝ)
    (hP : ∀π : Fin n≃Fin n,∀σ,P (T.assignmentGauge (nativeSiteSpinPerm π) σ)=P σ)
    (a c : T.Slot) (i : Fin n) :
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h)
      (fun σ=>spinValue (T.atSlot σ a i)*spinValue (T.atSlot σ c i)*P σ) 0=
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h)
      (fun σ=>orderedOverlap n (T.atSlot σ a) (T.atSlot σ c)*P σ) 0 := by
  classical
  let F:=fun j : Fin n=>T.disorderExpect (uniformWeight n) (finiteFeature n) 0
    (physicalCompletedClock n b h)
    (fun σ=>spinValue (T.atSlot σ a j)*spinValue (T.atSlot σ c j)*P σ) 0
  have Hsame (j : Fin n) : F i=F j := by
    have H:=native_actual_site_permutation_law (Equiv.swap i j) T ho b h
      (fun σ=>spinValue (T.atSlot σ a i)*spinValue (T.atSlot σ c i)*P σ)
    have Hswap : (Equiv.swap i j).symm i=j:=by simp
    simp_rw [hP] at H
    simpa only [atSlot_assignmentGauge,nativeSiteSpinPerm,Equiv.coe_fn_mk,Hswap] using H
  have Havg : T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h)
      (fun σ=>orderedOverlap n (T.atSlot σ a) (T.atSlot σ c)*P σ) 0=
      (∑j,F j)/(n:ℝ) := by
    dsimp only [F,disorderExpect,orderedOverlap]
    simp only [Finset.sum_mul,mul_div_assoc,Finset.mul_sum,Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  have Hsum : (∑j,F j)=(n:ℝ)*F i := by
    simp only [←Hsame,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Havg,Hsum]
  have hN : (n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  change F i=(n:ℝ)*F i/(n:ℝ)
  field_simp

theorem native_actual_resource_site_pair_eq_overlap
    {n : ℕ} (hn : 0 < n) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    {i star : ℕ} (P : NativeResourceTerm i star T) (b h C : ℕ→ℝ)
    (a c : T.Slot) (j : Fin n) :
    let value:=P.value (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h)
      (orderedOverlap n) C 0
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h)
      (fun σ=>spinValue (T.atSlot σ a j)*spinValue (T.atSlot σ c j)*value σ) 0=
    T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h)
      (fun σ=>orderedOverlap n (T.atSlot σ a) (T.atSlot σ c)*value σ) 0 := by
  dsimp only
  exact native_actual_site_pair_eq_overlap hn T ho b h _
    (fun π σ=>P.full_overlap_value_sitePerm π b h C σ) a c j

end Cavity
end OAI.SKFluctuations
