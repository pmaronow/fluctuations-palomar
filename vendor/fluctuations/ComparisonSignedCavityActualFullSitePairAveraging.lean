module

public import ComparisonSignedCavityActualFullSitePermutationLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem nativeFullSiteSpinPerm_join {n : ℕ} (π : Fin (n+1)≃Fin (n+1)) (σ : Spin n×Bool) :
    joinSpin (nativeFullSiteSpinPerm π σ)=nativeSiteSpinPerm π (joinSpin σ) := by
  exact (spinEquiv n).apply_symm_apply _

theorem full_orderedOverlap_nativeSitePerm {n : ℕ}
    (π : Fin (n+1)≃Fin (n+1)) (σ τ : Spin n×Bool) :
    orderedOverlap (n+1) (joinSpin (nativeFullSiteSpinPerm π σ))
      (joinSpin (nativeFullSiteSpinPerm π τ))=
      orderedOverlap (n+1) (joinSpin σ) (joinSpin τ) := by
  rw [nativeFullSiteSpinPerm_join,nativeFullSiteSpinPerm_join,orderedOverlap_nativeSitePerm]

theorem native_actual_full_site_pair_eq_overlap
    {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (b h K : ℕ→ℝ) (P : T.Assignment→ℝ)
    (hP : ∀π : Fin (n+1)≃Fin (n+1),∀σ,P (T.assignmentGauge (nativeFullSiteSpinPerm π) σ)=P σ)
    (a c : T.Slot) (i : Fin (n+1)) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>spinValue (joinSpin (T.atSlot σ a) i)*spinValue (joinSpin (T.atSlot σ c) i)*P σ) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ a)) (joinSpin (T.atSlot σ c))*P σ) 0 := by
  classical
  let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
  let F:=fun j : Fin (n+1)=>T.disorderExpect (fullWeight n) (fullFeature n) 0 q
    (fun σ=>spinValue (joinSpin (T.atSlot σ a) j)*spinValue (joinSpin (T.atSlot σ c) j)*P σ) 0
  have Hsame (j : Fin (n+1)) : F i=F j := by
    have H:=native_actual_full_site_permutation_law (Equiv.swap i j) T ho U b h K
      (fun σ=>spinValue (joinSpin (T.atSlot σ a) i)*spinValue (joinSpin (T.atSlot σ c) i)*P σ)
    have Hswap : (Equiv.swap i j).symm i=j:=by simp
    simp_rw [hP] at H
    simpa only [atSlot_assignmentGauge,nativeFullSiteSpinPerm_join,nativeSiteSpinPerm,
      Equiv.coe_fn_mk,Hswap] using H
  have Havg : T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ a)) (joinSpin (T.atSlot σ c))*P σ) 0=
      (∑j,F j)/((n+1:ℕ):ℝ) := by
    dsimp only [F,disorderExpect,orderedOverlap]
    simp only [Finset.sum_mul,mul_div_assoc,Finset.mul_sum,Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  have Hsum : (∑j,F j)=((n+1:ℕ):ℝ)*F i := by
    simp only [←Hsame,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Havg,Hsum]
  change F i=((n+1:ℕ):ℝ)*F i/((n+1:ℕ):ℝ)
  field_simp

theorem native_actual_full_resource_site_pair_eq_overlap
    {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    {i star : ℕ} (P : NativeResourceTerm i star T) (U : ℕ) (b h K C : ℕ→ℝ)
    (a c : T.Slot) :
    let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
    let value:=P.value (fullWeight n) (fullFeature n) 0 q
      (fun σ τ=>orderedOverlap (n+1) (joinSpin σ) (joinSpin τ)) C 0
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>spinValue (T.atSlot σ a).2*spinValue (T.atSlot σ c).2*value σ) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ a)) (joinSpin (T.atSlot σ c))*value σ) 0 := by
  dsimp only
  have HI (π : Fin (n+1)≃Fin (n+1)) (σ : T.Assignment) :
      P.value (fullWeight n) (fullFeature n) 0
        (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
        (fun σ τ=>orderedOverlap (n+1) (joinSpin σ) (joinSpin τ)) C 0
        (T.assignmentGauge (nativeFullSiteSpinPerm π) σ)=
      P.value (fullWeight n) (fullFeature n) 0
        (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
        (fun σ τ=>orderedOverlap (n+1) (joinSpin σ) (joinSpin τ)) C 0 σ := by
    unfold NativeResourceTerm.value NativeGeneratedTest.value nativeGeneratedEdgeProduct
    simp only [atSlot_assignmentGauge,full_orderedOverlap_nativeSitePerm]
  simpa only [joinSpin_last] using native_actual_full_site_pair_eq_overlap
    T ho U b h K _ HI a c (Fin.last n)

end OAI.SKFluctuations.Cavity
