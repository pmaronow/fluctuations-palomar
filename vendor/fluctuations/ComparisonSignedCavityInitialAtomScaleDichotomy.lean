module

public import ComparisonSignedCavityInitialActualAtomDichotomy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open scoped BigOperators
set_option maxHeartbeats 14000000

 def nativeInitialOrdinaryRowSet {I : Type} [Fintype I] (site : I→Bool) : Finset I :=
  Finset.univ.filter (fun e=>site e=false)

 theorem native_initial_radius_product_le {I : Type} [Fintype I]
    (site : I→Bool) (r : I→ℝ) {R : ℝ} (_hR : 0≤R)
    (hr : ∀e,0≤r e) (hsite : ∀e,site e=true→ r e=1)
    (hrow : ∀e,site e=false→ r e≤R) :
    (∏e,r e)≤R^(nativeInitialOrdinaryRowSet site).card := by
  classical
  have Hsplit:=Finset.prod_filter_mul_prod_filter_not (s:=Finset.univ) (f:=r)
    (fun e=>site e=false)
  have Hsite : (∏e∈Finset.univ.filter (fun e=>¬site e=false),r e)=1:=by
    apply Finset.prod_eq_one
    intro e he
    apply hsite e
    have Hnot:site e≠false:=(Finset.mem_filter.mp he).2
    cases H : site e
    · exact False.elim (Hnot H)
    · rfl
  rw [Hsite,mul_one] at Hsplit
  rw [←Hsplit]
  simpa only [nativeInitialOrdinaryRowSet,Finset.prod_const] using
    (Finset.prod_le_prod₀ (fun e _=>hr e) (fun e he=>hrow e (Finset.mem_filter.mp he).2))

 theorem native_initial_radius_product_one_small {I : Type} [Fintype I]
    (site : I→Bool) (r : I→ℝ) {R S : ℝ} (_hR : 0≤R) (hS : 0≤S)
    (hr : ∀e,0≤r e) (hsite : ∀e,site e=true→ r e=1)
    (hrow : ∀e,site e=false→ r e≤R) (e : I) (he : site e=false) (hsmall : r e≤S) :
    (∏j,r j)≤S*R^((nativeInitialOrdinaryRowSet site).card-1) := by
  classical
  let rows:=nativeInitialOrdinaryRowSet site
  have Hemem : e∈rows:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
  have Hsplit:=Finset.prod_filter_mul_prod_filter_not (s:=Finset.univ) (f:=r)
    (fun e=>site e=false)
  have Hsite : (∏e∈Finset.univ.filter (fun e=>¬site e=false),r e)=1:=by
    apply Finset.prod_eq_one
    intro e he
    apply hsite e
    have Hnot:site e≠false:=(Finset.mem_filter.mp he).2
    cases H : site e
    · exact False.elim (Hnot H)
    · rfl
  rw [Hsite,mul_one] at Hsplit
  have Hrest : (∏j∈rows.erase e,r j)≤R^(rows.card-1):=by
    have H:=Finset.prod_le_prod₀ (s:=rows.erase e) (fun j _=>hr j)
      (fun j hj=>hrow j (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2)
    simpa only [Finset.prod_const,Finset.card_erase_of_mem Hemem] using H
  rw [←Hsplit]
  change (∏j∈rows,r j)≤_
  rw [←Finset.mul_prod_erase rows r Hemem]
  exact mul_le_mul hsmall Hrest (Finset.prod_nonneg (fun j _=>hr j)) hS

end OAI.SKFluctuations.Cavity
