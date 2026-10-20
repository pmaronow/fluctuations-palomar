module

public import ComparisonSignedCavityActualFrozenSiteRestoration
public import ComparisonSignedCavityActualFrozenResourceMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

def nativeResourceOmissionShape {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceMonomial i star T)
    (hi : i ≤ star) (hstar : star < as.length) (C : ℕ→ℝ) :
    ActualNaturalBoundaryShape n P.factors.length T where
  α:=fun e=>-C (T.splitIndex (P.factors.get e).2.1 (P.factors.get e).2.2)
  β:=fun _=>1
  i:=fun e=>(P.factors.get e).2.2
  j:=fun e=>(P.factors.get e).2.1
  distinct:=fun e=>Ne.symm (P.factor_endpoints_distinct hi hstar e)
  lowInGrid:=fun _e=>T.splitIndex_le_clockLength _ _

theorem native_resource_omission_shape_deleted_factor {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceMonomial i star T)
    (hi : i ≤ star) (hstar : star < as.length) (C : ℕ→ℝ)
    (e : Fin P.factors.length) (σ : T.Assignment) :
    (nativeResourceOmissionShape P hi hstar C).deletedFactor e σ=
      deletedOverlap n (joinSpin (T.atSlot σ (P.factors.get e).2.1))
        (joinSpin (T.atSlot σ (P.factors.get e).2.2))-
          C (T.splitIndex (P.factors.get e).2.1 (P.factors.get e).2.2) := by
  unfold nativeResourceOmissionShape ActualNaturalBoundaryShape.deletedFactor fullBoundaryAffineFactor
  ring

theorem native_resource_omission_shape_product {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceMonomial i star T)
    (hi : i ≤ star) (hstar : star < as.length) (C : ℕ→ℝ) (σ : T.Assignment) :
    (nativeResourceOmissionShape P hi hstar C).product σ=
      P.test.value (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C σ := by
  rw [ActualNaturalBoundaryShape.product_eq_prod_deletedFactor,P.value_eq_product_get]
  apply Finset.prod_congr rfl
  intro e _
  exact native_resource_omission_shape_deleted_factor P hi hstar C e σ

theorem native_resource_omission_shape_restored_product {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceMonomial i star T)
    (hi : i ≤ star) (hstar : star < as.length) (C : ℕ→ℝ) (σ : T.Assignment) :
    (nativeResourceOmissionShape P hi hstar C).restoredProduct σ=
      P.test.value (fun s t=>orderedOverlap (n+1) (joinSpin s) (joinSpin t)) C σ := by
  rw [P.value_eq_product_get]
  unfold ActualNaturalBoundaryShape.restoredProduct
  apply Finset.prod_congr rfl
  intro e _
  unfold ActualNaturalBoundaryShape.restoredFactor nativeResourceOmissionShape
  ring

theorem native_resource_raw_scale_get_product {n : ℕ} {as : List PositiveMass} {i star : ℕ}
    {T : ClockTree (Spin n×Bool) as} (P : NativeResourceMonomial i star T) (x W : ℝ) :
    (∏e : Fin P.factors.length,(P.factors.get e).1.savedScale x W 1)=nativeResourceScale x W 1 P.tags := by
  unfold nativeResourceScale NativeResourceMonomial.tags
  rw [List.map_map,←List.prod_ofFn]
  change (List.ofFn ((fun f : NativeResourceFactor T=>f.1.savedScale x W 1) ∘ P.factors.get)).prod=_
  rw [←List.map_ofFn,List.ofFn_get]
  rfl

theorem native_resource_monomial_pair_budget_drop_saving
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceMonomial i star T)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (xroot : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (A x W ε : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x) (hW : 0 ≤ W) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C xroot A x W ε) :
    P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C xroot A x W 1 := by
  intro e
  dsimp only at hm ⊢
  apply (hm e).trans
  have HS : (P.factors.get e).1.savedScale x W ε ≤ (P.factors.get e).1.savedScale x W 1 := by
    cases (P.factors.get e).1 <;> simp only [NativeResourceMark.savedScale,one_mul] <;> first
    | exact le_rfl
    | exact mul_le_of_le_one_left hW hε1
  have H0 : 0 ≤ A*(P.factors.get e).1.savedScale x W ε := by
    cases (P.factors.get e).1 <;> simp only [NativeResourceMark.savedScale] <;> first
    | exact mul_nonneg hA (mul_nonneg hε hW)
    | positivity
  exact pow_le_pow_left₀ H0 (mul_le_mul_of_nonneg_left HS hA) _

theorem native_resource_live_omission_square
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceMonomial i star T) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (xroot : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (A x W : ℝ) (hA : 0 < A) (hx : 0 < x) (hxW : x ≤ W)
    (hi : i ≤ star) (hstar : star < as.length) (hsite : 1/(n+1:ℕ) ≤ x)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C xroot A x W 1) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(P.test.value (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C σ-
        P.test.value (fun s t=>orderedOverlap (n+1) (joinSpin s) (joinSpin t)) C σ)^2) xroot ≤
      (((P.factors.length:ℝ)/((n+1:ℕ)*x))*
        ((2*(A+2))^P.factors.length*nativeResourceScale x W 1 P.tags))^2 := by
  let G:=nativeResourceOmissionShape P hi hstar C
  by_cases hm0 : 0 < P.factors.length
  · have Hscale (e : Fin P.factors.length) : x ≤ (P.factors.get e).1.savedScale x W 1 := by
      cases (P.factors.get e).1 <;> simp only [NativeResourceMark.savedScale,one_mul] <;> first
      | exact le_rfl
      | exact hxW
    have Hmom (e : Fin P.factors.length) : T.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>|G.deletedFactor e σ|^(2*P.factors.length)) xroot ≤
          (A*(P.factors.get e).1.savedScale x W 1)^(2*P.factors.length) := by
      dsimp only [G]
      simp_rw [native_resource_omission_shape_deleted_factor]
      rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho v q xroot
        (P.factors.get e).2.1 (P.factors.get e).2.2 (P.factor_endpoints_distinct hi hstar e)
        (fun s t=>|deletedOverlap n (joinSpin s) (joinSpin t)-
          C (T.splitIndex (P.factors.get e).2.1 (P.factors.get e).2.2)|^(2*P.factors.length))]
      rw [P.cuts (P.factors.get e) (List.get_mem _ e)]
      exact hm e
    have H:=native_omitted_site_product_square n P.factors.length hm0 T ho v q xroot G
      (fun e=>(P.factors.get e).1.savedScale x W 1) x A 1 hx hA zero_lt_one Hscale hsite
      (fun _=>by dsimp only [G,nativeResourceOmissionShape];norm_num) Hmom
    dsimp only [G] at H
    simp_rw [native_resource_omission_shape_product,native_resource_omission_shape_restored_product] at H
    rw [native_resource_raw_scale_get_product] at H
    simpa only [mul_one,div_eq_mul_inv,one_mul,show A+1+1=A+2 by ring] using H
  · have hnil : P.factors=[]:=List.eq_nil_of_length_eq_zero (by omega)
    have HV (R : (Spin n×Bool)→(Spin n×Bool)→ℝ) : P.test.value R C=fun _=>1 := by
      funext σ
      rw [←P.factor_product_eq,hnil]
      rfl
    simp only [HV,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),ClockTree.disorderExpect,
      mul_zero,Finset.sum_const_zero,hnil,List.length_nil,Nat.cast_zero,zero_div,zero_mul,le_refl]

theorem native_resource_raw_scale_pos (rs : List NativeResourceMark)
    {x W : ℝ} (hx : 0 < x) (hW : 0 < W) : 0 < nativeResourceScale x W 1 rs := by
  have H:=nativeResourceEnvelope_pos rs (A:=1) zero_lt_one hx hW zero_lt_one
  simpa only [nativeResourceEnvelope_scale,one_pow,one_mul] using H

theorem native_frozen_resource_omission_square
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (v₀ : FullCoordinate n→ℝ) (q₀ : ℕ→FullCoordinate n→ℝ) (x₀ : FullCoordinate n→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (xroot : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (A x W : ℝ) (hA : 0 < A) (hx : 0 < x) (hxW : x ≤ W)
    (hi : i ≤ star) (hstar : star < as.length) (hsite : 1/(n+1:ℕ) ≤ x)
    (hm₀ : P.PairMomentBudget (fullWeight n) (fullFeature n) v₀ q₀
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀ A x W 1)
    (hm : P.live.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C xroot A x W 1) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(P.value (fullWeight n) (fullFeature n) v₀ q₀
        (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀ σ-
          nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ)^2) xroot ≤
      (|P.coefficient| *((P.live.factors.length:ℝ)/((n+1:ℕ)*x))*
        ((2*(A+2))^P.resources.length*nativeResourceScale x W 1 P.resources))^2 := by
  let B:=2*(A+2)
  have hB : 0 < B:=by dsimp [B];positivity
  have hAB : A ≤ B:=by dsimp [B];linarith
  have hW : 0 < W:=hx.trans_le hxW
  let fs:=P.frozen.flatMap (fun F=>F.monomial.tags)
  have HF:=frozen_resource_original_product_abs_le P.frozen (fullWeight_pos n) (fullFeature n)
    ho v₀ q₀ (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀ A x W 1
    hA hx hW zero_lt_one hi hstar hm₀.2
  have HE : nativeResourceEnvelope A x W 1 fs ≤ nativeResourceEnvelope B x W 1 fs := by
    rw [nativeResourceEnvelope_scale,nativeResourceEnvelope_scale]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA.le hAB _) (native_resource_raw_scale_pos fs hx hW).le
  have HS : |P.scalar (fullWeight n) (fullFeature n) v₀ q₀
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀| ≤
        |P.coefficient| *nativeResourceEnvelope B x W 1 fs := by
    have HS0 : |P.scalar (fullWeight n) (fullFeature n) v₀ q₀
        (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀| ≤
          |P.coefficient| *nativeResourceEnvelope A x W 1 fs := by
      simpa only [NativeResourceTerm.scalar,abs_mul] using
        mul_le_mul_of_nonneg_left HF (abs_nonneg P.coefficient)
    exact HS0.trans
      (mul_le_mul_of_nonneg_left HE (abs_nonneg P.coefficient))
  have HS2:= (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (abs_nonneg P.coefficient) (nativeResourceEnvelope_pos fs hB hx hW zero_lt_one).le)).mpr HS
  rw [sq_abs] at HS2
  have HL:=native_resource_live_omission_square P.live ho v q xroot C A x W hA hx hxW hi hstar hsite hm
  have H0 : 0 ≤ T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(P.live.test.value (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C σ-
        P.live.test.value (fun s t=>orderedOverlap (n+1) (joinSpin s) (joinSpin t)) C σ)^2) xroot := by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg fun σ _=>mul_nonneg
      ((T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q xroot).1 σ) (sq_nonneg _)
  have HD : (fun σ=>(P.value (fullWeight n) (fullFeature n) v₀ q₀
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀ σ-
        nativeOriginalFrozenRestoredResourceValue P v₀ q₀ x₀ C σ)^2)=
      fun σ=>(P.scalar (fullWeight n) (fullFeature n) v₀ q₀
        (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C x₀)^2*
        (P.live.test.value (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C σ-
          P.live.test.value (fun s t=>orderedOverlap (n+1) (joinSpin s) (joinSpin t)) C σ)^2 := by
    funext σ
    rw [native_frozen_resource_omission_eq_scalar_mul_live,mul_pow]
  rw [HD,T.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]
  apply (mul_le_mul HS2 HL H0 (sq_nonneg _)).trans_eq
  rw [nativeResourceEnvelope_scale]
  dsimp only [fs,B]
  simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map,
    pow_add,nativeResourceScale,List.map_append,List.prod_append]
  ring

theorem native_resource_term_pair_budget_drop_saving
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (xroot : FullCoordinate n→ℝ)
    (C : ℕ→ℝ) (A x W ε : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x) (hW : 0 ≤ W)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C xroot A x W ε) :
    P.PairMomentBudget (fullWeight n) (fullFeature n) v q
      (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t)) C xroot A x W 1 := by
  constructor
  · exact native_resource_monomial_pair_budget_drop_saving P.live v q xroot C A x W ε
      hA hx hW hε hε1 hm.1
  · intro F hF
    exact native_resource_monomial_pair_budget_drop_saving F.monomial v q xroot C A x W ε
      hA hx hW hε hε1 (hm.2 F hF)

end OAI.SKFluctuations.Cavity
