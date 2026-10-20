module

public import ComparisonSignedCavityActualGeneratedGammaFirstHighProfile
public import ComparisonSignedCavityActualFrozenResourceMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_live_scale_eq_edge_product
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (P : NativeGeneratedTest T) (i : ℕ) (x W : ℝ) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial P i)=
      (P.edges.map (fun e=>if T.splitIndex e.1 e.2=i then x else W)).prod := by
  classical
  rw [←source_factor_scale_product,←List.prod_ofFn]
  congr 1
  conv_rhs => rw [←List.ofFn_get P.edges,List.map_ofFn]
  congr 1
  funext e
  simp only [sourceFactorScale,nativeGeneratedCompleteInitial,Finset.mem_filter,Finset.mem_univ,true_and,
    Function.comp_apply]

end OAI.SKFluctuations.Cavity
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open OAI.SKFluctuations.Cavity

theorem NativeResourceMonomial.canonical_live_scale_le
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceMonomial i star T) {x W : ℝ} (hx : 0 < x) (hxW : x ≤ W) :
    sourceMonomialScale x W (nativeGeneratedCompleteInitial P.test i) ≤
      nativeResourceScale x W 1 P.tags := by
  classical
  let f:=fun e : T.Slot×T.Slot=>if T.splitIndex e.1 e.2=i then x else W
  rw [native_generated_live_scale_eq_edge_product]
  change (P.test.edges.map f).prod ≤ _
  rw [←(P.realizes.map f).prod_eq]
  simp only [List.map_map,nativeResourceScale,NativeResourceMonomial.tags]
  have Hnonneg (e : NativeResourceFactor T) : 0 ≤ f e.2 := by
    dsimp only [f]
    split_ifs
    · exact hx.le
    · exact hx.le.trans hxW
  have Hle (e : NativeResourceFactor T) (he : e∈P.factors) : f e.2 ≤ e.1.savedScale x W 1 := by
    have H:=P.cuts e he
    dsimp only [f]
    rw [H]
    cases e.1 <;> simp only [NativeResourceMark.cut,NativeResourceMark.savedScale,ite_true,one_mul]
    all_goals first
      | exact le_rfl
      | split_ifs <;> simp_all
  have H:=Finset.prod_le_prod₀ (s:=Finset.univ)
    (f:=fun e : Fin P.factors.length=>f (P.factors.get e).2)
    (g:=fun e=>((P.factors.get e).1).savedScale x W 1)
    (fun e _=>Hnonneg _) (fun e _=>Hle _ (List.get_mem _ e))
  rw [←List.prod_ofFn,←List.prod_ofFn] at H
  change (List.ofFn ((f ∘ Prod.snd) ∘ P.factors.get)).prod ≤
    (List.ofFn (((fun z : NativeResourceMark => z.savedScale x W 1) ∘ Prod.fst) ∘ P.factors.get)).prod at H
  rw [←List.map_ofFn,←List.map_ofFn,List.ofFn_get] at H
  exact H

theorem NativeResourceTerm.scalar_mul_canonical_live_scale_le
    {n : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T) {w : (Spin n×Bool)→ℝ} (hw : ∀σ,0 < w σ)
    (φ : (Spin n×Bool)→(ι→ℝ)→L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (R : (Spin n×Bool)→(Spin n×Bool)→ℝ) (C : ℕ→ℝ) (y : ι→ℝ)
    {A x W : ℝ} (hA : 1 ≤ A) (hx : 0 < x) (hxW : x ≤ W)
    (hi : i ≤ star) (hs : star < as.length)
    (hm : P.PairMomentBudget w φ v q R C y A x W 1) :
    |P.scalar w φ v q R C y| * sourceMonomialScale x W (nativeGeneratedCompleteInitial P.live.test i) ≤
      |P.coefficient| * nativeResourceEnvelope A x W 1 P.resources := by
  have hW : 0 < W:=hx.trans_le hxW
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  have HF:=frozen_resource_original_product_abs_le P.frozen hw φ ho v q R C y A x W 1
    hA0 hx hW zero_lt_one hi hs hm.2
  have hscale : 0 ≤ sourceMonomialScale x W (nativeGeneratedCompleteInitial P.live.test i) := by
    unfold sourceMonomialScale
    positivity
  have HL:=P.live.canonical_live_scale_le hx hxW
  have HL' : sourceMonomialScale x W (nativeGeneratedCompleteInitial P.live.test i) ≤
      nativeResourceEnvelope A x W 1 P.live.tags := by
    rw [nativeResourceEnvelope_scale]
    apply HL.trans
    exact le_mul_of_one_le_left
      (by
        unfold nativeResourceScale
        apply List.prod_nonneg
        intro z hz
        obtain ⟨m,hm,rfl⟩:=List.mem_map.mp hz
        exact (m.savedScale_pos hx hW zero_lt_one).le)
      (one_le_pow₀ hA)
  have H:=mul_le_mul HF HL' hscale (nativeResourceEnvelope_pos _ hA0 hx hW zero_lt_one).le
  have HH:=mul_le_mul_of_nonneg_left H (abs_nonneg P.coefficient)
  simpa only [NativeResourceTerm.scalar,abs_mul,NativeResourceTerm.resources,
    nativeResourceEnvelope_append,mul_assoc] using HH

end OAI.SKFluctuations.Hierarchy.ClockTree
