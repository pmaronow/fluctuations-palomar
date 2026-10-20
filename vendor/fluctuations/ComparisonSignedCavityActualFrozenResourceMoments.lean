module

public import ComparisonSignedCavityActualMarkedResourceMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
variable {as : List PositiveMass}

theorem frozen_resource_original_product_abs_le {i star : ℕ}
    (Fs : List (NativeFrozenResource S as i star)) {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm : ∀ F∈Fs,F.monomial.PairMomentBudget w φ v q R C x₀ A x W ε) :
    |(Fs.map (fun F => F.mean w φ v q R C x₀)).prod| ≤
      nativeResourceEnvelope A x W ε (Fs.flatMap (fun F => F.monomial.tags)) := by
  induction Fs with
  | nil => simp [nativeResourceEnvelope]
  | cons F Fs ih =>
    have hF := F.mean_abs_le hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar
      (hm F (List.mem_cons_self))
    have hFs := ih (fun F hF => hm F (List.mem_cons_of_mem _ hF))
    simpa only [List.map_cons,List.prod_cons,abs_mul,List.flatMap_cons,
      nativeResourceEnvelope_append] using
      mul_le_mul hF hFs (abs_nonneg _) (nativeResourceEnvelope_pos _ hA hx hW hε).le

theorem NativeResourceTerm.frozen_original_square_moment_le {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v₀ : ι → ℝ) (q₀ : ℕ → ι → ℝ) (x₀ : ι → ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (y : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm₀ : P.PairMomentBudget w φ v₀ q₀ R C x₀ A x W ε)
    (hm : P.live.PairMomentBudget w φ v q R C y A x W ε) :
    T.disorderExpect w φ v q (fun σ => (P.value w φ v₀ q₀ R C x₀ σ)^2) y ≤
      (|P.coefficient| * nativeResourceEnvelope A x W ε P.resources)^2 := by
  have HF := frozen_resource_original_product_abs_le P.frozen hw φ ho v₀ q₀ R C x₀ A x W ε
    hA hx hW hε hi hstar hm₀.2
  have HS : |P.scalar w φ v₀ q₀ R C x₀| ≤
      |P.coefficient| * nativeResourceEnvelope A x W ε
        (P.frozen.flatMap (fun F => F.monomial.tags)) := by
    simpa only [NativeResourceTerm.scalar,abs_mul] using
      mul_le_mul_of_nonneg_left HF (abs_nonneg P.coefficient)
  have HS2 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _)
    (nativeResourceEnvelope_pos _ hA hx hW hε).le)).mpr HS
  rw [sq_abs] at HS2
  have HL := P.live.square_moment_le hw φ ho v q R C y A x W ε
    hA hx hW hε hi hstar hm
  have hL0 : 0 ≤ T.disorderExpect w φ v q (fun σ => (P.live.test.value R C σ)^2) y :=
    Finset.sum_nonneg (fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q y).1 σ) (sq_nonneg _))
  have he : (fun σ => (P.value w φ v₀ q₀ R C x₀ σ)^2) =
      fun σ => (P.scalar w φ v₀ q₀ R C x₀)^2*(P.live.test.value R C σ)^2 := by
    funext σ
    exact mul_pow _ _ 2
  rw [he,T.disorderExpect_const_mul hw φ ho]
  apply (mul_le_mul HS2 HL hL0 (sq_nonneg _)).trans
  rw [NativeResourceTerm.resources,nativeResourceEnvelope_append]
  ring_nf
  rfl

theorem NativeActualResourceGenerated.normalized_frozen_transported_terminal_pairing_sq_le
    {i star U : ℕ} {seed : List NativeResourceMark} {k : ℕ}
    {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {V : ClockTree S as} (Q : NativeResourceTerm i star V)
    (hresources : Q.resources=P.resources) (hcoeff : Q.coefficient=P.coefficient)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v₀ : ι → ℝ) (q₀ : ℕ → ι → ℝ) (x₀ : ι → ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (y : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm₀ : Q.PairMomentBudget w φ v₀ q₀ R C x₀ A x W ε)
    (hm : Q.live.PairMomentBudget w φ v q R C y A x W ε)
    (G : V.Assignment → ℝ) (B : ℝ)
    (hG : V.disorderExpect w φ v q (fun σ=>(G σ)^2) y≤B^2) :
    (V.disorderExpect w φ v q
      (fun σ=>(W⁻¹)^k*(Q.value w φ v₀ q₀ R C x₀ σ*G σ)) y)^2≤
      (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)^2 := by
  have HS:=Q.frozen_original_square_moment_le hw φ ho v₀ q₀ x₀ v q R C y A x W ε hA hx hW hε hi hstar hm₀ hm
  rw [hresources,hcoeff,nativeResourceEnvelope_scale,hP.total_factor_depth,hP.saved_scale x W ε] at HS
  have HG0 : 0≤V.disorderExpect w φ v q (fun σ=>(G σ)^2) y :=
    Finset.sum_nonneg (fun σ _=>mul_nonneg ((V.disorderWeight_probability hw φ ho v q y).1 σ) (sq_nonneg _))
  have HC:=V.disorderExpect_mul_sq_le hw φ ho v q (Q.value w φ v₀ q₀ R C x₀) G y
  have Hpair := HC.trans (mul_le_mul HS hG HG0 (sq_nonneg _))
  rw [V.disorderExpect_const_mul hw φ ho,mul_pow]
  apply (mul_le_mul_of_nonneg_left Hpair (sq_nonneg ((W⁻¹)^k))).trans
  have hcancel : (W⁻¹)^k*W^k=1 := by rw [←mul_pow,inv_mul_cancel₀ hW.ne',one_pow]
  apply le_of_eq
  calc
    _ = ((|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)*
        ((W⁻¹)^k*W^k))^2 := by rw [mul_pow];ring
    _ = _ := by rw [hcancel,mul_one]

theorem NativeActualResourceGenerated.normalized_frozen_transported_terminal_pairing_abs_le
    {i star U : ℕ} {seed : List NativeResourceMark} {k : ℕ}
    {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {V : ClockTree S as} (Q : NativeResourceTerm i star V)
    (hresources : Q.resources=P.resources) (hcoeff : Q.coefficient=P.coefficient)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v₀ : ι → ℝ) (q₀ : ℕ → ι → ℝ) (x₀ : ι → ℝ)
    (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (y : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm₀ : Q.PairMomentBudget w φ v₀ q₀ R C x₀ A x W ε)
    (hm : Q.live.PairMomentBudget w φ v q R C y A x W ε)
    (G : V.Assignment → ℝ) (B : ℝ) (hB : 0≤B)
    (hG : V.disorderExpect w φ v q (fun σ=>(G σ)^2) y≤B^2) :
    |V.disorderExpect w φ v q
      (fun σ=>(W⁻¹)^k*(Q.value w φ v₀ q₀ R C x₀ σ*G σ)) y|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B := by
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  simpa only [sq_abs] using hP.normalized_frozen_transported_terminal_pairing_sq_le Q hresources hcoeff
    hw φ ho v₀ q₀ x₀ v q R C y A x W ε hA hx hW hε hi hstar hm₀ hm G B hG

theorem NativeActualResourceGenerated.normalized_frozen_square_moment_le
    {i star U : ℕ} {seed : List NativeResourceMark} {k : ℕ}
    {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v₀ : ι→ℝ) (q₀ : ℕ→ι→ℝ) (x₀ : ι→ℝ)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (R : S→S→ℝ) (C : ℕ→ℝ) (y : ι→ℝ)
    (A x W ε : ℝ) (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm₀ : P.PairMomentBudget w φ v₀ q₀ R C x₀ A x W ε)
    (hm : P.live.PairMomentBudget w φ v q R C y A x W ε) :
    T.disorderExpect w φ v q (fun σ=>((W⁻¹)^k*P.value w φ v₀ q₀ R C x₀ σ)^2) y≤
      (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)^2 := by
  have HS:=P.frozen_original_square_moment_le hw φ ho v₀ q₀ x₀ v q R C y
    A x W ε hA hx hW hε hi hstar hm₀ hm
  rw [nativeResourceEnvelope_scale,hP.total_factor_depth,hP.saved_scale x W ε] at HS
  simp_rw [mul_pow]
  rw [T.disorderExpect_const_mul hw φ ho]
  apply (mul_le_mul_of_nonneg_left HS (sq_nonneg ((W⁻¹)^k))).trans
  have hcancel : (W⁻¹)^k*W^k=1 := by rw [←mul_pow,inv_mul_cancel₀ hW.ne',one_pow]
  apply le_of_eq
  calc
    _=((|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k)*
      ((W⁻¹)^k*W^k))^2 := by rw [mul_pow];ring
    _=_ := by rw [hcancel,mul_one];ring

end OAI.SKFluctuations.Hierarchy.ClockTree
