module

public import ComparisonSignedCavityActualResourceTerminalMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
variable {as : List PositiveMass}

omit [Nonempty S] [Nonempty ι] in
theorem NativeResourceMonomial.pairMomentBudget_retainOnMarked
    {i star : ℕ} {T : ClockTree S as} (P : NativeResourceMonomial i star T)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε) :
    (P.retainOnMarked a p hp).PairMomentBudget w φ v q R C x₀ A x W ε := by
  unfold NativeResourceMonomial.PairMomentBudget at hm ⊢
  intro e
  dsimp only
  let e' : Fin P.factors.length :=
    ⟨e.val,by simpa only [NativeResourceMonomial.retainOnMarked,List.length_map] using e.isLt⟩
  have hfactor : ((P.retainOnMarked a p hp).factors.get e).1=(P.factors.get e').1 := by
    exact congrArg Prod.fst (List.getElem_map (nativeResourceMarkedLiftFactor p)
      (l:=P.factors) (i:=e.val) (h:=e.isLt))
  rw [hfactor]
  simpa only [NativeResourceMonomial.retainOnMarked,List.length_map] using hm e'

omit [Nonempty S] [Nonempty ι] in
theorem NativeResourceTerm.pairMomentBudget_retainOnMarked
    {i star : ℕ} {T : ClockTree S as} (P : NativeResourceTerm i star T)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (w : S → ℝ) (φ : S → (ι → ℝ)→L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε) :
    (P.retainOnMarked a p hp).PairMomentBudget w φ v q R C x₀ A x W ε :=
  ⟨P.live.pairMomentBudget_retainOnMarked a p hp w φ v q R C x₀ A x W ε hm.1,hm.2⟩

theorem NativeActualResourceGenerated.normalized_transported_terminal_pairing_sq_le
    {i star U : ℕ} {seed : List NativeResourceMark} {k : ℕ}
    {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {V : ClockTree S as} (Q : NativeResourceTerm i star V)
    (hresources : Q.resources=P.resources) (hcoeff : Q.coefficient=P.coefficient)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : Q.PairMomentBudget w φ v q R C x₀ A x W ε)
    (G : V.Assignment → ℝ) (B : ℝ)
    (hG : V.disorderExpect w φ v q (fun σ=>(G σ)^2) x₀≤B^2) :
    (V.disorderExpect w φ v q
      (fun σ=>(W⁻¹)^k*(Q.value w φ v q R C x₀ σ*G σ)) x₀)^2≤
      (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)^2 := by
  have HS:=Q.square_moment_le hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar hm
  rw [hresources,hcoeff,nativeResourceEnvelope_scale,hP.total_factor_depth,hP.saved_scale x W ε] at HS
  have HG0 : 0≤V.disorderExpect w φ v q (fun σ=>(G σ)^2) x₀ :=
    Finset.sum_nonneg (fun σ _=>mul_nonneg ((V.disorderWeight_probability hw φ ho v q x₀).1 σ) (sq_nonneg _))
  have HC:=V.disorderExpect_mul_sq_le hw φ ho v q (Q.value w φ v q R C x₀) G x₀
  have Hpair := HC.trans (mul_le_mul HS hG HG0 (sq_nonneg _))
  rw [V.disorderExpect_const_mul hw φ ho,mul_pow]
  apply (mul_le_mul_of_nonneg_left Hpair (sq_nonneg ((W⁻¹)^k))).trans
  have hcancel : (W⁻¹)^k*W^k=1 := by rw [←mul_pow,inv_mul_cancel₀ hW.ne',one_pow]
  apply le_of_eq
  calc
    _ = ((|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)*
        ((W⁻¹)^k*W^k))^2 := by rw [mul_pow];ring
    _ = _ := by rw [hcancel,mul_one]

theorem NativeActualResourceGenerated.normalized_transported_terminal_pairing_abs_le
    {i star U : ℕ} {seed : List NativeResourceMark} {k : ℕ}
    {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {V : ClockTree S as} (Q : NativeResourceTerm i star V)
    (hresources : Q.resources=P.resources) (hcoeff : Q.coefficient=P.coefficient)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : Q.PairMomentBudget w φ v q R C x₀ A x W ε)
    (G : V.Assignment → ℝ) (B : ℝ) (hB : 0≤B)
    (hG : V.disorderExpect w φ v q (fun σ=>(G σ)^2) x₀≤B^2) :
    |V.disorderExpect w φ v q
      (fun σ=>(W⁻¹)^k*(Q.value w φ v q R C x₀ σ*G σ)) x₀|≤
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B := by
  have hscale : 0≤nativeResourceScale x W ε seed := by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro a ha
    obtain ⟨m,hm,rfl⟩:=List.mem_map.mp ha
    exact (m.savedScale_pos hx hW hε).le
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  simpa only [sq_abs] using hP.normalized_transported_terminal_pairing_sq_le Q hresources hcoeff
    hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar hm G B hG

end OAI.SKFluctuations.Hierarchy.ClockTree
