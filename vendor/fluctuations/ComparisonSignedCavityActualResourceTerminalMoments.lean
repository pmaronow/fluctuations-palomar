module

public import ComparisonSignedCavityActualResourceFold
public import ComparisonSignedCavityGeneratedResourcesMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem NativeActualResourceGenerated.seed_counts {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) :
    nativeInitialResourceCount seed ≤ 1 ∧ nativeMarkedResourceCount seed=0 := by
  induction h with
  | physical h=>exact h.to_resource_generated.seed_counts
  | freeze h ih=>exact ih
  | reweight h c ih=>exact ih
  | retarget h ih=>exact ih
  | projection h hl ih=>exact ih
  | markedSwitch h p hp hs hh ih=>exact ih

theorem NativeActualResourceGenerated.at_most_one_initial_across_expectations
    {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) :
    nativeInitialResourceCount P.resources ≤ 1 := by
  rw [h.resource_word]
  simpa [nativeInitialResourceCount,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,NativeResourceMark.initialWeight] using h.seed_counts.1

theorem NativeActualResourceGenerated.exact_marked_depth
    {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) :
    nativeMarkedResourceCount P.resources=k := by
  rw [h.resource_word]
  simp only [nativeMarkedResourceCount,List.map_append,List.sum_append]
  change nativeMarkedResourceCount seed+
    nativeMarkedResourceCount ((List.range k).map NativeResourceMark.markedStar)=k
  rw [h.seed_counts.2,nativeMarkedResourceCount_range,zero_add]

theorem NativeActualResourceGenerated.total_factor_depth
    {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) :
    P.resources.length=seed.length+k := by
  rw [h.resource_word]
  simp only [List.length_append,List.length_map,List.length_range]

theorem NativeActualResourceGenerated.saved_scale
    {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) (x W ε : ℝ) :
    nativeResourceScale x W ε P.resources=nativeResourceScale x W ε seed*(ε*W)^k := by
  rw [h.resource_word]
  simp only [nativeResourceScale,List.map_append,List.prod_append]
  rw [show ((((List.range k).map NativeResourceMark.markedStar).map
    (NativeResourceMark.savedScale x W ε)).prod)=(ε*W)^k from nativeResourceScale_marked_range x W ε k]

theorem NativeActualResourceGenerated.normalized_saved_scale
    {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) (x W ε : ℝ) (hW : W≠0) :
    (W⁻¹)^k*nativeResourceScale x W ε P.resources=nativeResourceScale x W ε seed*ε^k := by
  rw [h.saved_scale x W ε]
  calc
    _=nativeResourceScale x W ε seed*ε^k*((W⁻¹)^k*W^k) := by rw [mul_pow];ring
    _=_ := by rw [←mul_pow,inv_mul_cancel₀ hW,one_pow,mul_one]

variable {ι : Type} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

theorem NativeActualResourceGenerated.terminal_pairing_sq_le
    {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε)
    (G : T.Assignment → ℝ) (B : ℝ)
    (hG : T.disorderExpect w φ v q (fun σ=>(G σ)^2) x₀≤B^2) :
    (T.disorderExpect w φ v q (fun σ=>P.value w φ v q R C x₀ σ*G σ) x₀)^2≤
      (|P.coefficient| *A^P.resources.length*nativeResourceScale x W ε seed*(ε*W)^k*B)^2 := by
  have HS:=P.square_moment_le hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar hm
  have HG0 : 0≤T.disorderExpect w φ v q (fun σ=>(G σ)^2) x₀ :=
    Finset.sum_nonneg (fun σ _=>mul_nonneg ((T.disorderWeight_probability hw φ ho v q x₀).1 σ) (sq_nonneg _))
  have HC:=T.disorderExpect_mul_sq_le hw φ ho v q (P.value w φ v q R C x₀) G x₀
  apply (HC.trans (mul_le_mul HS hG HG0 (sq_nonneg _))).trans
  rw [nativeResourceEnvelope_scale,hP.saved_scale x W ε]
  ring_nf
  rfl

theorem NativeActualResourceGenerated.normalized_terminal_pairing_sq_le
    {i star U : ℕ} {seed : List NativeResourceMark}
    {k : ℕ} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star<as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε)
    (G : T.Assignment → ℝ) (B : ℝ)
    (hG : T.disorderExpect w φ v q (fun σ=>(G σ)^2) x₀≤B^2) :
    (T.disorderExpect w φ v q (fun σ=>(W⁻¹)^k*(P.value w φ v q R C x₀ σ*G σ)) x₀)^2≤
      (|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)^2 := by
  rw [T.disorderExpect_const_mul hw φ ho,mul_pow]
  have H:=mul_le_mul_of_nonneg_left
    (hP.terminal_pairing_sq_le hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar hm G B hG)
    (sq_nonneg ((W⁻¹)^k))
  rw [hP.total_factor_depth] at H
  apply H.trans
  rw [←mul_pow]
  have he : (W⁻¹)^k*(|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*(ε*W)^k*B)=
      |P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B := by
    calc
      _=(|P.coefficient| *A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)*((W⁻¹)^k*W^k) := by
        rw [mul_pow];ring
      _=_ := by rw [←mul_pow,inv_mul_cancel₀ hW.ne',one_pow,mul_one]
  rw [he]

end OAI.SKFluctuations.Hierarchy.ClockTree
