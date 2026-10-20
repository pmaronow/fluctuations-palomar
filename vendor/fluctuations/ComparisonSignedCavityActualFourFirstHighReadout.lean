module

public import ComparisonSignedCavityActualFrozenGammaFirstHighProfile
public import ComparisonSignedCavityActualResourceRestReadout
public import ComparisonSignedCavityOriginalGammaPairLawAdapter

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

theorem native_actual_resource_rest_value_retarget
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} {T : ClockTree (Spin n×Bool) as}
    (P : NativeResourceTerm i star T)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (C : ℕ→ℝ) :
    nativeActualResourceRestValue (P.retarget 0) v q x C=
      fun σ=>nativeActualResourceRestValue P v q x C
        ((nativeFreshAtSlot T 0 P.live.test.target star).restRestrict σ) := by
  funext σ
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let τ:=g.tree.cavityAssignment.symm (σ,assignmentOfSlots g.tree.cavityRight (fun _=>false))
  have Hτ : (g.tree.cavityAssignment τ).1=σ:=by simp only [τ,Equiv.apply_symm_apply]
  rw [←Hτ,native_actual_resource_rest_value_eq_full,P.retarget_value,←g.restRestrict_actual,
    native_actual_resource_rest_value_eq_full]

theorem native_gamma_first_high_affine_kernel
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (s : T.Slot) (star U : ℕ) (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) (c d : ℝ) :
    nativeGammaProjectedFirstHighDisplacement T s star U q b h K (fun σ τ=>c*(A σ τ-d)) P=
      c*nativeGammaProjectedFirstHighDisplacement T s star U q b h K A P := by
  unfold nativeGammaProjectedFirstHighDisplacement
  dsimp only
  rw [←List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro p hp
  have H : nativeRestProjectedDisplacementTest T s star (fun σ τ=>c*(A σ τ-d)) P p=
      fun σ=>c*nativeRestProjectedDisplacementTest T s star A P p σ := by
    funext σ
    dsimp only [nativeRestProjectedDisplacementTest]
    ring
  rw [H,retained_signed_jets_const_mul_test]
  ring

theorem actual_minimum_generated_first_high_sub_const
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) (c : ℝ) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A (fun σ=>P σ-c)=
      nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A P := by
  dsimp only
  rw [actual_minimum_generated_Gamma_first_high_eq_paired_source M hP hi hs ho,
    actual_minimum_generated_Gamma_first_high_eq_paired_source M hP hi hs ho]
  congr 1
  congr 1
  apply List.map_congr_left
  intro p hp
  have H : nativeRestProjectedPairedTest T P₀.live.test.target star A (fun σ=>P σ-c) p=
      nativeRestProjectedPairedTest T P₀.live.test.target star A P p := by
    funext σ
    dsimp only [nativeRestProjectedPairedTest]
    ring
  rw [H]

theorem nativeActualResourceFirstHigh_eq_rest_readout
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    nativeActualResourceFirstHigh M U P=
      nativeGammaProjectedFirstHighDisplacement T P.live.test.target star U
        (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
        (fun σ τ=>(∑j,spinValue (σ j)*spinValue (τ j))/(n+1:ℕ))
        (nativeActualResourceRestValue P 0 qfull 0 C) := by
  dsimp only
  rw [nativeActualResourceFirstHigh_eq_literal_source]
  unfold nativeActualResourceRestValue
  simp only [deletedOverlap,joinSpin,Fin.lastCases_castSucc]

theorem actual_minimum_resource_centered_first_high
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
    let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
    nativeGammaProjectedFirstHighDisplacement T P.live.test.target star U q b h K
      (restCenteredFixedForkKernel n b C star 0) Pc=
      b star*nativeActualResourceFirstHigh M U P := by
  dsimp only
  rw [nativeActualResourceFirstHigh_eq_rest_readout]
  dsimp only
  have HK (b C : ℕ→ℝ) : restCenteredFixedForkKernel n b C star 0=
      fun σ τ=>b star*((∑j,spinValue (σ j)*spinValue (τ j))/(n+1:ℕ)-C star) := by
    funext σ τ
    rfl
  rw [HK,native_gamma_first_high_affine_kernel]
  congr 1
  exact actual_minimum_generated_first_high_sub_const M hP hi hs ho _ _ _

end OAI.SKFluctuations.Cavity
