module

public import ComparisonActualGeneralGammaHighSecondPairedSource
public import ComparisonSignedCavityActualResourceGammaHighSecondKernel

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def actualGeneralGeneratedHighSecond {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (star U : ℕ)
    (P : NativeGeneratedTest T) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  nativeGammaProjectedHighSecondRestoration T P.target star U
    (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h
    (nativeContinuumMixedClock n bf hf as) A
    (nativeRestGeneratedTestValue T P A (nativePhysicalResourceCenter n bf hf as))

theorem actual_general_generated_high_second_empty_live
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as)
    (hempty : P₀.live.test.edges=[]) :
    actualGeneralGeneratedHighSecond bf hf T star U P₀.live.test=0 := by
  unfold actualGeneralGeneratedHighSecond
  dsimp only
  have HE (A : Spin n→Spin n→ℝ) (C : ℕ→ℝ) :
      nativeRestGeneratedTestValue T P₀.live.test A C=fun _=>1 := by
    funext σ
    simp only [nativeRestGeneratedTestValue,hempty,List.map_nil,List.prod_nil]
  rw [HE,actual_general_generated_Gamma_high_second_eq_paired_source bf hf hbf hhf hP hi hs ho]
  simp only [native_rest_projected_paired_constant_zero,actual_general_rest_payload_high_second_integral_zero bf hf hbf hhf _ ho U,
    mul_zero,List.map_const',List.sum_replicate,nsmul_zero]

theorem actual_general_generated_high_second_fixed_fork_kernel
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (star U : ℕ) (P : NativeGeneratedTest T) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let C:=nativePhysicalResourceCenter n bf hf as
    let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    nativeGammaProjectedHighSecondRestoration T P.target star U q b h K
      (restCenteredFixedForkKernel n b C star 0) (nativeRestGeneratedTestValue T P A C)=
      b star*actualGeneralGeneratedHighSecond bf hf T star U P := by
  dsimp only
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hbf hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hhf hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n bf hf
    hbf hhf as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n bf hf
    hbf hhf as ho
  have hq : ∀j₀,Monotone (fun j=>q j j₀) := by
    intro j₀
    cases j₀ with
    | inl j₀=>exact hbm
    | inr j₀=>exact hhm
  have hq0 : ∀j j₀,0 ≤ q j j₀ := by
    intro j j₀
    cases j₀ with
    | inl j₀=>exact hb j
    | inr j₀=>exact hh j
  let C:=nativePhysicalResourceCenter n bf hf as
  let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  have HA : restCenteredFixedForkKernel n b C star 0=
      (fun σ τ=>b star*A σ τ+(-b star*C star)) := by
    funext σ τ
    simp only [restCenteredFixedForkKernel,A,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
    ring
  rw [HA,native_gamma_high_second_affine_kernel T ho P.target star U q b h K A
    (nativeRestGeneratedTestValue T P A C) (b star) (-b star*C star)
    hq0 hq hb hh hK hbm hhm hKm]
  rfl

end OAI.SKFluctuations.Cavity
