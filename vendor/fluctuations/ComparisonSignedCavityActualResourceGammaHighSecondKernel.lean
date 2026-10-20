module

public import ComparisonSignedCavityInheritedGammaHighSecondBoundedDegree
public import ComparisonSignedCavityActualResourceGammaRestorationReadout
public import ComparisonSignedCavityGeneratedPairedFrozenScale
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_gamma_high_second_affine_kernel
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) (α c : ℝ)
    (hq0 : ∀j j₀,0 ≤ q j j₀) (hq : ∀j₀,Monotone (fun j=>q j j₀))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeGammaProjectedHighSecondRestoration T s star U q b h K
        (fun σ τ=>α*A σ τ+c) P=
      α*nativeGammaProjectedHighSecondRestoration T s star U q b h K A P := by
  unfold nativeGammaProjectedHighSecondRestoration
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have Htest : (fun σ : p.tree.Assignment=>nativeRestProjectedDisplacementTest T s star
      (fun u v=>α*A u v+c) P p (p.tree.cavityAssignment σ).1)=
      (fun σ=>α*nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1) := by
    funext σ
    dsimp only [nativeRestProjectedDisplacementTest]
    ring
  have HE:=native_frozen_high_jets_eq_of_expectation_eq n q U b h K p.tree ho
    (fun σ=>nativeRestProjectedDisplacementTest T s star (fun u v=>α*A u v+c) P p (p.tree.cavityAssignment σ).1)
    (fun σ=>nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1) α
    hq0 hq hb hh hK hbm hhm hKm (fun t _=>by
      rw [Htest,p.tree.disorderExpect_const_mul (fullWeight_pos n) (fullFeature n) ho]) 2
  have HI : (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K p.tree
      (fun σ=>nativeRestProjectedDisplacementTest T s star (fun u v=>α*A u v+c) P p
        (p.tree.cavityAssignment σ).1) 0 0 2 t)=
      α*(∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K p.tree
        (fun σ=>nativeRestProjectedDisplacementTest T s star A P p (p.tree.cavityAssignment σ).1) 0 0 2 t) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [HE t (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht)]
    ring
  rw [HI]
  ring

theorem actual_minimum_generated_high_second_fixed_fork_kernel
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (star U : ℕ) (P : NativeGeneratedTest T) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let C:=nativePhysicalResourceCenter n M.bf M.hf as
    let A:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    nativeGammaProjectedHighSecondRestoration T P.target star U q b h K
      (restCenteredFixedForkKernel n b C star 0) (nativeRestGeneratedTestValue T P A C)=
      b star*nativeActualGeneratedHighSecond M T star U P := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_bf_monotone hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.inherited_hf_monotone hu hv huv)) as ho
  have hb j : 0 ≤ b j:=NNReal.coe_nonneg _
  have hh j : 0 ≤ h j:=NNReal.coe_nonneg _
  have hK : ∀j,0 ≤ K j:=native_continuum_mixed_clock_nonneg n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm : Monotone K:=native_continuum_mixed_clock_monotone n M.bf M.hf
    M.inherited_bf_monotone M.inherited_hf_monotone as ho
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
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
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
