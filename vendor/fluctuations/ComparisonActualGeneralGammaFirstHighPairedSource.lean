module

public import ComparisonSignedCavityActualGeneratedGammaFirstHighProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators

theorem actual_general_generated_Gamma_first_high_eq_paired_source
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ) :
    let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n bf hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let g:=nativeFreshAtSlot T 0 P₀.live.test.target star
    nativeGammaProjectedFirstHighDisplacement T P₀.live.test.target star U q b h K A P=
      (1/2:ℝ)*((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed P₀.live.test.target)) p.mark*
        retainedSignedJets n q U b h K [restHighKernel n U b h K] p.tree
          (nativeRestProjectedPairedTest T P₀.live.test.target star A P p) [])).sum := by
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
  exact native_actual_generated_Gamma_first_high_eq_paired_source hP hi hs ho q b h K A P
    hq0 hq hb hh hK hbm hhm hKm

end OAI.SKFluctuations.Cavity
