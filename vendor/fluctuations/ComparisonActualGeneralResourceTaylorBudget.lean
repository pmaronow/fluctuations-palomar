module

public import ComparisonActualGeneralResourceThirdLowReadout
public import ComparisonActualGeneralFreshResourceHighTaylorReadout
public import ComparisonActualGeneralFourCategories
public import ComparisonSignedCavityActualTaylorHighLowBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

def actualGeneralOriginalFreshResourceTaylorRemainder
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeActualTaylorRemainder n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark

theorem actual_general_normalized_fresh_resource_Taylor_abs_le
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U k : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    {W H L : ℝ} (hW : 0 < W) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hHigh : ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
      |(W⁻¹)^k*actualGeneralOriginalFreshResourceHigherHighPart bf hf U P part l t| ≤ H)
    (hLow : ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
      |(W⁻¹)^k*actualGeneralOriginalFreshResourceThirdLowPart bf hf U P l t| ≤ L) :
    |(W⁻¹)^k*actualGeneralOriginalFreshResourceTaylorRemainder bf hf U P| ≤ 2*H+L/2 := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let norm:=(W⁻¹)^k
  have hnorm : 0 < norm:=by dsimp only [norm];positivity
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hbf hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hhf hu hv huv)) as ho
  have HK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  have HKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  have H:=native_actual_taylor_remainder_abs_le_HIGH_LOW n q U b h K g.tree ho
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark
    (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
    (by intro x;cases x <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm
    (H/norm) (L/norm) (div_nonneg hH hnorm.le) (div_nonneg hL hnorm.le)
    (by
      intro l t hl ht part
      have HH:=hHigh l t hl ht part
      rw [abs_mul,abs_of_pos hnorm] at HH
      apply (le_div_iff₀ hnorm).2
      simpa only [actualGeneralOriginalFreshResourceHigherHighPart,mul_comm] using HH)
    (by
      intro l t hl ht
      have HH:=hLow l t hl ht
      rw [abs_mul,abs_of_pos hnorm] at HH
      apply (le_div_iff₀ hnorm).2
      simpa only [actualGeneralOriginalFreshResourceThirdLowPart,mul_comm] using HH)
  unfold actualGeneralOriginalFreshResourceTaylorRemainder
  dsimp only
  change |norm*nativeActualTaylorRemainder n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark| ≤ _
  rw [abs_mul,abs_of_pos hnorm]
  apply (mul_le_mul_of_nonneg_left H hnorm.le).trans_eq
  field_simp

theorem actual_general_four_higher_Taylor_contrast_eq_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (ho : MassOrdered 0 as) :
    actualGeneralFourCategoryContrast bf hf U st .higherTaylor=
      actualGeneralOriginalFreshResourceTaylorRemainder bf hf U st.term-
        (1/2:ℝ)*actualGeneralOriginalFreshResourceTaylorRemainder bf hf U (st.term.retarget 0) := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C st.tree st.term ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold actualGeneralFourCategoryContrast nativeActualOriginalOtherSourceCategory
    actualGeneralOriginalFreshResourceTaylorRemainder
  dsimp only
  rw [Hread]
  rfl

end OAI.SKFluctuations.Cavity
