module

public import ComparisonSignedCavityActualFreshResourceHighTaylorReadout
public import ComparisonSignedCavityActualFreshResourceLowTaylorReadout
public import ComparisonSignedCavityActualTaylorHighLowBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

def nativeActualOriginalFreshResourceTaylorRemainder
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeActualTaylorRemainder n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark

theorem actual_minimum_normalized_fresh_resource_Taylor_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U k : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    {W H L : ℝ} (hW : 0 < W) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hHigh : ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
      |(W⁻¹)^k*nativeActualOriginalFreshResourceHigherHighPart M U P part l t| ≤ H)
    (hLow : ∀l t : ℝ,l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
      |(W⁻¹)^k*nativeActualOriginalFreshResourceThirdLowPart M U P l t| ≤ L) :
    |(W⁻¹)^k*nativeActualOriginalFreshResourceTaylorRemainder M U P| ≤ 2*H+L/2 := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let norm:=(W⁻¹)^k
  have hnorm : 0 < norm:=by dsimp only [norm];positivity
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.inherited_hf_monotone hu hv huv) as ho
  have HK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
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
      simpa only [nativeActualOriginalFreshResourceHigherHighPart,mul_comm] using HH)
    (by
      intro l t hl ht
      have HH:=hLow l t hl ht
      rw [abs_mul,abs_of_pos hnorm] at HH
      apply (le_div_iff₀ hnorm).2
      simpa only [nativeActualOriginalFreshResourceThirdLowPart,mul_comm] using HH)
  unfold nativeActualOriginalFreshResourceTaylorRemainder
  dsimp only
  change |norm*nativeActualTaylorRemainder n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark| ≤ _
  rw [abs_mul,abs_of_pos hnorm]
  apply (mul_le_mul_of_nonneg_left H hnorm.le).trans_eq
  field_simp

end OAI.SKFluctuations.Cavity
