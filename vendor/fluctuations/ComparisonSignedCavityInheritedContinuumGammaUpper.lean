module

public import ComparisonSignedCavityActualContinuumGammaUpper
public import ComparisonSignedCavityInheritedCanonicalSourceMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_continuum_scalar_gamma_mass_bound
    (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf →
      ∀(as : List PositiveMass) (_ho : MassOrdered 0 as)
        (T : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U →
      ∀(s e : T.Slot),s≠e →
        let K:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
          (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        |fullScalarCutGamma T U K s e| ≤ Cg*(M.xs+partitionPoint 0 as (T.splitIndex s e)) := by
  obtain ⟨B,hB,HB⟩:=eventually_actual_minimum_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨1+Cf+Temp*B,by positivity,?_⟩
  filter_upwards [HB] with n hn
  intro M hsource as ho T U hU s e hse
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbm : Monotone b:=comp_partitionPoint_monotone (toNNReal_monotoneOn had.1) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone (toNNReal_monotoneOn had.2.1) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone M.mass_mean_monotone as ho
  have hS0 j : 0 ≤ S j:=M.mass_mean_nonneg (partitionPoint_mem as ho j)
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (hS0 j))
  have hKm : Monotone K:=by
    intro j k hjk
    exact add_le_add (hhm hjk) (mul_le_mul (hbm hjk) (hSm hjk) (hS0 j) (NNReal.coe_nonneg _))
  have Hmean j : S j ≤ B*(M.xs+partitionPoint 0 as j) := by
    by_cases hz : partitionPoint 0 as j=0
    · simp only [S,hz,orderedPathS,orderedPathPair_zero]
      have hx:=M.hxs
      positivity
    · exact hn M _ ⟨lt_of_le_of_ne (partitionPoint_mem as ho j).1 (Ne.symm hz),
        (partitionPoint_mem as ho j).2⟩
  have Hclock j : K j ≤ (1+Cf+Temp*B)*(M.xs+partitionPoint 0 as j) := by
    have HC:=hsource _ (partitionPoint_mem as ho j)
    have Hmul:=mul_le_mul HC.1 (Hmean j) (hS0 j) hTemp
    have Hfield:=HC.2
    have Hpos : 0 ≤ M.xs+partitionPoint 0 as j:=add_nonneg M.hxs.le (partitionPoint_mem as ho j).1
    change h j ≤ Cf*(M.xs+partitionPoint 0 as j) at Hfield
    change b j*S j ≤ Temp*(B*(M.xs+partitionPoint 0 as j)) at Hmul
    dsimp only [K]
    nlinarith only [Hfield,Hmul,Hpos]
  exact native_full_scalar_gamma_abs_le_clock n T ho U hU K hKm hK0 s e hse (Hclock _)

end OAI.SKFluctuations.Cavity
