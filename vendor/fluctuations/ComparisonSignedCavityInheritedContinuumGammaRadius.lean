module

public import ComparisonSignedCavityInheritedContinuumGammaUpper
public import ComparisonSignedCavityContinuumMixedClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 4000000

theorem eventually_actual_minimum_inherited_continuum_scalar_gamma_radius_bound
    (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf →
      ∀(as : List PositiveMass),MassOrdered 0 as →
      ∀(tree : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U →
      ∀a c : tree.Slot,a≠c →
        let v:=M.R (partitionPoint 0 as (tree.splitIndex a c))
        M.xs ≤ v → M.z ≤ v →
        |fullScalarCutGamma tree U (nativeContinuumMixedClock n M.bf M.hf as) a c| ≤ Cg*v := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_continuum_scalar_gamma_mass_bound
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg*(1+cu),by positivity,?_⟩
  filter_upwards [HG] with n hn
  intro M hsource as ho tree U hU a c hac
  dsimp only
  intro hxv hzv
  have H:=hn M hsource as ho tree U hU a c hac
  let u:=partitionPoint 0 as (tree.splitIndex a c)
  let v:=M.R u
  have hu:=partitionPoint_mem as ho (tree.splitIndex a c)
  have hv:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hmass : u ≤ cu*v:=by
    have Hreg:=(M.regular v ⟨hzv,hv.2⟩).2
    rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha hu] at Hreg
    exact Hreg
  apply H.trans
  have Hsum : M.xs+u ≤ (1+cu)*v:=by linarith only [hxv,hmass]
  exact (mul_le_mul_of_nonneg_left Hsum hCg.le).trans_eq (by ring)

end OAI.SKFluctuations.Cavity
