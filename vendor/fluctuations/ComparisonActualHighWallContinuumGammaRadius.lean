module

public import ComparisonActualHighWallStarPreparatory
public import ComparisonActualHighWallSourceClockBudget
public import ComparisonSignedCavityActualContinuumGammaUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_continuum_scalar_gamma_mass_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0<Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(as : List PositiveMass),MassOrdered 0 as →
      ∀(T : ClockTree (Spin n×Bool) as) (U : ℕ),0<U →
      ∀s e : T.Slot,s≠e →
        |fullScalarCutGamma T U (nativeContinuumMixedClock n M.bf M.hf as) s e| ≤
          Cg*(M.xs+partitionPoint 0 as (T.splitIndex s e)) := by
  obtain ⟨B,hB,HB⟩:=eventually_actual_high_wall_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Temp:=max Bclock 0
  have hTemp : 0≤Temp:=le_max_right _ _
  refine ⟨2+Temp*B,by positivity,?_⟩
  filter_upwards [HB] with n hn
  intro M hwork as ho T U hU s e hse
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.data.bf_monotone M.alpha hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (M.data.hf_monotone M.alpha hu hv huv)) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone M.mass_mean_monotone as ho
  have hS0 j : 0≤S j:=M.mass_mean_nonneg (partitionPoint_mem as ho j)
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (hS0 j))
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (hS0 i) (NNReal.coe_nonneg _))
  have Hmean j : S j≤B*(M.xs+partitionPoint 0 as j):=by
    by_cases hz : partitionPoint 0 as j=0
    · simp only [S,hz,orderedPathS,orderedPathPair_zero]
      simpa only [add_zero] using mul_nonneg hB.le M.hxs.le
    · exact hn M _ ⟨lt_of_le_of_ne (partitionPoint_mem as ho j).1 (Ne.symm hz),
        (partitionPoint_mem as ho j).2⟩
  have Hclock j : K j≤(2+Temp*B)*(M.xs+partitionPoint 0 as j):=by
    have HC:=M.data.small_source_clock_budget M.alpha hwork.ge (partitionPoint_mem as ho j)
    have Hb : b j≤Temp:=HC.1.trans (M.hT.trans (le_max_left _ _))
    have Hmul:=mul_le_mul Hb (Hmean j) (hS0 j) hTemp
    have Hpos : 0≤M.xs+partitionPoint 0 as j:=add_nonneg M.hxs.le (partitionPoint_mem as ho j).1
    have Hfield:=HC.2
    change h j≤M.xs+partitionPoint 0 as j at Hfield
    dsimp only [K]
    nlinarith only [Hfield,Hmul,Hpos]
  exact native_full_scalar_gamma_abs_le_clock n T ho U hU K hKm hK0 s e hse (Hclock _)

theorem eventually_actual_high_wall_continuum_scalar_gamma_radius_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0<Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(as : List PositiveMass),MassOrdered 0 as →
      ∀(T : ClockTree (Spin n×Bool) as) (U : ℕ),0<U →
      ∀s e : T.Slot,s≠e →
        let v:=M.data.wallRadius M.alpha (partitionPoint 0 as (T.splitIndex s e))
        M.xs≤v → M.z≤v →
        |fullScalarCutGamma T U (nativeContinuumMixedClock n M.bf M.hf as) s e| ≤ Cg*v := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_continuum_scalar_gamma_mass_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg*(1+cu),by positivity,?_⟩
  filter_upwards [HG] with n hn
  intro M hwork as ho T U hU s e hse
  dsimp only
  intro hxv hzv
  let u:=partitionPoint 0 as (T.splitIndex s e)
  let v:=M.data.wallRadius M.alpha u
  have hu:=partitionPoint_mem as ho (T.splitIndex s e)
  have hv:=M.data.wallRadius_bounds M.alpha u
  have hrmin : M.data.rmin<v:=by
    have H:=M.data.hrbounds.2.1
    rw [hwork] at hxv
    dsimp only [v] at *
    nlinarith only [H,hxv,M.data.hd]
  have hhigh : M.data.s≤u:=(M.data.wallRadius_high_mass M.alpha hrmin).le
  have hmass : u≤cu*v:=by
    have H:=(M.regular v ⟨hzv,hv.2⟩).2
    rw [M.data.wallRadius_spec M.alpha ⟨hhigh,hu.2⟩] at H
    exact H
  have H:=hn M hwork as ho T U hU s e hse
  have Hsum : M.xs+u≤(1+cu)*v:=by linarith only [hxv,hmass]
  exact H.trans ((mul_le_mul_of_nonneg_left Hsum hCg.le).trans_eq (by ring))

end OAI.SKFluctuations.Cavity
