module

public import ComparisonSignedCavityScalarMeanClockBudget
public import ComparisonSignedCavityObservedProjectedReplacement

@[expose] public section

noncomputable section
set_option maxHeartbeats 6000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy LaplaceWindowFormalization
namespace Cavity

theorem native_full_scalar_gamma_abs_le_clock (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U : ℕ) (hU : 0 < U) (K : ℕ→ℝ) (hKm : Monotone K) (hK0 : ∀j,0 ≤ K j)
    (s e : T.Slot) (hse : s≠e) {C v : ℝ} (hclock : K (T.splitIndex s e) ≤ C*v) :
    |fullScalarCutGamma T U K s e| ≤ C*v := by
  have hm := relocatedClock_monotone U (show (0:ℝ)∈Icc 0 1 by norm_num) hKm hK0
  have hz : relocatedClock U 0 K 0=0 := by simp [relocatedClock,hU]
  have hneq : T.cavityRightSlot s≠T.cavityRightSlot e :=
    fun h=>hse (T.cavityRightSlot.injective h)
  have H := actual_scalar_distinct_pair_abs_le T.cavityRight ho (relocatedClock U 0 K)
    hm hz _ _ hneq (C:=C) (v:=v) (by
      rw [T.splitIndex_cavityRight]
      exact (relocatedClock_le U (by norm_num) hK0 _).trans hclock)
  simpa only [fullScalarCutGamma,fullScalarCutMoment,scalarCutMoment,List.map_cons,List.map_nil,
    ClockTree.slotProduct,scalarFeature_apply_spin,mul_one,one_mul,Pi.zero_def] using H

end Cavity
namespace LaplaceWindowFormalization
open Cavity

theorem eventually_actual_minimum_bare_scalar_gamma_bound
    (Bclock Temp : ℝ) (hT : 0 ≤ Temp) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as := finiteCutMasses us k
        ∀(tree : ClockTree (Spin n×Bool) as) (U : ℕ),0 < U →
        ∀s e : tree.Slot,s≠e →
        let v := M.R (partitionPoint 0 as (tree.splitIndex s e))
        M.xs ≤ v → M.z ≤ v →
        |fullScalarCutGamma tree U (retainedStarMixedClock n M.bf M.hf as) s e| ≤ Cg*v := by
  obtain ⟨Cs,Ck,_,hCk,H⟩ := eventually_actual_minimum_bare_finite_mean_clock_bounds
    (D:=D) Bclock Temp hT hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ck*(1+cu),by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  let as := finiteCutMasses us k
  have ho := finiteCutMasses_ordered us hus k
  intro tree U hU s e hse hxv hzv
  let j := tree.splitIndex s e
  let v := M.R (partitionPoint 0 as j)
  have hj : j ≤ as.length := tree.splitIndex_le_clockLength s e
  have hv := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha (partitionPoint 0 as j)
  have hmass : partitionPoint 0 as j ≤ cu*v := by
    have Hreg := (M.regular v ⟨hzv,hv.2⟩).2
    rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mem as ho j)] at Hreg
    exact Hreg
  have hbound : retainedStarMixedClock n M.bf M.hf as j ≤ (Ck*(1+cu))*v := by
    have H := (hk j hj).2
    have Hsum : M.xs+partitionPoint 0 as j ≤ (1+cu)*v := by dsimp only [v,j] at *;linarith
    exact H.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hsum hCk.le)
  have had := comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le
    M.hlb M.hb M.hh M.hh0 M.alpha
  exact native_full_scalar_gamma_abs_le_clock n tree ho U hU _
    (retainedStarMixedClock_monotone n M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) as ho)
    (retainedStarMixedClock_nonneg n M.bf M.hf as) s e hse hbound

end LaplaceWindowFormalization
end OAI.SKFluctuations
