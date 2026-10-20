module

public import ComparisonActualHighWallOriginalTaylorLocalThermalAlong
public import ComparisonActualHighWallOriginalFreshHighContractionAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000

theorem eventually_actual_high_wall_original_target_Taylor_saved_local_thermal_profile_along
    (dOrder : ℕ) (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p)
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Ccut c : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcout : cu*Az < c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U : ℕ,i < U → U ≤ as.length → Ccut*(M n).data.d ≤ 1 →
          partitionPoint 0 as U ≤ Ccut*(M n).data.d → 2*c*(M n).data.d ≤ partitionPoint 0 as U →
        let di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)
        |actualGeneralTargetOriginalTaylorPart (n:=dim n) (M n).bf (M n).hf as i U| ≤
          C*((M n).data.d^2*di+(M n).data.d*
              (∫u in 0..Ccut*(M n).data.d,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
                (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))+(M n).data.N^(-(actualMassSavingExponent m delta/256))*(M n).data.d^3) := by
  obtain ⟨C,hC,HT⟩:=eventually_actual_high_wall_original_target_Taylor_local_thermal_profile_along
    (D:=D) dOrder hd p hp hOrder Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim
  have HH:=eventually_actual_high_wall_original_fresh_HIGH_profile_contraction_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout dim hdim M (fun n=>(hfixed n).le) hdlim hsRatio
  refine ⟨C,hC,?_⟩
  filter_upwards [HT,HH] with n hnT hnH
  intro L us hus hret hmesh
  filter_upwards [hnT (M n) (hfixed n) L us hus hret hmesh,hnH] with jGrid hjT hjH
  dsimp only at hjT ⊢
  intro i U hi hU hcut1 hcut hcutlo
  have HB:=hjT i U hi hU hcut1 hcut
  have HP:=hjH us hus i U hi hU hcutlo (4/p) htheta1 htheta2 hdeficit 0
  have Hprice:=mul_le_mul_of_nonneg_left HP (mul_nonneg hC.le (M n).data.hd.le)
  apply HB.trans
  nlinarith only [Hprice]

end OAI.SKFluctuations.Cavity
