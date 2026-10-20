module

public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000

 theorem eventually_actual_original_thermal_norm_upper_along_original_q
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualThetaZeroOverlapMinimum.OriginalQComparableBandContext M T)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃Cd : ℝ,0 < Cd ∧ ∀ᶠn in atTop,∀u∈Ioc (0:ℝ) 1,u ≤ A*(M n).xs →
      Real.sqrt (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2) ≤ Cd*(M n).xs := by
  obtain ⟨K,hK,Hraw⟩:=eventually_actual_B_normalized_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cd:=Real.sqrt K*(1+A)
  have hCd : 0 < Cd:=mul_pos (Real.sqrt_pos.2 hK) (by linarith only [hA])
  refine ⟨Cd,hCd,?_⟩
  filter_upwards [((tendsto_add_atTop_nat 1).comp hdim).eventually Hraw,G.eventually_geometric_gates_original_q] with n hn hngate u hu huA
  have H:=hn (M n) hngate.2 hngate.1 u hu
  dsimp only [Function.comp_def] at H
  have HX : 0 ≤ (M n).xs+u:=add_nonneg (M n).hxs.le hu.1.le
  calc
    _ ≤ Real.sqrt (K*((M n).xs+u)^2) := Real.sqrt_le_sqrt (by linarith only [H,sq_nonneg (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)])
    _ = Real.sqrt K*((M n).xs+u) := by rw [Real.sqrt_mul hK.le,Real.sqrt_sq_eq_abs,abs_of_nonneg HX]
    _ ≤ Real.sqrt K*((1+A)*(M n).xs) := mul_le_mul_of_nonneg_left (by linarith only [huA]) (Real.sqrt_nonneg K)
    _ = Cd*(M n).xs := by dsimp only [Cd];ring

end OAI.SKFluctuations.LaplaceWindowFormalization
