module

public import ComparisonSignedCavityJointLowRestorationAdditivity
public import ComparisonSignedCavityOriginalGRestorationLinearity
public import ComparisonSignedCavityActualOriginalGLowAllocation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem native_centered_low_gamma_HIGH_ledger_test_linear (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (α β : ℝ) :
    nativeCenteredLowGammaHighLedger n q U b h K S T (fun σ=>α*P σ+β*Q σ) a z=
      α*nativeCenteredLowGammaHighLedger n q U b h K S T P a z+
      β*nativeCenteredLowGammaHighLedger n q U b h K S T Q a z := by
  have HI (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      insertedRestTest (fun σ=>α*P σ+β*Q σ) (restCenteredLowKernel n U b S) p r=
      fun σ=>α*insertedRestTest P (restCenteredLowKernel n U b S) p r σ+
        β*insertedRestTest Q (restCenteredLowKernel n U b S) p r σ:=by
    funext σ
    unfold insertedRestTest
    ring
  unfold nativeCenteredLowGammaHighLedger
  simp_rw [HI,retained_signed_jets_add_test,retained_signed_jets_const_mul_test]
  simp only [mul_add,List.sum_map_add,mul_left_comm,List.sum_map_mul_left,add_div]
  ring

theorem native_centered_low_gamma_HIGH_second_test_linear (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (α β : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeCenteredLowGammaHighSecondRemainder n q U b h K S T (fun σ=>α*P σ+β*Q σ) a z=
      α*nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z+
      β*nativeCenteredLowGammaHighSecondRemainder n q U b h K S T Q a z := by
  have HP:=native_centered_low_gamma_high_path_taylor n q U b h K S T ho P a z hq0 hq hb hh hK hbm hhm hKm
  have HQ:=native_centered_low_gamma_high_path_taylor n q U b h K S T ho Q a z hq0 hq hb hh hK hbm hhm hKm
  have HC:=native_centered_low_gamma_high_path_taylor n q U b h K S T ho (fun σ=>α*P σ+β*Q σ) a z hq0 hq hb hh hK hbm hhm hKm
  have HL t : nativeCenteredLowGammaHighPath n q U b h K S T (fun σ=>α*P σ+β*Q σ) a z t=
      α*nativeCenteredLowGammaHighPath n q U b h K S T P a z t+
      β*nativeCenteredLowGammaHighPath n q U b h K S T Q a z t:=by
    have HA:=native_low_gamma_at_full_clock_add n (cutFullVariance n q U 0 t b h K) U b K S T
      (fun σ=>α*P σ) (fun σ=>β*Q σ) a z
    rw [native_low_gamma_at_full_clock_const_mul,native_low_gamma_at_full_clock_const_mul] at HA
    exact HA
  have Hledger:=native_centered_low_gamma_HIGH_ledger_test_linear n q U b h K S T P Q a z α β
  linear_combination -HC+α*HP+β*HQ+HL 1-HL 0-Hledger

theorem native_original_four_G_LOW_restoration_test_linear (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P Q : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (α β : ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalGKernelLowRestoration n q U b h K S T (fun σ=>α*P σ+β*Q σ) a z
      (restCenteredLowKernel n U b S)=
      α*nativeOriginalGKernelLowRestoration n q U b h K S T P a z (restCenteredLowKernel n U b S)+
      β*nativeOriginalGKernelLowRestoration n q U b h K S T Q a z (restCenteredLowKernel n U b S) := by
  have HI (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      insertedRestTest (fun σ=>α*P σ+β*Q σ) (restCenteredLowKernel n U b S) p r=
      fun σ=>α*insertedRestTest P (restCenteredLowKernel n U b S) p r σ+
        β*insertedRestTest Q (restCenteredLowKernel n U b S) p r σ:=by
    funext σ
    unfold insertedRestTest
    ring
  unfold nativeOriginalGKernelLowRestoration
  simp_rw [HI,native_original_high_pair_restoration_test_linear n q U b h K S _ ho _ _ _ _ α β
    hq0 hq hb hh hK hbm hhm hKm]
  simp only [mul_add,List.sum_map_add,mul_left_comm,List.sum_map_mul_left,add_div]
  ring

end OAI.SKFluctuations.Cavity
