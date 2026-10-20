module

public import ComparisonNativeBroadError
public import ComparisonPhysicalLedgerAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

def comparisonNearZeroCoefficient (K Cx Az cl : ℝ) : ℝ :=
  8*(K*(Cx+8)^2+(Az*Cx+8/cl)^2)

theorem comparison_near_zero_physical_cost {N delta E lam xs K Cx Az cl : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam) (hxs : 0 ≤ xs)
    (hK : 0 ≤ K) (hCx : 0 ≤ Cx) (hAz : 0 ≤ Az) (hcl : 0 < cl)
    (hxsA : xs ≤ Cx*comparisonConditionalScale N delta E lam)
    (hUA : comparisonSmallMass N E ≤ comparisonConditionalScale N delta E lam) :
    8*lam*comparisonSmallMass N E*
      (K*(xs+8*comparisonSmallMass N E)^2+(Az*xs+8*comparisonSmallMass N E/cl)^2) ≤
      comparisonNearZeroCoefficient K Cx Az cl*N^(2*delta)*E := by
  let A := comparisonConditionalScale N delta E lam
  have hA : 0 < A := comparison_conditional_scale_pos hN hE hlam
  have hU := comparisonSmallMass_pos hN hE
  have hfirst : xs+8*comparisonSmallMass N E ≤ (Cx+8)*A := by dsimp [A];linarith
  have hsecond : Az*xs+8*comparisonSmallMass N E/cl ≤ (Az*Cx+8/cl)*A := by
    have hx := mul_le_mul_of_nonneg_left hxsA hAz
    have hu := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hUA (by norm_num : (0:ℝ) ≤ 8)) hcl.le
    calc
      _ ≤ Az*(Cx*comparisonConditionalScale N delta E lam)+8*comparisonConditionalScale N delta E lam/cl := add_le_add hx hu
      _ = _ := by dsimp [A];ring
  have hsq1 := pow_le_pow_left₀ (by positivity : 0 ≤ xs+8*comparisonSmallMass N E) hfirst 2
  have hsq2 := pow_le_pow_left₀ (by positivity : 0 ≤ Az*xs+8*comparisonSmallMass N E/cl) hsecond 2
  have hbracket : K*(xs+8*comparisonSmallMass N E)^2+(Az*xs+8*comparisonSmallMass N E/cl)^2 ≤
      (K*(Cx+8)^2+(Az*Cx+8/cl)^2)*A^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq1 hK
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ 8*lam*comparisonSmallMass N E by positivity)
  have he := comparison_conditional_small_mass_cost (delta:=delta) hN hE hlam
  change lam*A^2*comparisonSmallMass N E=N^(2*delta)*E at he
  apply hm.trans_eq
  calc
    _ = (8*(K*(Cx+8)^2+(Az*Cx+8/cl)^2))*(lam*A^2*comparisonSmallMass N E) := by ring
    _ = _ := by rw [he];unfold comparisonNearZeroCoefficient;ring

theorem actual_native_near_zero_error_eventually {delta K Cx Az cl : ℝ}
    (hdelta : 0 < delta) (hK : 0 ≤ K) (hCx : 0 ≤ Cx) (hAz : 0 ≤ Az) (hcl : 0 < cl) :
    ∀ᶠ N : ℝ in atTop, ∀ (m : NativeBandModel) (z0 : ℝ),
      m.N=N → m.delta=delta → m.U=comparisonSmallMass m.N m.E →
      m.xs ≤ Cx*comparisonConditionalScale m.N m.delta m.E m.lam →
      m.U ≤ comparisonConditionalScale m.N m.delta m.E m.lam →
      z0 ∈ Icc (0:ℝ) 1 → z0 ≤ Az*m.xs →
      (∀r∈Icc z0 1,cl*r ≤ m.alpha.val.val r) →
      (∀u∈Ioc (0:ℝ) 1,orderedPathB (m.n+1) m.bf m.hf u ≤ K*(m.xs+u)^2) →
      (∫u in 0..1,(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
        N^(3*delta)*m.E := by
  have hc : 0 ≤ comparisonNearZeroCoefficient K Cx Az cl := by unfold comparisonNearZeroCoefficient;positivity
  filter_upwards [comparison_log_loss_eventually (p:=0) hc hdelta,eventually_ge_atTop (1:ℝ)] with N hcoef hN
  intro m z0 hNeq hdeq hUeq hxsA hUA hz hzxs hregular hB
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have ha := actual_native_near_zero_error_of_normalized_B m hK hcl hAz hz hzxs hregular hB
  have hb := comparison_near_zero_physical_cost (zero_lt_one.trans_le m.hN) m.hE m.hlam
    m.hxs.le hK hCx hAz hcl hxsA (hUeq ▸ hUA)
  rw [←hUeq] at hb
  have hstep := ha.trans hb
  rw [hNeq,hdeq] at hstep
  simp only [Real.rpow_zero,mul_one] at hcoef
  have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ N^(2*delta)*m.E by have hE:=m.hE;positivity)
  have he : N^delta*(N^(2*delta)*m.E)=N^(3*delta)*m.E := by
    rw [←mul_assoc,←Real.rpow_add hNp]
    congr 2
    ring
  rw [he] at hh
  exact hstep.trans (by nlinarith)

end OAI.SKFluctuations.LaplaceWindowFormalization
