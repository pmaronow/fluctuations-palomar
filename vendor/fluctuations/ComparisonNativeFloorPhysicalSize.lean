module

public import ComparisonNativeFloorRawEnvelope
public import ComparisonNativeLogarithmicLoss

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

theorem comparison_floor_shift_log_le {N delta U : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hdelta : 0 ≤ delta)
    (hU : 0 < U) (hUlower : 1/N ≤ U) :
    Real.log ((1+N^(2*delta)*U)/(N^(2*delta)*U)) ≤ 2*Real.log N := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hpow : 1 ≤ N^(2*delta) := Real.one_le_rpow hN (by linarith)
  have hshift : 1/N ≤ N^(2*delta)*U := hUlower.trans (by nlinarith)
  have hs : 0 < N^(2*delta)*U := mul_pos (Real.rpow_pos_of_pos hNp _) hU
  have hinv : 1/(N^(2*delta)*U) ≤ N := by
    have hh := (div_le_iff₀ hNp).mp hshift
    exact (div_le_iff₀ hs).mpr (by nlinarith)
  have harg : (1+N^(2*delta)*U)/(N^(2*delta)*U) ≤ 2*N := by
    have he : (1+N^(2*delta)*U)/(N^(2*delta)*U)=1/(N^(2*delta)*U)+1 := by field_simp
    rw [he]
    linarith
  have hh := Real.log_le_log (div_pos (by linarith) hs) harg
  rw [Real.log_mul (by norm_num) hNp.ne'] at hh
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  norm_num at hlog2
  linarith

theorem comparison_floor_physical_cost {N delta margin gamma E d lam : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hdelta : 0 ≤ delta)
    (hmargin : 0 ≤ margin) (hgamma : 0 < gamma) (hE : 0 < E) (hE1 : E ≤ 1)
    (hd : 0 < d) (hlam : 0 < lam)
    (hlower : gamma*N^(-(2:ℝ)/3+margin)*d ≤ E) :
    2*lam*(comparisonConditionalScale N delta E lam)^2*N^(-delta)*comparisonSmallMass N E+
      4*d^3*Real.log N*N^delta*(comparisonSmallMass N E)^2*
        Real.log ((1+N^(2*delta)*comparisonSmallMass N E)/(N^(2*delta)*comparisonSmallMass N E)) ≤
      (2+(8/gamma^3)*(Real.log N)^2)*N^delta*E := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hU := comparisonSmallMass_pos hNp hE
  have hUlower : 1/N ≤ comparisonSmallMass N E := by
    unfold comparisonSmallMass
    exact one_div_le_one_div_of_le (mul_pos hNp hE) (by nlinarith)
  have hlg := comparison_floor_shift_log_le hN hlog hdelta hU hUlower
  have hmass := comparison_conditional_floor_mass_cost (delta:=delta) hNp hE hlam
  have hfloor := comparison_conditional_outer_floor_cost (delta:=delta) hNp hgamma hd hE hlower
  have hexp : N^(delta-3*margin) ≤ N^delta := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hbase : d^3*N^delta*(comparisonSmallMass N E)^2 ≤ (1/gamma^3)*N^delta*E := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 1/gamma^3)) hE.le
    exact hfloor.trans hh
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hlg0 : 0 ≤ Real.log ((1+N^(2*delta)*comparisonSmallMass N E)/(N^(2*delta)*comparisonSmallMass N E)) := by
    have hs : 0 < N^(2*delta)*comparisonSmallMass N E := by positivity
    exact (Real.log_pos ((lt_div_iff₀ hs).mpr (by linarith))).le
  have hh := mul_le_mul hbase hlg hlg0 (show 0 ≤ (1/gamma^3)*N^delta*E by positivity)
  have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*Real.log N by positivity)
  linear_combination ht + 2*hmass

theorem comparison_floor_physical_cost_eventually {delta margin gamma K C : ℝ}
    (hdelta : 0 < delta) (hmargin : 0 ≤ margin) (hgamma : 0 < gamma)
    (hK : 0 ≤ K) :
    ∀ᶠ N : ℝ in atTop, ∀ E d lam : ℝ, 0 < E → E ≤ 1 → 0 < d → 0 < lam →
      gamma*N^(-(2:ℝ)/3+margin)*d ≤ E →
      (K*C^2+1)*(2*lam*(comparisonConditionalScale N delta E lam)^2*N^(-delta)*comparisonSmallMass N E+
        4*d^3*Real.log N*N^delta*(comparisonSmallMass N E)^2*
          Real.log ((1+N^(2*delta)*comparisonSmallMass N E)/(N^(2*delta)*comparisonSmallMass N E))) ≤ N^(2*delta)*E := by
  have ht := comparison_log_loss_eventually (C:=(K*C^2+1)*(2+8/gamma^3)) (p:=2) (by positivity) hdelta
  have hl := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [ht,hl,eventually_ge_atTop (1:ℝ)] with N hcoef hlog hN
  intro E d lam hE hE1 hd hlam hlower
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hb := comparison_floor_physical_cost hN hlog hdelta.le hmargin hgamma hE hE1 hd hlam hlower
  have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ K*C^2+1 by positivity)
  have hlog2 : 1 ≤ (Real.log N)^2 := by nlinarith
  have hco : (K*C^2+1)*(2+(8/gamma^3)*(Real.log N)^2) ≤ N^delta := by
    have hm := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 2*(K*C^2+1) by positivity)
    have hc : (K*C^2+1)*(2+8/gamma^3)*(Real.log N)^2 ≤ N^delta := by
      simpa only [Real.rpow_two] using hcoef
    linear_combination hc + hm
  have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hco (Real.rpow_pos_of_pos hNp delta).le) hE.le
  have he : N^delta*N^delta*E=N^(2*delta)*E := by rw [←Real.rpow_add hNp];congr 2;ring
  rw [he] at ht
  nlinarith

theorem actual_comparison_floor_error_eventually {delta margin gamma K C : ℝ}
    (hdelta : 0 < delta) (hmargin : 0 ≤ margin) (hgamma : 0 < gamma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∀ᶠ N : ℝ in atTop, ∀ (m : NativeBandModel) (F : Set ℝ), m.N=N → m.delta=delta →
      MeasurableSet F → m.U=comparisonSmallMass N m.E → m.E ≤ 1 →
      gamma*N^(-(2:ℝ)/3+margin)*m.d ≤ m.E →
      (∀ᵐ r,r ∈ Icc (0:ℝ) 1 → r ∈ F → deriv m.alpha.val.val r=comparisonFloor N delta m.U r) →
      (∀u ∈ Ioc (0:ℝ) 1,orderedPathB (m.n+1) m.bf m.hf u ≤ K*(m.xs+u)^2) →
      (∀r ∈ Icc (0:ℝ) 1,r ∈ F → m.xs+m.alpha.val.val r ≤ C*(comparisonConditionalScale N delta m.E m.lam+r)) →
      (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (m.R u)*m.comparisonErrorDensity u) ≤ N^(2*delta)*m.E := by
  filter_upwards [comparison_floor_physical_cost_eventually (C:=C) hdelta hmargin hgamma hK]
    with N hcost
  intro m F hN hdelt hF hU hE1 hlower hfloor hB hscale
  have hNp : 0 < N := hN ▸ zero_lt_one.trans_le m.hN
  have hb := actual_comparison_floor_error_of_normalized_B m F hF
    (comparison_conditional_scale_pos (delta:=delta) hNp m.hE m.hlam).le hK hC
    (by simpa only [hN,hdelt] using hfloor) hB hscale
  have hc := hcost m.E m.d m.lam m.hE hE1 m.hd m.hlam hlower
  simpa only [hN,hdelt,hU] using hb.trans (by simpa only [hN,hdelt,hU] using hc)

end OAI.SKFluctuations.LaplaceWindowFormalization
