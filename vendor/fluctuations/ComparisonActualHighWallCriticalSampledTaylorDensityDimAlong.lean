module

public import ComparisonActualHighWallCriticalSampledTaylorDensityAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000

theorem actual_high_wall_original_sampled_site_over_square_dim_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d) :
    Tendsto (fun n=>3/(((dim n+1:ℕ):ℝ)*(M n).data.d^2)) atTop (𝓝 0) := by
  have Hpow : Tendsto (fun n=>3*C0^6*((dim n+1:ℕ):ℝ)^(-6*m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,neg_mul] using
      (((tendsto_rpow_neg_atTop (by positivity : 0 < 6*m)).comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))).const_mul (3*C0^6))
  apply squeeze_zero' (Eventually.of_forall (fun n=>by positivity)) ?_ Hpow
  filter_upwards [] with n
  have hd1 : (M n).data.d ≤ 1:=(M n).data.hd1
  have hd4 : (M n).data.d^4 ≤ 1:=pow_le_one₀ (M n).data.hd.le hd1
  have hd6 : (M n).data.d^6 ≤ (M n).data.d^2 := by
    have HH:=mul_le_mul_of_nonneg_left hd4 (sq_nonneg (M n).data.d)
    nlinarith only [HH]
  have Hcritical:=(M n).high_mass_inverse_power hC0 6
  rw [hfixed n] at Hcritical
  norm_num only [Nat.cast_ofNat,div_self (by norm_num : (6:ℝ) ≠ 0),
    Real.rpow_one] at Hcritical
  have Hle : 1/((M n).data.N*(M n).data.d^2) ≤
      1/((M n).data.N*(M n).data.d^6) :=
    div_le_div_of_nonneg_left zero_le_one
      (by have :=(M n).data.hd; have :=(M n).data.hN; positivity)
      (mul_le_mul_of_nonneg_left hd6 (M n).data.hN.le)
  have Hmul:=mul_le_mul_of_nonneg_left (Hle.trans Hcritical)
    (by norm_num : (0:ℝ) ≤ 3)
  convert Hmul using 1 <;> ring

theorem actual_high_wall_critical_sampled_initial_radius_dim_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Ccut : ℝ}
    (hCcut : 0 < Ccut)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∃eps : ℕ→ℝ,Tendsto eps atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1)→
        ∀ᶠjGrid : ℕ in atTop,
          let as:=finiteCutMasses us jGrid
          ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ Ccut*(M n).data.d →
            ClockTree.edgeBudget 0 as
              (fun j=>if j<U then nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as j+
                1/(dim n+1:ℕ) else 0) ≤ eps n*(M n).data.d^2 := by
  let J:=fun n=>∫u in 0..Ccut*(M n).data.d,
    Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
      (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)
  let eps:=fun n=>J n/(M n).data.d^2+
    3/(((dim n+1:ℕ):ℝ)*(M n).data.d^2)
  have Hthermal:=ActualHighWallOverlapMinimum.actual_high_wall_critical_thermal_radius_tendsto_zero_along
    hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hdlim hsRatio
  have Hsite:=actual_high_wall_original_sampled_site_over_square_dim_tendsto_zero hm hC0 dim hdim M hfixed
  have Heps : Tendsto eps atTop (𝓝 0) := by
    have HH:=Hthermal.add Hsite
    simpa only [eps,J,id_eq,zero_add] using HH
  have Hcut : ∀ᶠn in atTop,Ccut*(M n).data.d≤1 := by
    filter_upwards [hdlim.eventually (eventually_le_nhds
      (show (0:ℝ) < 1/Ccut by positivity))] with n hn
    calc
      Ccut*(M n).data.d ≤ Ccut*(1/Ccut) := mul_le_mul_of_nonneg_left hn hCcut.le
      _ = 1 := by field_simp
  refine ⟨eps,Heps,?_⟩
  filter_upwards [Hcut] with n hncut
  intro us hus
  have Hgrid:=actual_high_wall_original_sampled_initial_radius_le_thermal
    (M n) hCcut.le hncut us hus
  filter_upwards [Hgrid] with jGrid hj
  dsimp only at hj ⊢
  intro U hU hmass
  have H:=hj U hU hmass
  have hd:=(M n).data.hd
  have HEq : eps n*(M n).data.d^2=J n+3/(dim n+1:ℕ) := by
    dsimp only [eps,J]
    field_simp
  rw [HEq]
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
