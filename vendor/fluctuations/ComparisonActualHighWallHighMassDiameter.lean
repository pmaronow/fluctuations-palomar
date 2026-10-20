module

public import ComparisonActualHighWallHighMassNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem highMassDiameter_square_bound
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {Cdiam c v : ℝ} (hCdiam : 0 ≤ Cdiam) (hc : 0 < c) (hv : 0 < v)
    (hvlo : c*a.data.d ≤ v) :
    (a.highMassDiameter Cdiam v)^2*(a.data.d^2/a.xs^4) ≤
      (2*Cdiam*Ct*C0^3/c)^2*(Real.log a.data.N)^4*a.data.N^(-2*(3*m+delta)) := by
  let W := a.data.d
  let diam := a.highMassDiameter Cdiam v
  let C := 2*Cdiam*Ct*C0^3
  let L := Real.log a.data.N
  have hW : 0 < W := a.data.hd
  have hx := a.hxs
  have hN0 := a.data.hN
  have hE := a.data.hE
  have hd := a.data.hd
  have hL : 0 ≤ L := zero_le_one.trans hlog
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdiam : 0 ≤ diam := by dsimp [diam,highMassDiameter]; positivity
  have Hsource := a.highMassDiameter_source_power_le hN hlog hnd hCt hC0 hxs1 hCdiam hv
  have Hratio : W/v ≤ 1/c := (div_le_div_iff₀ hv hc).mpr (by simpa only [one_mul,mul_one,mul_comm,W] using hvlo)
  have Hmul := mul_le_mul_of_nonneg_right Hsource (show 0 ≤ W/a.xs^2 by positivity)
  have HE : (C*L^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)))*(W/a.xs^2)=
      C*L^2*a.data.N^(-(3*m+delta))*(W/v) := by field_simp
  change diam*(W/a.xs^2) ≤ (C*L^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)))*(W/a.xs^2) at Hmul
  rw [HE] at Hmul
  have Hupper : diam*W/a.xs^2 ≤ (C/c)*L^2*a.data.N^(-(3*m+delta)) := by
    have HH := mul_le_mul_of_nonneg_left Hratio
      (show 0 ≤ C*L^2*a.data.N^(-(3*m+delta)) by positivity)
    have HHmul : diam*W/a.xs^2 ≤ C*L^2*a.data.N^(-(3*m+delta))*(W/v) := by
      simpa only [mul_div_assoc] using Hmul
    apply HHmul.trans
    convert HH using 1
    ring
  have Hsq := pow_le_pow_left₀ (show 0 ≤ diam*W/a.xs^2 by positivity) Hupper 2
  have HEN : (a.data.N^(-(3*m+delta)))^2=a.data.N^(-2*(3*m+delta)) := by
    rw [←Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  rw [mul_pow,mul_pow,HEN] at Hsq
  have Hlhs : (diam*W/a.xs^2)^2=diam^2*(W^2/a.xs^4) := by field_simp
  rw [Hlhs,show (L^2)^2=L^4 by ring] at Hsq
  exact Hsq

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_high_mass_diameter_square_polynomial_le
    {m delta cl cu Az C0 Ct D Bclock c Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hc : 0 < c) (hCdiam : 0 ≤ Cdiam) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ a.data.d → ∀v : ℝ,c*a.data.d ≤ v →
          (a.highMassDiameter Cdiam v)^2*(a.data.d^2/a.xs^4) ≤
            a.data.N^(-(32*actualMassSavingExponent m delta)) := by
  have Hb := actualMassSavingExponent_bounds m delta
  have Hroom : 32*actualMassSavingExponent m delta < 2*(3*m+delta) := by
    nlinarith [Hb.2.1,actualMassSavingExponent_pos hm hdelta]
  have Hrate := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay Hroom 4 ((2*Cdiam*Ct*C0^3/c)^2))
  have Hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  filter_upwards [Hrate,Hdepth,Hlog] with n hn hdepth hlog
  intro a hxsD v hvlo
  have hN : 1 ≤ a.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_pos n
  have hnd : 1/a.data.N ≤ a.data.d :=
    ((hdepth a.data.E a.data.d a.data.hE a.data.hd a.hlower).trans a.hscale).trans hxsD
  have hv : 0 < v := (mul_pos hc a.data.hd).trans_le hvlo
  exact (a.highMassDiameter_square_bound hN hlog hnd hCt hC0
    (hxsD.trans a.data.hd1) hCdiam hc hv hvlo).trans (by simpa only [neg_mul] using hn)

end OAI.SKFluctuations.LaplaceWindowFormalization
