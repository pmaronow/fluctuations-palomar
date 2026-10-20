module

public import ComparisonOriginalQOuterVarianceScalarDraft
public import ComparisonOriginalQOuterTraceGeometryImportFirstDraft
public import ComparisonNativeActualHighMassDiameter
public import ComparisonConditionalOptimizedSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem outer_truncated_variance_atom_optimized_rate_corrected_c0_isolated_draft
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0)
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hL : 1 ≤ Real.log Q.data.N)
    {lo K v : ℝ} (hK : 4 ≤ K)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hgroup : (cl/(4*cu))*lo ≤ v)
    (q : ℝ) :
    let z := min (K*v) 1
    let H := 2/cl+K
    let J := max 1 ((Az+1/cl)*H)
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    let ez := laplaceComparisonStrength Q.data.d Q.lam
      (Q.shiftedNativeModel.R z)
    e*(K*v)*(2*((q^2*(Q.xs+z))/
      (Q.data.N*ez*(K*v)^2))^((2:ℝ)/3)) ≤
      (2*C0)*(q^2*H*J)^((2:ℝ)/3)*
        Q.data.N^(-m)*(2*Real.log Q.data.N)^((1:ℝ)/3)*Q.data.E := by
  let z := min (K*v) 1
  let H := 2/cl+K
  let J := max 1 ((Az+1/cl)*H)
  let e := laplaceComparisonStrength Q.data.d Q.lam v
  let ez := laplaceComparisonStrength Q.data.d Q.lam
    (Q.shiftedNativeModel.R z)
  have hxs := Q.outer_trace_import_first_carrier_le_group_draft
    hcl hcu hAz houter hgroup
  have hz : z ≤ K*v := min_le_left _ _
  have hheight : Q.xs+z ≤ H*v := by
    dsimp only [H]
    linarith only [hxs,hz]
  have hshape : e ≤ J*ez := by
    simpa only [z,H,J,e,ez] using
      (Q.outer_trace_import_first_endpoint_strength_le_draft
        hcl hAz (K:=K) (H:=2/cl)
        (by linarith) (by positivity) hv hxs)
  have he : 0 ≤ e := (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
  have hez : 0 < ez := laplaceComparisonStrength_pos Q.data.d Q.hlam _
  have hy : 0 ≤ Q.xs+z := by
    have hz0 : 0 ≤ z := le_min
      (mul_nonneg (by linarith : 0 ≤ K) hv.1.le) zero_le_one
    exact add_nonneg Q.hxs.le hz0
  have hJ : 0 ≤ J := zero_le_one.trans (le_max_left _ _)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hscalar := OriginalQOuterVarianceDraft.literal_variance_atom_le_outer_cube_root_draft
      (N:=Q.data.N) (e:=e) (ez:=ez) (v:=v) (y:=Q.xs+z)
      (K:=K) (J:=J) (H:=H) (q:=q)
      Q.data.hN he hez hv.1 hy (by linarith : 1 ≤ K)
      hJ hH hshape hheight
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have Hcubic := laplaceComparisonStrength_le_log_cubic
    hN Q.data.hd hnd Q.hlam Q.hld hv.1 hv.2
  have Hmul := mul_le_mul_of_nonneg_right Hcubic hv.1.le
  have hlog2 : 1+Real.log Q.data.N ≤ 2*Real.log Q.data.N := by
    linarith
  have Hd := mul_le_mul_of_nonneg_right hlog2
    (pow_nonneg Q.data.hd.le 3)
  have henergy : e*v ≤ Q.data.d^3*(2*Real.log Q.data.N) := by
    dsimp only [e]
    calc
      laplaceComparisonStrength Q.data.d Q.lam v*v ≤
          ((1+Real.log Q.data.N)*Q.data.d^3/v)*v := Hmul
      _ = (1+Real.log Q.data.N)*Q.data.d^3 := by
        field_simp [hv.1.ne']
      _ ≤ Q.data.d^3*(2*Real.log Q.data.N) := by
        nlinarith only [Hd]
  have hlowerNorm :
      (1/C0)*Q.data.N^(-(2:ℝ)/3+m)*Q.data.d ≤ Q.data.E := by
    calc
      (1/C0)*Q.data.N^(-(2:ℝ)/3+m)*Q.data.d =
          (Q.data.N^(-(2:ℝ)/3+m)*Q.data.d)/C0 := by ring
      _ ≤ Q.data.E := (div_le_iff₀ hC0).mpr (by
        simpa only [mul_comm] using Q.hlower)
  have hsize := comparison_conditional_outer_optimized_cost
    (N:=Q.data.N) (m:=m) (gamma:=1/C0) (d:=Q.data.d)
    (E:=Q.data.E) (t:=e*v) (L:=2*Real.log Q.data.N)
    Q.data.hN (one_div_pos.mpr hC0) Q.data.hd Q.data.hE
    (mul_nonneg he hv.1.le)
    (by linarith : 0 ≤ 2*Real.log Q.data.N)
    henergy
    hlowerNorm
  have hgammaEq : 1/(1/C0)=C0 := by field_simp [hC0.ne']
  rw [hgammaEq] at hsize
  have hcoef : 0 ≤ 2*(q^2*H*J)^((2:ℝ)/3) := by positivity
  have Hscaled := mul_le_mul_of_nonneg_left hsize hcoef
  dsimp only [z,H,J,e,ez] at hscalar Hscaled ⊢
  nlinarith only [hscalar,Hscaled]

theorem outer_truncated_variance_five_atom_input_corrected_c0_isolated_draft
    (hm : 0 < m) (hdelta : 0 < delta)
    (hmargin : delta/2 ≤ m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0)
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hL : 1 ≤ Real.log Q.data.N)
    {lo K v : ℝ} (hK : 4 ≤ K)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hgroup : (cl/(4*cu))*lo ≤ v)
    (q : ℝ) :
    let z := min (K*v) 1
    let H := 2/cl+K
    let J := max 1 ((Az+1/cl)*H)
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    let P := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
      (Q.shiftedNativeModel.R z)
    let M := K*v
    e*M*(2*((q^2*(Q.xs+z))/(P*M^2))^((2:ℝ)/3)) ≤
      ((4*C0)*(q^2*H*J)^((2:ℝ)/3))*
        (Real.log Q.data.N)^3*Q.data.N^(-delta/2)*Q.data.E := by
  let L := Real.log Q.data.N
  let H := 2/cl+K
  let J := max 1 ((Az+1/cl)*H)
  let Craw := (q^2*H*J)^((2:ℝ)/3)
  have Hatom := Q.outer_truncated_variance_atom_optimized_rate_corrected_c0_isolated_draft
    hcl hcu hAz hC0 hnd hL hK hv houter hgroup q
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpow : Q.data.N^(-m) ≤ Q.data.N^(-delta/2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith [hmargin])
  have hL3 : L ≤ L^3 := by
    have hL2 : 1 ≤ L^2 := one_le_pow₀ hL
    have H := mul_le_mul_of_nonneg_left hL2 (by linarith : 0 ≤ L)
    nlinarith only [H]
  have hroot : (2*L)^((1:ℝ)/3) ≤ 2*L := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le
        (by linarith : 1 ≤ 2*L)
        (by norm_num : (1:ℝ)/3 ≤ 1))
  have hCraw : 0 ≤ Craw := by dsimp [Craw]; positivity
  have hE : 0 ≤ Q.data.E := Q.data.hE.le
  have Hpow := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (2*C0)*Craw*(2*L)^((1:ℝ)/3)*Q.data.E by positivity)
  have Hroot := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ (2*C0)*Craw*Q.data.N^(-delta/2)*Q.data.E by positivity)
  have Hlog := mul_le_mul_of_nonneg_left hL3
    (show 0 ≤ (4*C0)*Craw*Q.data.N^(-delta/2)*Q.data.E by positivity)
  dsimp only [L,H,J,Craw] at Hatom Hpow Hroot Hlog ⊢
  calc
    _ ≤ (2*C0)*(q^2*(2/cl+K)*
          max 1 ((Az+1/cl)*(2/cl+K)))^((2:ℝ)/3)*
          Q.data.N^(-m)*(2*Real.log Q.data.N)^((1:ℝ)/3)*Q.data.E := Hatom
    _ ≤ (2*C0)*(q^2*(2/cl+K)*
          max 1 ((Az+1/cl)*(2/cl+K)))^((2:ℝ)/3)*
          Q.data.N^(-delta/2)*(2*Real.log Q.data.N)^((1:ℝ)/3)*Q.data.E := by
      nlinarith only [Hpow]
    _ ≤ (4*C0)*(q^2*(2/cl+K)*
          max 1 ((Az+1/cl)*(2/cl+K)))^((2:ℝ)/3)*
          Q.data.N^(-delta/2)*Real.log Q.data.N*Q.data.E := by
      nlinarith only [Hroot]
    _ ≤ _ := by nlinarith only [Hlog]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
