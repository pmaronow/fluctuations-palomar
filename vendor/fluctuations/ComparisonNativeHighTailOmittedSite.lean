module

public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 13000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_high_tail_site_normalized_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hW1 : M.canonicalDirectTestBandScale≤1) :
    (1/M.context.N)/(M.xs^2/M.canonicalDirectTestBandScale)≤
      C0^2*M.context.N^(-(2:ℝ)/3-2*m) := by
  have hN:=M.context.hN
  have hx:=M.hxs
  have hW:=M.canonical_direct_test_band_pos
  have H:=M.canonical_high_mass_inverse_power hC0 2
  have H' : 1/(M.context.N^((1:ℝ)/3)*M.xs^2)≤C0^2*M.context.N^(-2*m) := by
    simpa only [Nat.cast_ofNat,show (2:ℝ)/6=1/3 by norm_num] using H
  have HE : (1/M.context.N)/(M.xs^2/M.canonicalDirectTestBandScale)=
      M.canonicalDirectTestBandScale*(M.context.N^(-(2:ℝ)/3)*
        (1/(M.context.N^((1:ℝ)/3)*M.xs^2))) := by
    have Hpow : M.context.N^(-(2:ℝ)/3)*M.context.N=
        M.context.N^((1:ℝ)/3) := by
      calc
        _=M.context.N^(-(2:ℝ)/3)*M.context.N^(1:ℝ) := by rw [Real.rpow_one]
        _=M.context.N^(-(2:ℝ)/3+1) := (Real.rpow_add hN _ _).symm
        _=M.context.N^((1:ℝ)/3) := by congr 1;norm_num
    field_simp
    simpa only [mul_comm,neg_div] using Hpow.symm
  rw [HE]
  have Hscaled:=mul_le_mul_of_nonneg_left H' (Real.rpow_nonneg hN.le (-(2:ℝ)/3))
  have Hfirst:=mul_le_of_le_one_left
    (show 0≤M.context.N^(-(2:ℝ)/3)*(1/(M.context.N^((1:ℝ)/3)*M.xs^2)) by positivity) hW1
  have Hfinal : M.context.N^(-(2:ℝ)/3)*(C0^2*M.context.N^(-2*m))=
      C0^2*M.context.N^(-(2:ℝ)/3-2*m) := by
    rw [mul_left_comm,←Real.rpow_add hN]
    congr 1
    ring
  exact Hfirst.trans (Hscaled.trans_eq Hfinal)

theorem eventually_actual_minimum_high_tail_site_le
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0<C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.canonicalDirectTestBandScale≤1 →
        1/M.context.N≤M.context.N^(-(actualMassSavingExponent m delta/16))*
          (M.xs^2/M.canonicalDirectTestBandScale) := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0<eta:=actualMassSavingExponent_pos hm hdelta
  have he1:=(actualMassSavingExponent_bounds m delta).1
  have Hcoef:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^2) (d:=1)
      (q:=-(2:ℝ)/3-2*m) (r:=-eta/16) zero_lt_one (by dsimp only [eta] at *;linarith))
  filter_upwards [Hcoef] with n hn
  intro M hW1
  have H:=(native_high_tail_site_normalized_le M hC0 hW1).trans
    (show C0^2*M.context.N^(-(2:ℝ)/3-2*m)≤M.context.N^(-eta/16) by
      simpa only [NativeOverlapContext.N,one_mul] using hn)
  have htarget : 0<M.xs^2/M.canonicalDirectTestBandScale:=by
    have :=M.hxs;have :=M.canonical_direct_test_band_pos;positivity
  simpa only [eta,neg_div] using (div_le_iff₀ htarget).mp H

end OAI.SKFluctuations.LaplaceWindowFormalization
