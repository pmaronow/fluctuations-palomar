module

public import ComparisonActualHighWallInitialFourSecondLowModulusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators
set_option maxHeartbeats 12000000

theorem original_initial_low_moment_modulus_factor
    {K D Ci d : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hCi : 0 < Ci) (hd : 0 < d) (p : ℕ) :
    originalInitialLowMomentModulus (K*D) (Ci*d) p =
      (K/Ci)^((p:ℝ)⁻¹) * (D/d)^((p:ℝ)⁻¹) := by
  unfold originalInitialLowMomentModulus
  have hquot : K*D/(Ci*d)=(K/Ci)*(D/d) := by
    field_simp [hCi.ne',hd.ne']
  rw [hquot,Real.mul_rpow (div_nonneg hK hCi.le) (div_nonneg hD hd.le)]

theorem actual_high_wall_initial_full_B0_envelope_fractional_factor
    (degree : ℕ) (C CiU CiB CiM : Fin degree→ℝ)
    (Cf Cr K D d N eta : ℝ)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hd : 0 < d)
    (hCiU : ∀a,0 < CiU a) (hCiB : ∀a,0 < CiB a)
    (hCiM : ∀a,0 < CiM a) (hCr : 0 < Cr) :
    actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr (K*D) d N eta =
      (∑a : Fin degree,C a*(
        (K/CiU a)^((8:ℝ)⁻¹)*(D/d)^((8:ℝ)⁻¹)+
        (K/CiB a)^((8:ℝ)⁻¹)*(D/d)^((8:ℝ)⁻¹)+
        (K/CiM a)^((4:ℝ)⁻¹)*(D/d)^((4:ℝ)⁻¹)+N^(-eta)))+
      Cf*(Cr*((K/Cr)^(((2*(degree+1):ℕ):ℝ)⁻¹)*
        (D/d)^(((2*(degree+1):ℕ):ℝ)⁻¹))+d^3) := by
  unfold actualHighWallInitialFullB0Envelope actualHighWallInitialLiveB0Envelope
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [original_initial_low_moment_modulus_factor hK hD (hCiU a) hd 8,
      original_initial_low_moment_modulus_factor hK hD (hCiB a) hd 8,
      original_initial_low_moment_modulus_factor hK hD (hCiM a) hd 4]
    norm_num
  · rw [original_initial_low_moment_modulus_factor hK hD hCr hd (2*(degree+1))]

theorem actual_high_wall_initial_full_B0_envelope_fractional_factor_at_cut
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (i degree : ℕ)
    (C CiU CiB CiM : Fin degree→ℝ) (Cf Cr eta : ℝ)
    (hCiU : ∀a,0 < CiU a) (hCiB : ∀a,0 < CiB a)
    (hCiM : ∀a,0 < CiM a) (hCr : 0 < Cr) :
    let K:=originalInitialPairComparisonConstant (2*max Bclock 0) (max Bclock 0)
    let Di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
    actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
        (originalHighWallInitialPairErrorScale M as i) M.data.d (n:ℝ) eta =
      (∑a : Fin degree,C a*(
        (K/CiU a)^((8:ℝ)⁻¹)*(Di/M.data.d)^((8:ℝ)⁻¹)+
        (K/CiB a)^((8:ℝ)⁻¹)*(Di/M.data.d)^((8:ℝ)⁻¹)+
        (K/CiM a)^((4:ℝ)⁻¹)*(Di/M.data.d)^((4:ℝ)⁻¹)+(n:ℝ)^(-eta)))+
      Cf*(Cr*((K/Cr)^(((2*(degree+1):ℕ):ℝ)⁻¹)*
        (Di/M.data.d)^(((2*(degree+1):ℕ):ℝ)⁻¹))+M.data.d^3) := by
  dsimp only
  have hK : 0 ≤ originalInitialPairComparisonConstant (2*max Bclock 0)
      (max Bclock 0) := (original_initial_pair_comparison_constant_pos _ _).le
  have hDi : 0 ≤ nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ) :=
    add_nonneg (Real.sqrt_nonneg _) (by positivity)
  simpa only [originalHighWallInitialPairErrorScale] using
    (actual_high_wall_initial_full_B0_envelope_fractional_factor degree
      C CiU CiB CiM Cf Cr
      (originalInitialPairComparisonConstant (2*max Bclock 0) (max Bclock 0))
      (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
      M.data.d (n:ℝ) eta hK hDi M.data.hd hCiU hCiB hCiM hCr)

end OAI.SKFluctuations.Cavity
