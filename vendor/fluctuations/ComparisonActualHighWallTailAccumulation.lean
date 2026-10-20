module

public import ComparisonActualHighWallHighProfile
public import ComparisonNativeHighTailDyadicAccumulation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem physical_thermal_intervalIntegrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (M.data.thermal M.alpha) volume 0 1 :=
  physicalOrderedThermal_intervalIntegrable n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)

theorem thermal_tail_le_of_dyadic_bound
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {c sigma u : ℝ} (hc : 0< c) (hu : 2*c*M.data.d≤ u) (hu1 : u≤1)
    (hdyad : ∀v : ℝ,0< v → 2*v≤1 → c*M.data.d≤ v →
      (∫s in v..2*v,M.data.thermal M.alpha s)≤ M.data.N^(-sigma)*M.data.d^2*v) :
    (∫s in u..1,M.data.thermal M.alpha s)≤2*M.data.N^(-sigma)*M.data.d^2 := by
  let lo:=c*M.data.d
  let A:=M.data.N^(-sigma)*M.data.d^2
  have hlo : 0< lo:=mul_pos hc M.data.hd
  have hlohalf : lo≤1/2:=by dsimp only [lo];linarith only [hu,hu1]
  have HA : 0≤ A:=by dsimp only [A];positivity
  have HT:=native_high_tail_integral_le_dyadic_budget M.physical_thermal_intervalIntegrable
    (fun s hs=>M.data.thermal_nonneg M.alpha hs) hlo hlohalf HA hdyad
  have hbig : IntervalIntegrable (M.data.thermal M.alpha) volume lo 1:=by
    apply M.physical_thermal_intervalIntegrable.mono_set
    rw [uIcc_of_le (by linarith only [hlohalf]),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hlo.le le_rfl
  have hlu : lo≤ u:=by dsimp only [lo];linarith only [hu,hlo]
  have hf0 : 0≤ᵐ[volume.restrict (Ioc lo 1)] (M.data.thermal M.alpha):=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact M.data.thermal_nonneg M.alpha ⟨hlo.le.trans hs.1.le,hs.2⟩
  have Hmono:=intervalIntegral.integral_mono_interval hlu hu1 le_rfl hf0 hbig
  exact Hmono.trans (by simpa only [A,mul_assoc] using HT)

theorem sqrt_thermal_tail_le_of_dyadic_bound
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {c sigma u : ℝ} (hc : 0< c) (hu : 2*c*M.data.d≤ u) (hu1 : u≤1)
    (hdyad : ∀v : ℝ,0< v → 2*v≤1 → c*M.data.d≤ v →
      (∫s in v..2*v,M.data.thermal M.alpha s)≤ M.data.N^(-sigma)*M.data.d^2*v) :
    (∫s in u..1,Real.sqrt (M.data.thermal M.alpha s))≤2*M.data.N^(-(sigma/2))*M.data.d := by
  have hd:=M.data.hd
  have hu0 : 0≤ u:=(mul_pos (by positivity : 0<2*c) M.data.hd).le.trans hu
  have hfi:=M.physical_thermal_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hu1,uIcc_of_le zero_le_one];exact Icc_subset_Icc hu0 le_rfl)
  have HS:=interval_integral_sqrt_sq_le_length hu1 hfi
    (fun s hs=>M.data.thermal_nonneg M.alpha ⟨hu0.trans hs.1,hs.2⟩)
  have HT:=M.thermal_tail_le_of_dyadic_bound hc hu hu1 hdyad
  have HM:=mul_le_mul_of_nonneg_left HT (sub_nonneg.mpr hu1)
  have HL:=mul_le_mul_of_nonneg_right (show 1-u≤1 by linarith)
    (show 0≤2*M.data.N^(-sigma)*M.data.d^2 by positivity)
  have HE : (M.data.N^(-(sigma/2)))^2=M.data.N^(-sigma):=by
    rw [←Real.rpow_mul_natCast M.data.hN.le];congr 1;push_cast;ring
  have Hpow : (2*M.data.N^(-(sigma/2))*M.data.d)^2=4*M.data.N^(-sigma)*M.data.d^2:=by
    rw [mul_pow,mul_pow,HE];norm_num
  have HX:=HS.trans (HM.trans HL)
  simp only [one_mul] at HX
  have HR : 0≤2*M.data.N^(-(sigma/2))*M.data.d:=by positivity
  have HT0 : 0≤ M.data.N^(-sigma)*M.data.d^2:=by positivity
  nlinarith only [HX,Hpow,HR,HT0]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
