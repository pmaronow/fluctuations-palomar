module

public import ComparisonNativeActualHighMassReverse
public import ComparisonActualHighOnlyHighMassDiameter

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def canonicalChosenHighMassDiameter
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (Cdiam v : ℝ) : ℝ :=
  Cdiam*Real.log a.data.N*a.data.E/(a.data.N^delta*a.data.d^3*v)

theorem canonical_chosen_high_mass_diameter_pos
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Cdiam v : ℝ} (hCdiam : 0 < Cdiam) (hlog : 0 < Real.log a.data.N) (hv : 0 < v) :
    0 < a.canonicalChosenHighMassDiameter Cdiam v := by
  unfold canonicalChosenHighMassDiameter
  exact div_pos (mul_pos (mul_pos hCdiam hlog) a.data.hE)
    (mul_pos (mul_pos (Real.rpow_pos_of_pos a.data.hN _) (pow_pos a.data.hd _)) hv)

theorem canonical_local_mass_diameter_le_chosen
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Cdiam v : ℝ} (hCdiam : 576 ≤ Cdiam) (_hlog : 0 ≤ Real.log a.data.N) (hv : 0 < v) :
    a.canonicalLocalMassDiameter v ≤ a.canonicalChosenHighMassDiameter Cdiam v := by
  have hNpow:=Real.rpow_pos_of_pos a.data.hN delta
  have hd:=a.data.hd
  have hE:=a.data.hE
  have hU:=a.data.hU
  unfold canonicalLocalMassDiameter canonicalChosenHighMassDiameter
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have HC : 288*v ≤ Cdiam*(v/2+a.data.U):=by
    have HH:=mul_le_mul_of_nonneg_right hCdiam (show 0 ≤ v/2+a.data.U by positivity)
    nlinarith [HH]
  have HH:=mul_le_mul_of_nonneg_left HC (show 0 ≤ Real.log a.data.N*a.data.E*(a.data.N^delta*a.data.d^3) by positivity)
  nlinarith only [HH]

theorem canonical_outer_mass_diameter_le_chosen
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (_hcl : 0 < cl) (_hcu : 0 < cu) {Cdiam v : ℝ}
    (hCdiam : 288*cu^3/cl^3 ≤ Cdiam) (hlog : 0 ≤ Real.log a.data.N) (hv : 0 < v) :
    a.canonicalOuterBroadMassDiameter v ≤ a.canonicalChosenHighMassDiameter Cdiam v := by
  unfold canonicalOuterBroadMassDiameter
  apply (mul_le_mul_of_nonneg_left (min_le_right _ _) (show 0 ≤ 9*Real.log a.data.N by positivity)).trans
  unfold canonicalChosenHighMassDiameter
  have HE : 9*Real.log a.data.N*((32*cu^3/cl^3)*a.data.E/
      (a.data.N^delta*a.data.d^3*v))=
      (288*cu^3/cl^3)*Real.log a.data.N*a.data.E/(a.data.N^delta*a.data.d^3*v):=by ring
  rw [HE]
  have hNpow:=Real.rpow_pos_of_pos a.data.hN delta
  have hd:=a.data.hd
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdiam hlog) a.data.hE.le)
    (by positivity)

theorem canonical_chosen_high_mass_diameter_lower
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) {Cdiam v : ℝ} (hCdiam : 0 < Cdiam)
    (hlog : 1 ≤ Real.log a.data.N) (hv : 0 < v) (hv1 : v ≤ 1) :
    (Cdiam/(C0*D^2))*a.data.N^(-delta-(2:ℝ)/3+m) ≤
      a.canonicalChosenHighMassDiameter Cdiam v := by
  have hD : 0 < D:=a.data.hd.trans_le a.hdD
  have hN:=a.data.hN
  have hE:=a.data.hE
  have hd:=a.data.hd
  have Hlo : a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ C0*a.data.E:=by
    simpa only [mul_comm] using a.hlower
  have HD:=pow_le_pow_left₀ hd.le a.hdD 2
  have Henergy : a.data.N^(-(2:ℝ)/3+m)/(C0*D^2) ≤ a.data.E/a.data.d^3:=by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have H1:=mul_le_mul_of_nonneg_right Hlo (sq_nonneg a.data.d)
    have H2:=mul_le_mul_of_nonneg_left HD (show 0 ≤ C0*a.data.E by positivity)
    nlinarith only [H1,H2]
  have Hy : (1:ℝ) ≤ Real.log a.data.N/v:=
    (le_div_iff₀ hv).mpr (by linarith)
  have Hfactor:=mul_le_mul_of_nonneg_left Hy
    (show 0 ≤ Cdiam*a.data.N^(-delta)*(a.data.E/a.data.d^3) by positivity)
  have Hbase:=mul_le_mul_of_nonneg_left Henergy
    (show 0 ≤ Cdiam*a.data.N^(-delta) by positivity)
  have HE : Cdiam*a.data.N^(-delta)*(a.data.N^(-(2:ℝ)/3+m)/(C0*D^2))=
      (Cdiam/(C0*D^2))*a.data.N^(-delta-(2:ℝ)/3+m):=by
    calc
      _ = (Cdiam/(C0*D^2))*(a.data.N^(-delta)*a.data.N^(-(2:ℝ)/3+m)):=by ring
      _ = _:=by rw [←Real.rpow_add hN, show -delta+(-(2:ℝ)/3+m)=-delta-(2:ℝ)/3+m by ring]
  have HE2 : Cdiam*a.data.N^(-delta)*(a.data.E/a.data.d^3)*(Real.log a.data.N/v)=
      a.canonicalChosenHighMassDiameter Cdiam v:=by
    unfold canonicalChosenHighMassDiameter
    rw [Real.rpow_neg hN.le]
    ring
  rw [HE] at Hbase
  apply Hbase.trans
  simpa only [mul_one,HE2] using Hfactor

theorem eventually_chosen_high_mass_diameter_polynomial_lower
    {m delta cl cu Az C0 Ct D Bclock Cdiam : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hD : 0 < D) (hCdiam : 0 < Cdiam) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1 ≤ Real.log a.data.N → ∀v : ℝ,0 < v → v ≤ 1 →
          a.data.N^(-(delta+2)) ≤ a.canonicalChosenHighMassDiameter Cdiam v := by
  let K:=Cdiam/(C0*D^2)
  have hK : 0 < K:=by dsimp [K];positivity
  have Hlarge:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-delta-2) (eps:=-delta-(2:ℝ)/3+m)
      (by linarith) (1/K))
  filter_upwards [Hlarge] with n hn
  intro a hlog v hv hv1
  have H:=mul_le_mul_of_nonneg_left hn hK.le
  have HE : K*((1/K)*a.data.N^(-delta-2))=a.data.N^(-(delta+2)):=by
    rw [show -delta-2=-(delta+2) by ring]
    field_simp
  rw [HE] at H
  exact H.trans (a.canonical_chosen_high_mass_diameter_lower hC0 hCdiam hlog hv hv1)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
