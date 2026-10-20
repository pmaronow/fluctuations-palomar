module

public import ComparisonNativeActualHighMassCriticalRates
public import ComparisonNativeActualLocalDiameterBudgetMonotonicity
public import ReverseMovementPowerExtraction

@[expose] public section

noncomputable section
set_option maxHeartbeats 11000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_reverse_power_extraction {N diam Q y p a k eps0 : ℝ}
    (hN : 0 < N) (hdiam : 0 < diam) (hQ : 0 < Q) (hy : 0 < y) (hp : 2 < p)
    (hraw : Q ≤ N^eps0) (hyN : y ≤ N^a) (hdiamN : N^(-k) ≤ diam) :
    diam^((p-2)/(p-1))*((2*Q)^(2*p)*y^p)^(1/(p-1)) ≤
      (2:ℝ)^(2*p/(p-1))*N^(2*p*eps0/(p-1)+(a+k)/(p-1))*y*diam := by
  let q : ℝ := 1/(p-1)
  let theta : ℝ := (p-2)/(p-1)
  have hpm : 0 < p-1:=by linarith
  have hq : 0 < q:=one_div_pos.mpr hpm
  have ht : 0 ≤ theta:=div_nonneg (by linarith) hpm.le
  have htid : theta=1-q:=by dsimp [theta,q];field_simp;ring
  have hpid : p*q=1+q:=by dsimp [q];field_simp;ring
  have Hratio : y/diam ≤ N^(a+k):=by
    calc
      _ ≤ N^a/N^(-k):=div_le_div₀ (Real.rpow_nonneg hN.le _) hyN
        (Real.rpow_pos_of_pos hN _) hdiamN
      _ = N^(a+k):=by rw [←Real.rpow_sub hN];congr 1;ring
  have HR:=Real.rpow_le_rpow (div_nonneg hy.le hdiam.le) Hratio hq.le
  rw [←Real.rpow_mul hN.le] at HR
  have HQ:=Real.rpow_le_rpow hQ.le hraw (by dsimp [q];positivity : 0 ≤ 2*p*q)
  rw [←Real.rpow_mul hN.le] at HQ
  have HE : diam^theta*((2*Q)^(2*p)*y^p)^q=
      (2:ℝ)^(2*p*q)*Q^(2*p*q)*(y*diam)*(y/diam)^q:=by
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul (by positivity),
      ←Real.rpow_mul hy.le,Real.mul_rpow (by norm_num) hQ.le,
      Real.div_rpow hy.le hdiam.le,htid,hpid,Real.rpow_sub hdiam,Real.rpow_add hy]
    simp only [Real.rpow_one]
    field_simp
  calc
    _ = (2:ℝ)^(2*p*q)*Q^(2*p*q)*(y*diam)*(y/diam)^q:=HE
    _ ≤ (2:ℝ)^(2*p*q)*N^(eps0*(2*p*q))*(y*diam)*N^((a+k)*q):=by
      gcongr
    _ = _:=by
      rw [show (2:ℝ)^(2*p*q)*N^(eps0*(2*p*q))*(y*diam)*N^((a+k)*q)=
        (2:ℝ)^(2*p*q)*(N^(eps0*(2*p*q))*N^((a+k)*q))*y*diam by ring,
        ←Real.rpow_add hN]
      dsimp only [q]
      congr 3 <;> field_simp

theorem exists_high_mass_reverse_order {k eps0 eps : ℝ}
    (_hk : 0 ≤ k) (_heps0 : 0 ≤ eps0) (heps : 0 < eps) (hgap : eps0 < eps/4) :
    ∃ ell : ℕ,2 < ell ∧
      2*(ell:ℝ)*eps0/((ell:ℝ)-1)+(1+k)/((ell:ℝ)-1) < eps := by
  have hmargin : 0 < eps-2*eps0:=by linarith
  obtain ⟨ell,hEll⟩:=exists_nat_gt (max (3:ℝ) (1+(2*eps0+1+k)/(eps-2*eps0)))
  have hEll3 : 3 < (ell:ℝ):=(le_max_left _ _).trans_lt hEll
  have hEllB : 1+(2*eps0+1+k)/(eps-2*eps0) < (ell:ℝ):=(le_max_right _ _).trans_lt hEll
  have hden : 0 < (ell:ℝ)-1:=by linarith
  have HB : 2*eps0+1+k < ((ell:ℝ)-1)*(eps-2*eps0):=by
    apply (div_lt_iff₀ hmargin).mp
    linarith
  refine ⟨ell,by exact_mod_cast (by linarith : (2:ℝ) < ell),?_⟩
  have HE : 2*(ell:ℝ)*eps0/((ell:ℝ)-1)+(1+k)/((ell:ℝ)-1)=
      2*eps0+(2*eps0+1+k)/((ell:ℝ)-1):=by field_simp;ring
  rw [HE]
  have HH:=(div_lt_iff₀ hden).mpr (by nlinarith only [HB] :
    2*eps0+1+k < (eps-2*eps0)*((ell:ℝ)-1))
  linarith

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def canonicalChosenHighMassDiameter
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (Cdiam v : ℝ) : ℝ :=
  Cdiam*Real.log a.context.N*a.context.E/(a.context.N^delta*a.context.d^3*v)

theorem canonical_chosen_high_mass_diameter_pos
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Cdiam v : ℝ} (hCdiam : 0 < Cdiam) (hlog : 0 < Real.log a.context.N) (hv : 0 < v) :
    0 < a.canonicalChosenHighMassDiameter Cdiam v := by
  unfold canonicalChosenHighMassDiameter
  exact div_pos (mul_pos (mul_pos hCdiam hlog) a.context.hE)
    (mul_pos (mul_pos (Real.rpow_pos_of_pos a.context.hN _) (pow_pos a.context.hd _)) hv)

theorem canonical_local_mass_diameter_le_chosen
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Cdiam v : ℝ} (hCdiam : 576 ≤ Cdiam) (_hlog : 0 ≤ Real.log a.context.N) (hv : 0 < v) :
    a.canonicalLocalMassDiameter v ≤ a.canonicalChosenHighMassDiameter Cdiam v := by
  have hNpow:=Real.rpow_pos_of_pos a.context.hN delta
  have hd:=a.context.hd
  have hE:=a.context.hE
  have hU:=a.context.hU
  unfold canonicalLocalMassDiameter canonicalChosenHighMassDiameter
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have HC : 288*v ≤ Cdiam*(v/2+a.context.U):=by
    have HH:=mul_le_mul_of_nonneg_right hCdiam (show 0 ≤ v/2+a.context.U by positivity)
    nlinarith [HH]
  have HH:=mul_le_mul_of_nonneg_left HC (show 0 ≤ Real.log a.context.N*a.context.E*(a.context.N^delta*a.context.d^3) by positivity)
  nlinarith only [HH]

theorem canonical_outer_mass_diameter_le_chosen
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (_hcl : 0 < cl) (_hcu : 0 < cu) {Cdiam v : ℝ}
    (hCdiam : 288*cu^3/cl^3 ≤ Cdiam) (hlog : 0 ≤ Real.log a.context.N) (hv : 0 < v) :
    a.canonicalOuterBroadMassDiameter v ≤ a.canonicalChosenHighMassDiameter Cdiam v := by
  unfold canonicalOuterBroadMassDiameter
  apply (mul_le_mul_of_nonneg_left (min_le_right _ _) (show 0 ≤ 9*Real.log a.context.N by positivity)).trans
  unfold canonicalChosenHighMassDiameter
  have HE : 9*Real.log a.context.N*((32*cu^3/cl^3)*a.context.E/
      (a.context.N^delta*a.context.d^3*v))=
      (288*cu^3/cl^3)*Real.log a.context.N*a.context.E/(a.context.N^delta*a.context.d^3*v):=by ring
  rw [HE]
  have hNpow:=Real.rpow_pos_of_pos a.context.hN delta
  have hd:=a.context.hd
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdiam hlog) a.context.hE.le)
    (by positivity)

theorem canonical_chosen_high_mass_diameter_lower
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) {Cdiam v : ℝ} (hCdiam : 0 < Cdiam)
    (hlog : 1 ≤ Real.log a.context.N) (hv : 0 < v) (hv1 : v ≤ 1) :
    (Cdiam/(C0*D^2))*a.context.N^(-delta-(2:ℝ)/3+m) ≤
      a.canonicalChosenHighMassDiameter Cdiam v := by
  have hD : 0 < D:=a.context.hd.trans_le a.hdD
  have hN:=a.context.hN
  have hE:=a.context.hE
  have hd:=a.context.hd
  have Hlo : a.context.N^(-(2:ℝ)/3+m)*a.context.d ≤ C0*a.context.E:=by
    simpa only [mul_comm] using a.hlower
  have HD:=pow_le_pow_left₀ hd.le a.hdD 2
  have Henergy : a.context.N^(-(2:ℝ)/3+m)/(C0*D^2) ≤ a.context.E/a.context.d^3:=by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have H1:=mul_le_mul_of_nonneg_right Hlo (sq_nonneg a.context.d)
    have H2:=mul_le_mul_of_nonneg_left HD (show 0 ≤ C0*a.context.E by positivity)
    nlinarith only [H1,H2]
  have Hy : (1:ℝ) ≤ Real.log a.context.N/v:=
    (le_div_iff₀ hv).mpr (by linarith)
  have Hfactor:=mul_le_mul_of_nonneg_left Hy
    (show 0 ≤ Cdiam*a.context.N^(-delta)*(a.context.E/a.context.d^3) by positivity)
  have Hbase:=mul_le_mul_of_nonneg_left Henergy
    (show 0 ≤ Cdiam*a.context.N^(-delta) by positivity)
  have HE : Cdiam*a.context.N^(-delta)*(a.context.N^(-(2:ℝ)/3+m)/(C0*D^2))=
      (Cdiam/(C0*D^2))*a.context.N^(-delta-(2:ℝ)/3+m):=by
    calc
      _ = (Cdiam/(C0*D^2))*(a.context.N^(-delta)*a.context.N^(-(2:ℝ)/3+m)):=by ring
      _ = _:=by rw [←Real.rpow_add hN];congr 1;ring
  have HE2 : Cdiam*a.context.N^(-delta)*(a.context.E/a.context.d^3)*(Real.log a.context.N/v)=
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
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1 ≤ Real.log a.context.N → ∀v : ℝ,0 < v → v ≤ 1 →
          a.context.N^(-(delta+2)) ≤ a.canonicalChosenHighMassDiameter Cdiam v := by
  let K:=Cdiam/(C0*D^2)
  have hK : 0 < K:=by dsimp [K];positivity
  have Hlarge:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-delta-2) (eps:=-delta-(2:ℝ)/3+m)
      (by linarith) (1/K))
  filter_upwards [Hlarge] with n hn
  intro a hlog v hv hv1
  have H:=mul_le_mul_of_nonneg_left hn hK.le
  have HE : K*((1/K)*a.context.N^(-delta-2))=a.context.N^(-(delta+2)):=by
    field_simp;congr 1;ring
  rw [HE] at H
  exact H.trans (a.canonical_chosen_high_mass_diameter_lower hC0 hCdiam hlog hv hv1)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
