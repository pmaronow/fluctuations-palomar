module

public import ComparisonActualHighWallBoundaryResampling
public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open Filter Set
open scoped Topology
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_high_wall_terminal_power_over_cubic_scale {n : ℕ}
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) {C gamma : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    C*((n+1:ℕ):ℝ)^(-gamma*(k:ℝ))/a.xs^3 ≤
      (C*C0^3)*((n+1:ℕ):ℝ)^(-(gamma*(k:ℝ)-(1:ℝ)/2+3*m)) := by
  let N : ℝ:=((n+1:ℕ):ℝ)
  have hN : 0 < N:=by dsimp only [N];positivity
  have H:=actual_high_wall_original_boundary_critical_radius hC0 a
  have HP:=pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) H 3
  have HE : (N^(-(1:ℝ)/6+m))^3=N^(-(1:ℝ)/2+3*m):=by
    rw [←Real.rpow_mul_natCast hN.le];congr 1;norm_num;ring
  change (N^(-(1:ℝ)/6+m))^3 ≤ (C0*a.xs)^3 at HP
  rw [HE,mul_pow] at HP
  have HB:=mul_le_mul_of_nonneg_left HP (Real.rpow_nonneg hN.le ((1:ℝ)/2-3*m))
  have Hcancel : N^((1:ℝ)/2-3*m)*N^(-(1:ℝ)/2+3*m)=1:=by
    rw [←Real.rpow_add hN,show (1:ℝ)/2-3*m+(-(1:ℝ)/2+3*m)=0 by ring,Real.rpow_zero]
  rw [Hcancel] at HB
  have HI : 1/a.xs^3 ≤ C0^3*N^((1:ℝ)/2-3*m):=by
    apply (div_le_iff₀ (pow_pos a.hxs 3)).mpr
    nlinarith only [HB]
  have HM:=mul_le_mul_of_nonneg_left HI
    (show 0 ≤ C*N^(-gamma*(k:ℝ)) by positivity)
  have HH : C*N^(-gamma*(k:ℝ))*(C0^3*N^((1:ℝ)/2-3*m))=
      (C*C0^3)*N^(-(gamma*(k:ℝ)-(1:ℝ)/2+3*m)):=by
    calc
      _=(C*C0^3)*(N^(-gamma*(k:ℝ))*N^((1:ℝ)/2-3*m)):=by ring
      _=_:=by rw [←Real.rpow_add hN];congr 1;congr 1;ring
  rw [HH] at HM
  simpa only [N,div_eq_mul_inv,one_mul] using HM

theorem exists_actual_high_wall_cubic_terminal_depth
    (hm : 0 < m) (hC0 : 0 < C0) {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃k : ℕ,0 < k ∧ ∃saving : ℝ,0 < saving ∧
      ∀C : ℝ,0 ≤ C → ∀ᶠn : ℕ in atTop,
        ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        ∀depth : ℕ,k ≤ depth →
          C*(((n+1:ℕ):ℝ)^(-gamma))^depth ≤
            ((n+1:ℕ):ℝ)^(-saving)*a.xs^3 := by
  obtain ⟨k,hk⟩:=exists_nat_gt (((1:ℝ)/2)/gamma)
  have hk0 : 0 < k:=by
    have H : (0:ℝ) < k:=(by positivity : 0 < ((1:ℝ)/2)/gamma).trans hk
    exact_mod_cast H
  have hkg : (1:ℝ)/2 < (k:ℝ)*gamma:=(div_lt_iff₀ hgamma).mp hk
  let q:=gamma*(k:ℝ)-(1:ℝ)/2+3*m
  have hq : 0 < q:=by dsimp only [q];nlinarith
  refine ⟨k,hk0,q/2,by positivity,?_⟩
  intro C hC
  have HR:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=q) (s:=q/2) (by linarith) 0 (C*C0^3))
  filter_upwards [HR] with n hn
  intro a depth hd
  have Hmono : (((n+1:ℕ):ℝ)^(-gamma))^depth ≤ ((n+1:ℕ):ℝ)^(-gamma*(k:ℝ)):=by
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ ((n+1:ℕ):ℝ))]
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (show 1 ≤ n+1 by omega)
    · have Hd : (k:ℝ) ≤ depth:=by exact_mod_cast hd
      nlinarith
  apply (mul_le_mul_of_nonneg_left Hmono hC).trans
  apply (div_le_iff₀ (pow_pos a.hxs 3)).mp
  apply (actual_high_wall_terminal_power_over_cubic_scale a hC0 hC k).trans
  simpa only [q,pow_zero,mul_one] using hn

end OAI.SKFluctuations.LaplaceWindowFormalization
