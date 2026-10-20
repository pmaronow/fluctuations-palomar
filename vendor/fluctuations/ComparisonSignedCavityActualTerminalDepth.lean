module

public import ComparisonNativeActualHighMassCriticalRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_terminal_power_over_scale {n : ℕ}
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) {C gamma : ℝ} (hC : 0≤C) (k : ℕ) :
    C*a.context.N^(-gamma*(k:ℝ))/a.xs^2 ≤
      (C*C0^2)*a.context.N^(-(gamma*(k:ℝ)-(1:ℝ)/3+2*m)) := by
  have H:=a.canonical_high_mass_inverse_power hC0 2
  norm_num only [Nat.cast_ofNat] at H
  have Hmul:=mul_le_mul_of_nonneg_left H
    (show 0≤C*a.context.N^((1:ℝ)/3-gamma*(k:ℝ)) by positivity)
  have HEleft : C*a.context.N^((1:ℝ)/3-gamma*(k:ℝ))*
      (1/(a.context.N^((1:ℝ)/3)*a.xs^2))=C*a.context.N^(-gamma*(k:ℝ))/a.xs^2 := by
    calc
      _=C*(a.context.N^((1:ℝ)/3-gamma*(k:ℝ))/a.context.N^((1:ℝ)/3))/a.xs^2 := by ring
      _=_ := by rw [←Real.rpow_sub a.context.hN];congr 2;congr 1;ring
  have HEright : C*a.context.N^((1:ℝ)/3-gamma*(k:ℝ))*(C0^2*a.context.N^(-(2:ℝ)*m))=
      (C*C0^2)*a.context.N^(-(gamma*(k:ℝ)-(1:ℝ)/3+2*m)) := by
    calc
      _=(C*C0^2)*(a.context.N^((1:ℝ)/3-gamma*(k:ℝ))*a.context.N^(-(2:ℝ)*m)) := by ring
      _=_ := by rw [←Real.rpow_add a.context.hN];congr 1;congr 1;ring
  rwa [HEleft,HEright] at Hmul

theorem exists_actual_terminal_depth
    (hm : 0 < m) (hC0 : 0<C0) {gamma : ℝ} (hgamma : 0<gamma) :
    ∃k : ℕ,0<k ∧ (1:ℝ)/3<(k:ℝ)*gamma ∧
      ∃saving : ℝ,0 < saving ∧ ∀C : ℝ,0≤C →
        ∀ᶠn : ℕ in atTop,
          ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
            C*a.context.N^(-gamma*(k:ℝ))≤a.context.N^(-saving)*a.xs^2 := by
  obtain ⟨k,hk⟩:=exists_nat_gt (((1:ℝ)/3)/gamma)
  have hk0 : 0<k := by
    have H : (0:ℝ)<k := (by positivity : 0<((1:ℝ)/3)/gamma).trans hk
    exact_mod_cast H
  have hkg : (1:ℝ)/3<(k:ℝ)*gamma := (div_lt_iff₀ hgamma).mp hk
  let q:=gamma*(k:ℝ)-(1:ℝ)/3+2*m
  have hq : 0<q := by dsimp [q];nlinarith
  refine ⟨k,hk0,hkg,q/2,by positivity,?_⟩
  intro C hC
  have Hrate:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=q) (s:=q/2) (by linarith) 0 (C*C0^2))
  filter_upwards [Hrate] with n hn
  intro a
  apply (div_le_iff₀ (sq_pos_of_pos a.hxs)).mp
  apply (a.actual_terminal_power_over_scale hC0 hC k).trans
  simpa only [NativeOverlapContext.N,pow_zero,mul_one,q] using hn

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
