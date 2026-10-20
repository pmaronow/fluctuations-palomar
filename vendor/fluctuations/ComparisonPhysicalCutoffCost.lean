module

public import ComparisonPhysicalLedgerAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

theorem comparison_physical_bin_count {N P y v Q P0 V0 : ℝ}
    (hN : 1 ≤ N) (hP : 0 ≤ P) (hy : 0 ≤ y) (hv : 0 ≤ v)
    (hP0 : 0 ≤ P0) (hV0 : 0 ≤ V0)
    (hPy : P ≤ P0*N) (hyN : y ≤ N) (hvV : v ≤ V0) :
    ((Q^2*y)^2*P*v^2)^((1:ℝ)/3)+2 ≤ ((Q^4*P0*V0^2)^((1:ℝ)/3)+2)*N := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hb : (Q^2*y)^2*P*v^2 ≤ (Q^4*P0*V0^2)*N^3 := by
    have hh : (Q^2*y)^2*P*v^2 ≤ (Q^2*N)^2*(P0*N)*V0^2 := by gcongr
    nlinarith
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (Q^2*y)^2*P*v^2) hb (by norm_num : (0:ℝ) ≤ 1/3)
  have hpow : (N^3)^((1:ℝ)/3)=N := by
    rw [←Real.rpow_natCast N 3,←Real.rpow_mul hNp.le]
    norm_num
  rw [Real.mul_rpow (by positivity : 0 ≤ Q^4*P0*V0^2) (pow_nonneg hNp.le _),hpow] at hh
  nlinarith

theorem comparison_physical_cutoff_log {N C : ℝ} (hN : 0 < N) :
    0 < N^(-C) ∧ Real.log (1/N^(-C))=C*Real.log N := by
  refine ⟨Real.rpow_pos_of_pos hN _,?_⟩
  rw [one_div,Real.log_inv,Real.log_rpow hN]
  ring

theorem comparison_ordinary_cutoff_eventually {Q P0 V0 Ccut : ℝ}
    (hP0 : 0 ≤ P0) (hV0 : 0 ≤ V0) (hcut : 3 ≤ Ccut) :
    ∀ᶠ N : ℝ in atTop, ∀ P y v s E : ℝ,
      0 ≤ P → P ≤ P0*N → 0 ≤ y → y ≤ N → 0 ≤ v → v ≤ V0 →
      0 ≤ s → s ≤ 1 → 1/N ≤ E →
      54*s*(((Q^2*y)^2*P*v^2)^((1:ℝ)/3)+2)*N^(-Ccut) ≤ E := by
  let c := (Q^4*P0*V0^2)^((1:ℝ)/3)+2
  have hc : 0 ≤ c := by dsimp [c];positivity
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (54*c)] with N hN hsize
  intro P y v s E hP hPN hy hyN hv hvV hs hs1 hE
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hb := comparison_physical_bin_count (Q:=Q) hN hP hy hv hP0 hV0 hPN hyN hvV
  have hbase : 54*s*(((Q^2*y)^2*P*v^2)^((1:ℝ)/3)+2)*N^(-Ccut) ≤ 54*c*N^(1-Ccut) := by
    have hh : 54*s*(((Q^2*y)^2*P*v^2)^((1:ℝ)/3)+2)*N^(-Ccut) ≤ 54*1*(c*N)*N^(-Ccut) := by
      gcongr
    have he : 54*1*(c*N)*N^(-Ccut)=54*c*N^(1-Ccut) := by
      nth_rw 1 [←Real.rpow_one N]
      rw [mul_assoc (54:ℝ) 1 (c*N^1)]
      calc
        _=54*c*(N^(1:ℝ)*N^(-Ccut)) := by ring
        _=_ := by rw [←Real.rpow_add hNp,sub_eq_add_neg]
    exact hh.trans_eq he
  have hpow := Real.rpow_le_rpow_of_exponent_le hN (show 1-Ccut ≤ -(2:ℝ) by linarith)
  have hp := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 54*c by positivity)
  have hsize' := mul_le_mul_of_nonneg_right hsize (Real.rpow_pos_of_pos hNp (-(2:ℝ))).le
  have he : N*N^(-(2:ℝ))=1/N := by
    rw [Real.rpow_neg hNp.le,Real.rpow_two]
    field_simp
  rw [he] at hsize'
  exact hbase.trans (hp.trans (hsize'.trans hE))

theorem comparison_broad_cutoff_eventually {Ccut : ℝ} (hcut : 2 ≤ Ccut) :
    ∀ᶠ N : ℝ in atTop, ∀ E s : ℝ, 0 < E → 0 ≤ s → s ≤ 1 →
      16*s*N^(-Ccut)/comparisonSmallMass N E ≤ E := by
  filter_upwards [eventually_ge_atTop (16:ℝ)] with N hN16
  intro E s hE hs hs1
  have hN : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have he : 16*s*N^(-Ccut)/comparisonSmallMass N E=16*s*N^(1-Ccut)*E := by
    unfold comparisonSmallMass
    calc
      _=16*s*(N*N^(-Ccut))*E := by field_simp <;> ring
      _=_ := by nth_rw 1 [←Real.rpow_one N];rw [←Real.rpow_add hNp,sub_eq_add_neg]
  rw [he]
  have hp := Real.rpow_le_rpow_of_exponent_le hN (show 1-Ccut ≤ -(1:ℝ) by linarith)
  have hh : 16*s*N^(1-Ccut)*E ≤ 16*N^(-(1:ℝ))*E := by
    have ht : 16*s*N^(1-Ccut)*E ≤ 16*1*N^(-(1:ℝ))*E := by gcongr
    simpa using ht
  have hb : 16*N^(-(1:ℝ)) ≤ 1 := by
    rw [Real.rpow_neg_one,←div_eq_mul_inv]
    exact (div_le_one hNp).mpr hN16
  exact hh.trans (by nlinarith)

end OAI.SKFluctuations.LaplaceWindowFormalization
