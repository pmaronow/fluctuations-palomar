module

public import ComparisonPhysicalLedgerAbsorption

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

theorem comparison_physical_dyadic_index_bound {N U : ℝ} {j : ℕ}
    (hN : 0 < N) (hU : 0 < U) (hUlower : 1/N ≤ U)
    (hscale : (2:ℝ)^j*U ≤ 1) :
    (j:ℝ) ≤ Real.log N/Real.log 2 := by
  have hpow : (2:ℝ)^j ≤ N := by
    have hh := mul_le_mul_of_nonneg_left hUlower (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) j)
    have hp : (2:ℝ)^j/N ≤ 1 := by simpa only [mul_one_div] using hh.trans hscale
    exact (div_le_one hN).mp hp
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) j) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr hlog

theorem comparison_physical_dyadic_card_le_log {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (j : ι→ℕ) {N U : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hU : 0 < U) (hUlower : 1/N ≤ U)
    (hscale : ∀i∈F,(2:ℝ)^(j i)*U ≤ 1)
    (hfiber : ∀k,(F.filter (fun i=>j i=k)).card ≤ 4) :
    (F.card:ℝ) ≤ 16*Real.log N := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let B : ℕ := Nat.ceil (Real.log N/Real.log 2)+1
  have hmap : (F:Set ι).MapsTo j (Finset.range B) := by
    intro i hi
    have hj := comparison_physical_dyadic_index_bound hNp hU hUlower (hscale i hi)
    have hh := hj.trans (Nat.le_ceil (Real.log N/Real.log 2))
    have hnat : j i ≤ Nat.ceil (Real.log N/Real.log 2) := by exact_mod_cast hh
    exact Finset.mem_range.mpr (by dsimp [B];omega)
  have hcard : F.card ≤ B*4 := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      _ ≤ ∑k∈Finset.range B,4 := Finset.sum_le_sum (fun k _=>hfiber k)
      _ = _ := by simp
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh
    exact hh
  have hratio : Real.log N/Real.log 2 ≤ 2*Real.log N := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
    nlinarith [mul_nonneg (show 0 ≤ Real.log N by linarith) (sub_nonneg.mpr hlog2)]
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ Real.log N/Real.log 2 by positivity)
  have hB : (B:ℝ) ≤ 4*Real.log N := by
    dsimp [B]
    rw [Nat.cast_add,Nat.cast_one]
    linarith
  have hc : (F.card:ℝ) ≤ (B:ℝ)*4 := by exact_mod_cast hcard
  nlinarith

theorem comparison_physical_dyadic_card_eventually {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℝ in atTop, ∀ (ι : Type*) (_ : DecidableEq ι) (F : Finset ι) (j : ι→ℕ) (U : ℝ),
      0 < U → 1/N ≤ U → (∀i∈F,(2:ℝ)^(j i)*U ≤ 1) →
      (∀k,(F.filter (fun i=>j i=k)).card ≤ 4) → (F.card:ℝ) ≤ N^eps := by
  have ht := comparison_log_loss_eventually (C:=16) (p:=1) (by norm_num) heps
  have hl := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [ht,hl,eventually_ge_atTop (1:ℝ)] with N hcost hlog hN
  intro ι _ F j U hU hUlower hscale hfiber
  exact (comparison_physical_dyadic_card_le_log F j hN hlog hU hUlower hscale hfiber).trans
    (by simpa using hcost)

theorem comparison_physical_dyadic_sum {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (j : ι→ℕ) {N U E exponent : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hU : 0 < U) (hUlower : 1/N ≤ U)
    (hE : 0 ≤ E) (hscale : ∀i∈F,(2:ℝ)^(j i)*U ≤ 1)
    (hfiber : ∀k,(F.filter (fun i=>j i=k)).card ≤ 4)
    (cost : ι→ℝ) (hcost : ∀i∈F,cost i ≤ N^exponent*E) :
    ∑i∈F,cost i ≤ 16*Real.log N*N^exponent*E := by
  calc
    _ ≤ ∑i∈F,N^exponent*E := Finset.sum_le_sum hcost
    _ = (F.card:ℝ)*N^exponent*E := by simp;ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (comparison_physical_dyadic_card_le_log F j hN hlog hU hUlower hscale hfiber)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) exponent).le) hE

end OAI.SKFluctuations.LaplaceWindowFormalization
