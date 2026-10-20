module

public import ComparisonNativeActualConditionalMinimum
public import ComparisonNativeActualMassBudgetScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7000000

theorem comparison_conditional_outer_room
    {N delta E d lam : ℝ} (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hE : 0 < E) (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hprod : 4 ≤ N*E*d) :
    E ≤ N^delta*d^3*(comparisonConditionalScale N delta E lam/2)^2 := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  let A := comparisonConditionalScale N delta E lam
  have hid : lam*A^2=N^(2*delta)*N*E^2 := comparison_conditional_scale_square hNp hlam
  have hp : 1 ≤ N^(2*delta) := Real.one_le_rpow hN (by linarith)
  have hp' : 1 ≤ N^delta := Real.one_le_rpow hN hdelta
  have hmul := mul_le_mul_of_nonneg_right hld (sq_nonneg A)
  have hpow := mul_le_mul_of_nonneg_right hp (show 0 ≤ N*E^2 by positivity)
  have hscale : N*E^2 ≤ d^2*A^2 := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hscale hd.le
  have he := mul_le_mul_of_nonneg_left hprod hE.le
  have hbase : E ≤ d^3*(A/2)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hp' (show 0 ≤ d^3*(A/2)^2 by positivity)
  exact hbase.trans (by nlinarith only [hh])

theorem eventually_actual_minimum_physical_scalar_data
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < margin) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.context.d ≤ 1 →
      a.context.E ≤ 1 ∧ 1/a.context.N ≤ a.context.E ∧
      1/a.context.N ≤ a.context.d ∧ 1/a.context.N ≤ a.context.U ∧
      a.context.U ≤ 1 ∧ a.context.U ≤ a.xs ∧
      a.context.L ≤ a.context.U ∧ a.context.N^(-(1:ℝ)) ≤ a.context.L ∧
      4 ≤ a.context.N*a.context.E*a.context.d := by
  let gamma := 1/C0
  have hgamma : 0 < gamma := one_div_pos.mpr hC0
  have hs : Tendsto (fun n : ℕ=>n+1) atTop atTop := tendsto_add_atTop_nat 1
  have hsR : Tendsto (fun n : ℕ=>(n+1:ℕ):ℕ→ℝ) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hs
  have hE := hs.eventually (eventually_coefficient_rpow_le (c:=1) (d:=gamma^2)
    (q:=-1) (r:=-(5:ℝ)/6+2*margin) (by positivity) (by linarith))
  have hd := hs.eventually (eventually_coefficient_rpow_le (c:=1) (d:=gamma)
    (q:=-1) (r:=-(1:ℝ)/6+margin) hgamma (by linarith))
  have hU := hs.eventually (eventually_coefficient_rpow_le (c:=C0^3) (d:=1)
    (q:=-3*margin) (r:=0) (by norm_num) (by linarith))
  have hP := hs.eventually (eventually_coefficient_rpow_le (c:=4) (d:=gamma^3)
    (q:=0) (r:=3*margin) (by positivity) (by linarith))
  have hL := hsR.eventually (comparison_physical_cap_length_eventually hm.le hgamma)
  filter_upwards [hE,hd,hU,hP,hL] with n hEn hdn hUn hPn hLn
  intro a hd1
  have hN : 1 ≤ a.context.N := by exact_mod_cast Nat.succ_pos n
  have hupper : a.context.E ≤ a.context.d^2/Real.sqrt a.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.context.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have hlower : gamma*a.context.N^(-(2:ℝ)/3+margin)*a.context.d ≤ a.context.E := by
    dsimp [gamma]
    have hh := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hh
  have hp := comparison_parent_scale_lower_bounds a.context.hN hgamma a.context.hd hlower hupper
  have hE1 : a.context.E ≤ 1 := by
    have hs1 : 1 ≤ Real.sqrt a.context.N := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN
    have hE0 := a.context.hE
    have hd0 := a.context.hd
    nlinarith [a.hupper]
  simp only [one_mul,Real.rpow_neg_one,←one_div] at hEn hdn
  have hElo : 1/a.context.N ≤ a.context.E := hEn.trans hp.2.1
  have hdlo : 1/a.context.N ≤ a.context.d := hdn.trans hp.1
  have hUlo : 1/a.context.N ≤ a.context.U := by
    unfold NativeOverlapContext.U comparisonSmallMass
    apply one_div_le_one_div_of_le (mul_pos a.context.hN a.context.hE)
    nlinarith
  have hU1 : a.context.U ≤ 1 := by
    unfold NativeOverlapContext.U comparisonSmallMass
    apply (div_le_one (mul_pos a.context.hN a.context.hE)).mpr
    simpa only [mul_comm] using (div_le_iff₀ a.context.hN).mp hElo
  have hUxs : a.context.U ≤ a.xs := by
    have hr := a.canonical_mass_small_ratio hC0
    simp only [Real.rpow_zero,one_mul] at hUn
    exact (div_le_one a.hxs).mp (hr.trans hUn)
  have hLlo : a.context.N^(-(1:ℝ)) ≤ a.context.L := by
    exact hLn a.context.d a.context.E a.context.hd hd1 a.context.hE hlower hupper
  have hprod := mul_le_mul hp.2.1 hp.1 (by positivity) a.context.hE.le
  have hprodN := mul_le_mul_of_nonneg_left hprod a.context.hN.le
  have he : a.context.N*((gamma^2*a.context.N^(-(5:ℝ)/6+2*margin))*
      (gamma*a.context.N^(-(1:ℝ)/6+margin)))=gamma^3*a.context.N^(3*margin) := by
    nth_rw 1 [←Real.rpow_one a.context.N]
    calc
      _ = gamma^3*(a.context.N^(1:ℝ)*a.context.N^(-(5:ℝ)/6+2*margin)*
        a.context.N^(-(1:ℝ)/6+margin)) := by ring
      _ = _ := by rw [←Real.rpow_add a.context.hN,←Real.rpow_add a.context.hN]; congr 2; ring
  rw [he] at hprodN
  simp only [Real.rpow_zero,mul_one] at hPn
  refine ⟨hE1,hElo,hdlo,hUlo,hU1,hUxs,min_le_left _ _,hLlo,?_⟩
  exact hPn.trans (by nlinarith only [hprodN])

end OAI.SKFluctuations.LaplaceWindowFormalization
