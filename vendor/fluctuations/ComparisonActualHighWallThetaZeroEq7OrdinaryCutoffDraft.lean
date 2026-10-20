module

public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_cube_root_le_self_add_one_draft
    {x : ℝ} (hx : 0 ≤ x) : x^((1:ℝ)/3) ≤ x+1 := by
  by_cases hx1 : x ≤ 1
  · have H := Real.rpow_le_rpow hx hx1
      (by norm_num : (0:ℝ) ≤ 1/3)
    norm_num at H
    linarith only [H,hx]
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have H := Real.rpow_le_rpow_of_exponent_le hx1'
      (by norm_num : (1:ℝ)/3 ≤ 1)
    simpa only [Real.rpow_one] using H.trans (le_add_of_nonneg_right zero_le_one)

theorem comparison_eq7_ordinary_cutoff_payload_geometry_draft
    {N delta A y M P q Y C : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hA : 0 ≤ A) (hAupper : A ≤ N^(5+delta))
    (hy : 0 ≤ y) (hyA : y ≤ Y*A)
    (hM : 0 ≤ M) (hMupper : M ≤ 16*C*A)
    (hP : 0 ≤ P) (hPupper : P ≤ N)
    (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (hK : q^4*Y^2*(16*C)^2 ≤ N) :
    (q^2*y)^2*P*M^2 ≤ N^(22+4*delta) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have Hq := mul_le_mul_of_nonneg_left hyA (sq_nonneg q)
  have Hq2 := pow_le_pow_left₀
    (mul_nonneg (sq_nonneg q) hy) Hq 2
  have HM2 := pow_le_pow_left₀ hM hMupper 2
  have Hfirst := mul_le_mul Hq2 hPupper hP
    (sq_nonneg (q^2*(Y*A)))
  have Hall := mul_le_mul Hfirst HM2 (sq_nonneg M)
    (by positivity : 0 ≤ (q^2*(Y*A))^2*N)
  have hA4 := pow_le_pow_left₀ hA hAupper 4
  have hPow4 : (N^(5+delta))^4 = N^(20+4*delta) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hNp.le]
    congr 1
    ring
  rw [hPow4] at hA4
  have HApow := mul_le_mul_of_nonneg_left hA4
    (show 0 ≤ q^4*Y^2*(16*C)^2*N by positivity)
  have HK := mul_le_mul_of_nonneg_right hK
    (show 0 ≤ N*N^(20+4*delta) by positivity)
  have hPow22 : N*N*N^(20+4*delta) = N^(22+4*delta) := by
    calc
      _ = N^(1:ℝ)*N^(1:ℝ)*N^(20+4*delta) := by simp
      _ = N^((1:ℝ)+1+20+4*delta) := by
        rw [←Real.rpow_add hNp, ←Real.rpow_add hNp]
        congr 1
        ring
      _ = _ := by congr 1; ring
  simp only [←mul_assoc] at HK
  rw [hPow22] at HK
  have Hidentity :
      (q^2*(Y*A))^2*N*(16*C*A)^2 =
        (q^4*Y^2*(16*C)^2)*N*A^4 := by ring
  rw [Hidentity] at Hall
  nlinarith only [Hall,HApow,HK]

theorem comparison_eq7_ordinary_cutoff_numeric_gates_eventually_draft
    (q Y C : ℝ) :
    ∀ᶠ N : ℝ in atTop,
      1 ≤ N ∧ 72 ≤ N^3 ∧ q^4*Y^2*(16*C)^2 ≤ N := by
  filter_upwards [eventually_ge_atTop
    (max (5:ℝ) (q^4*Y^2*(16*C)^2))] with N hN
  have h5 : (5:ℝ) ≤ N := (le_max_left _ _).trans hN
  have hK : q^4*Y^2*(16*C)^2 ≤ N :=
    (le_max_right _ _).trans hN
  have Hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) h5 3
  refine ⟨by linarith only [h5], ?_,hK⟩
  norm_num at Hpow
  linarith only [Hpow]

theorem comparison_eq7_ordinary_cutoff_from_payload_draft
    {N delta E lam beta payload : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hE : N^(-(5:ℝ)) ≤ E)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hbeta : beta = 30+10*delta)
    (hN3 : 72 ≤ N^3)
    (hpayload : 0 ≤ payload)
    (hpayloadBound : payload ≤ N^(22+4*delta)) :
    lam*(18*(payload^((1:ℝ)/3)+2)*N^(-beta)) ≤ E := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNpow : 1 ≤ N^(22+4*delta) :=
    Real.one_le_rpow hN (by linarith only [hdelta])
  have hroot := comparison_eq7_cube_root_le_self_add_one_draft hpayload
  have hterm : payload^((1:ℝ)/3)+2 ≤
      4*N^(22+4*delta) := by
    linarith only [hroot,hpayloadBound,hNpow]
  have hcoeff : 0 ≤ 18*N^(-beta) := by positivity
  have Hterm := mul_le_mul_of_nonneg_left hterm hcoeff
  have HtermLam := mul_le_mul_of_nonneg_left Hterm hlam
  have Hlam := mul_le_mul_of_nonneg_right hlam1
    (show 0 ≤ 72*N^(22+4*delta)*N^(-beta) by positivity)
  have hPowProd : N^(22+4*delta)*N^(-beta) =
      N^(22+4*delta-beta) := by
    rw [←Real.rpow_add hNp]
    simp only [sub_eq_add_neg]
  have Hexp := Real.rpow_le_rpow_of_exponent_le hN
    (show 22+4*delta-beta ≤ -(8:ℝ) by rw [hbeta]; linarith only [hdelta])
  have Hexp72 := mul_le_mul_of_nonneg_left Hexp
    (by norm_num : (0:ℝ) ≤ 72)
  have Hn3 := mul_le_mul_of_nonneg_right hN3
    (Real.rpow_nonneg hNp.le (-(8:ℝ)))
  have hPow53 : N^3*N^(-(8:ℝ)) = N^(-(5:ℝ)) := by
    rw [←Real.rpow_natCast N 3, ←Real.rpow_add hNp]
    congr 1
    norm_num
  rw [hPow53] at Hn3
  have Hcut : 72*N^(22+4*delta)*N^(-beta) ≤ E := by
    rw [mul_assoc,hPowProd]
    exact (Hexp72.trans Hn3).trans hE
  nlinarith only [HtermLam,Hlam,Hcut]

end OAI.SKFluctuations.LaplaceWindowFormalization
