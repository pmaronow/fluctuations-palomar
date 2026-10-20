module

public import ComparisonOuterPhysicalLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

theorem comparison_physical_energy_product_lower {N m gamma d E : ℝ}
    (hN : 0 < N) (hgamma : 0 < gamma) (hd : 0 < d)
    (hlower : gamma*N^(-(2:ℝ)/3+m)*d ≤ E)
    (hupper : E ≤ d^2/Real.sqrt N) : gamma^3*N^(3*m) ≤ N*d*E := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hdlow : gamma*N^(-(1:ℝ)/6+m) ≤ d := by
    have hh := mul_le_mul_of_nonneg_right hlower hs.le
    have hu := (le_div_iff₀ hs).mp hupper
    have he : gamma*N^(-(2:ℝ)/3+m)*d*Real.sqrt N=gamma*N^(-(1:ℝ)/6+m)*d := by
      rw [Real.sqrt_eq_rpow]
      calc
        _=gamma*(N^(-(2:ℝ)/3+m)*N^((1:ℝ)/2))*d := by ring
        _=_ := by rw [←Real.rpow_add hN];congr 2;ring
    rw [he] at hh
    nlinarith
  have hd2 := pow_le_pow_left₀ (mul_pos hgamma (Real.rpow_pos_of_pos hN _)).le hdlow 2
  have he := mul_le_mul_of_nonneg_left hlower (mul_pos hN hd).le
  have hh := mul_le_mul_of_nonneg_left hd2 (show 0 ≤ N*gamma*N^(-(2:ℝ)/3+m) by positivity)
  have hp : N*gamma*N^(-(2:ℝ)/3+m)*(gamma*N^(-(1:ℝ)/6+m))^2=gamma^3*N^(3*m) := by
    rw [mul_pow,←Real.rpow_mul_natCast hN.le]
    nth_rw 1 [←Real.rpow_one N]
    calc
      _=gamma^3*(N^(1:ℝ)*N^(-(2:ℝ)/3+m)*N^((-(1:ℝ)/6+m)*(2:ℝ))) := by ring
      _=_ := by rw [←Real.rpow_add hN,←Real.rpow_add hN];congr 1;congr 1;ring
  rw [hp] at hh
  nlinarith

theorem comparison_physical_outer_room_eventually {m gamma delta : ℝ}
    (hm : 0 < m) (hgamma : 0 < gamma) (hdelta : 0 ≤ delta) :
    ∀ᶠ N : ℝ in atTop, ∀ d E v : ℝ, 0 < d → d ≤ 1 →
      gamma*N^(-(2:ℝ)/3+m)*d ≤ E → E ≤ d^2/Real.sqrt N →
      Real.sqrt N*E/d ≤ v →
      comparisonSmallMass N E ≤ 1 ∧ E ≤ N^delta*d^3*v^2 := by
  have ht := (tendsto_rpow_atTop (show 0 < 3*m by linarith)).eventually_ge_atTop (1/gamma^3)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with N hN hpow
  intro d E v hd hd1 hlower hupper hv
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hE : 0 < E := (mul_pos (mul_pos hgamma (Real.rpow_pos_of_pos hNp _)) hd).trans_le hlower
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNp
  have hprod := comparison_physical_energy_product_lower hNp hgamma hd hlower hupper
  have hroom : 1 ≤ N*d*E := by
    have hh := mul_le_mul_of_nonneg_left hpow (pow_pos hgamma 3).le
    have he : gamma^3*(1/gamma^3)=1 := by field_simp
    rw [he] at hh
    exact hh.trans hprod
  have hNE : 1 ≤ N*E := hroom.trans (by nlinarith)
  constructor
  · unfold comparisonSmallMass
    exact (div_le_one (mul_pos hNp hE)).mpr hNE
  · have hva : 0 ≤ Real.sqrt N*E/d := by positivity
    have hv2 := pow_le_pow_left₀ hva hv 2
    have heq : (Real.sqrt N*E/d)^2=N*E^2/d^2 := by rw [div_pow,mul_pow,Real.sq_sqrt hNp.le]
    rw [heq] at hv2
    have hdiv := (div_le_iff₀ (sq_pos_of_pos hd)).mp hv2
    have hh := mul_le_mul_of_nonneg_left hdiv hd.le
    have hroomE := mul_le_mul_of_nonneg_right hroom hE.le
    have hNdelta : 1 ≤ N^delta := Real.one_le_rpow hN hdelta
    have hscale := mul_le_mul_of_nonneg_right hNdelta (mul_nonneg (pow_pos hd 3).le (sq_nonneg v))
    nlinarith

theorem comparison_local_diameter_spatial_bound {N delta d E v J : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hv : 0 < v) (hJ : 0 ≤ J)
    (hroom : E ≤ N^delta*d^3*v^2) :
    J*N^(-delta)*E/(d^3*v) ≤ J*v := by
  apply (div_le_iff₀ (mul_pos (pow_pos hd 3) hv)).mpr
  have hh := mul_le_mul_of_nonneg_left hroom (mul_nonneg hJ (Real.rpow_pos_of_pos hN (-delta)).le)
  have he : J*N^(-delta)*(N^delta*d^3*v^2)=J*d^3*v^2 := by
    rw [Real.rpow_neg hN.le]
    field_simp
  rw [he] at hh
  nlinarith

theorem comparison_local_diameter_reverse_ratio {N delta d E v J y : ℝ}
    (hN : 1 ≤ N) (hd : 0 < d) (hE : 0 < E) (hv : 0 < v)
    (hU : comparisonSmallMass N E ≤ 1) (hJ : d^3*v ≤ J)
    (hy : 0 ≤ y) (hyN : y ≤ N) :
    y/(J*N^(-delta)*E/(d^3*v)) ≤ N^(delta+2) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hJp : 0 < J := (mul_pos (pow_pos hd 3) hv).trans_le hJ
  have hEp : 1/N ≤ E := by
    have hh := (div_le_one (mul_pos hNp hE)).mp hU
    exact (div_le_iff₀ hNp).mpr (by nlinarith)
  have hlow : N^(-(delta+1)) ≤ J*N^(-delta)*E/(d^3*v) := by
    have hj := mul_le_mul_of_nonneg_right hJ (mul_pos (Real.rpow_pos_of_pos hNp (-delta)) hE).le
    have hle : N^(-delta)*E ≤ J*N^(-delta)*E/(d^3*v) := by
      apply (le_div_iff₀ (mul_pos (pow_pos hd 3) hv)).mpr
      nlinarith
    have he := mul_le_mul_of_nonneg_left hEp (Real.rpow_pos_of_pos hNp (-delta)).le
    have hid : N^(-delta)*(1/N)=N^(-(delta+1)) := by
      rw [mul_one_div]
      nth_rw 2 [←Real.rpow_one N]
      rw [←Real.rpow_sub hNp]
      congr 1
      ring
    rw [hid] at he
    exact he.trans hle
  have hD : 0 < J*N^(-delta)*E/(d^3*v) := by positivity
  have hh := comparison_reverse_ratio_of_scales hNp hD hy hlow (by simpa using hyN : y ≤ N^(1:ℝ))
  convert hh using 1 <;> congr 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
