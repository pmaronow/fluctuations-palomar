module

public import ComparisonCapIntervals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem comparisonCap_comparable_density
    {N δ U L E d u v K : ℝ} (hN : 0<N) (hU : 0<U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hu : 0≤u) (hv : 0≤v)
    (hK : 1≤K) (hband : v+U≤K*(u+U)) :
    comparisonCap N δ U L E d v≤K^2*comparisonCap N δ U L E d u := by
  have huU : 0<u+U := by linarith
  have hvU : 0<v+U := by linarith
  have hKK : K≤K^2 := by nlinarith
  have hlin : v+U≤K^2*(u+U) :=
    hband.trans (mul_le_mul_of_nonneg_right hKK huU.le)
  have hs : (v+U)^2≤K^2*(u+U)^2 := by
    have hh := (sq_le_sq₀ hvU.le (mul_nonneg (by linarith : 0≤K) huU.le)).mpr hband
    nlinarith
  have hlin' := div_le_div_of_nonneg_right hlin hL.le
  have hs' := mul_le_mul_of_nonneg_left hs (div_nonneg (pow_nonneg hd 3) hE.le)
  have hsum := add_le_add hlin' hs'
  have hscaled := mul_le_mul_of_nonneg_left hsum (Real.rpow_pos_of_pos hN δ).le
  unfold comparisonCap
  convert hscaled using 1 <;> ring

theorem comparisonCap_mass_band_density
    {N δ U L E d a b K : ℝ} (hN : 0<N) (hU : 0<U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (ha : 0≤a)
    (hK : 1≤K) (hband : b+U≤K*(a+U)) {u v : ℝ}
    (hu : u∈Icc a b) (hv : v∈Icc a b) :
    comparisonCap N δ U L E d v≤K^2*comparisonCap N δ U L E d u := by
  apply comparisonCap_comparable_density hN hU hL hE hd (ha.trans hu.1) (ha.trans hv.1) hK
  have hm := mul_le_mul_of_nonneg_left (show a+U≤u+U by linarith [hu.1]) (by linarith : 0≤K)
  linarith [hv.2]

end OAI.SKFluctuations.LaplaceWindowFormalization
