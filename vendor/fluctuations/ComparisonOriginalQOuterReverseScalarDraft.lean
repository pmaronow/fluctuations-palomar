module

public import ComparisonReverseInterpolationSize
public import ConcreteWallPowerBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 14000000

namespace OriginalQOuterReverseDraft

theorem concrete_error_div_d_cube_eq_power_draft
    (m : ℝ) {k : ℕ} (hk : 0 < k) :
    wallHighError m k/(wallHighD m k)^3 =
      (k:ℝ)^(-(1:ℝ)/3-20*m) := by
  have hN : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  rw [wallHighError_eq m hk]
  unfold wallHighD
  rw [←Real.rpow_natCast,←Real.rpow_mul hN.le,
      ←Real.rpow_sub hN]
  congr 1
  ring

theorem local_diameter_concrete_lower_draft
    {N m delta K L v E d Dloc : ℝ}
    (hN : 1 ≤ N) (hd : 0 < d) (hE : 0 < E)
    (hK : 4 ≤ K) (hL : 1 ≤ L)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hwall : E/d^3 = N^(-(1:ℝ)/3-20*m))
    (hD : Dloc = 9*K*L*E/(N^delta*d^3*v)) :
    N^(-(delta+(1:ℝ)/3+20*m)) ≤ Dloc := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hpow : 0 < N^delta := Real.rpow_pos_of_pos hNp _
  have hrate : 0 < N^(-(delta+(1:ℝ)/3+20*m)) :=
    Real.rpow_pos_of_pos hNp _
  have hfactor : 1 ≤ 9*K*L/v := by
    have hKL : 1 ≤ 9*K*L := by nlinarith only [hK,hL]
    exact (le_div_iff₀ hv).mpr (by linarith only [hKL,hv1])
  have Hmul := mul_le_mul_of_nonneg_right hfactor hrate.le
  calc
    N^(-(delta+(1:ℝ)/3+20*m)) =
        1*N^(-(delta+(1:ℝ)/3+20*m)) := by ring
    _ ≤ (9*K*L/v)*N^(-(delta+(1:ℝ)/3+20*m)) := Hmul
    _ = Dloc := by
      rw [hD]
      have Hpow : N^(-(delta+(1:ℝ)/3+20*m)) =
          N^(-delta)*N^(-(1:ℝ)/3-20*m) := by
        rw [←Real.rpow_add hNp]
        congr 1
        ring
      rw [Hpow,←hwall,Real.rpow_neg hNp.le]
      field_simp [hv.ne',hd.ne',hpow.ne']

theorem reverse_atom_of_local_energy_and_ratio_draft
    {ell : ℕ} (hell : 2 < ell)
    {N d E delta e v K L H q y Dloc T eps : ℝ}
    (hN : 1 ≤ N) (hd : 0 < d) (hE : 0 < E)
    (he : 0 ≤ e) (hv : 0 < v) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hq : 1 ≤ q) (hy : 0 < y) (hDpos : 0 < Dloc)
    (henergy : e*v ≤ 2*L*d^3)
    (hheight : y ≤ H*v)
    (hD : Dloc = 9*K*L*E/(N^delta*d^3*v))
    (hratio : y/Dloc ≤ N^T)
    (horder : T/((ell:ℝ)-1) ≤ eps) :
    e*(K*v)*comparisonReverseMoment ell Dloc q y ≤
      18*H*K^2*(2*q)^4*L^2*(N^eps/N^delta)*E := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hNdelta : 0 < N^delta := Real.rpow_pos_of_pos hNp _
  have hInterp := comparison_reverse_polynomial_loss
    hell hN hDpos hq hy hratio horder
  have hmass : e*y ≤ 2*H*L*d^3 := by
    calc
      e*y ≤ e*(H*v) := mul_le_mul_of_nonneg_left hheight he
      _ = H*(e*v) := by ring
      _ ≤ H*(2*L*d^3) := mul_le_mul_of_nonneg_left henergy hH
      _ = _ := by ring
  have hcoef : 0 ≤ 9*K^2*L*E/(N^delta*d^3) := by positivity
  have Hmass := mul_le_mul_of_nonneg_left hmass hcoef
  have hidentity : e*(K*v)*Dloc*y =
      (9*K^2*L*E/(N^delta*d^3))*(e*y) := by
    rw [hD]
    field_simp [hNdelta.ne',hd.ne',hv.ne']
  have hgeom : e*(K*v)*Dloc*y ≤
      18*H*K^2*L^2*E/N^delta := by
    rw [hidentity]
    calc
      _ ≤ (9*K^2*L*E/(N^delta*d^3))*(2*H*L*d^3) := Hmass
      _ = _ := by field_simp [hNdelta.ne',hd.ne']; ring
  have hprod : 0 ≤ e*(K*v) := by positivity
  have Hinterp := mul_le_mul_of_nonneg_left hInterp hprod
  have Hgeom := mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ (2*q)^4*N^eps by positivity)
  calc
    _ ≤ e*(K*v)*((2*q)^4*Dloc*y*N^eps) := Hinterp
    _ = ((2*q)^4*N^eps)*(e*(K*v)*Dloc*y) := by ring
    _ ≤ ((2*q)^4*N^eps)*(18*H*K^2*L^2*E/N^delta) := Hgeom
    _ = _ := by ring

end OriginalQOuterReverseDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
