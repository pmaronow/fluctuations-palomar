module

public import Mathlib

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization

def reciprocalSquareFloor (A B q : ℝ) : ℝ := A/(q+B)^2

def harmonicBarrierRadius (B t r v : ℝ) : ℝ :=
  ((1-t)/(r+B)+t/(v+B))⁻¹-B

def harmonicBarrierDerivative (B t r v dr dv : ℝ) : ℝ :=
  ((1-t)*dr/(r+B)^2+t*dv/(v+B)^2)/((1-t)/(r+B)+t/(v+B))^2

theorem harmonicBarrierDenominator_pos {B t r v : ℝ}
    (hB : 0<B) (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : 0 ≤ r) (hv : 0 ≤ v) :
    0<(1-t)/(r+B)+t/(v+B) := by
  have hR : 0<r+B := by linarith
  have hV : 0<v+B := by linarith
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [←h]
    simpa using one_div_pos.mpr hR
  · exact add_pos_of_nonneg_of_pos (div_nonneg (sub_nonneg.mpr ht.2) hR.le) (div_pos h hV)

theorem harmonicBarrierRadius_floor {A B t r v : ℝ}
    (hB : 0<B) (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : 0 ≤ r) (hv : 0 ≤ v) :
    reciprocalSquareFloor A B (harmonicBarrierRadius B t r v)=
      A*((1-t)/(r+B)+t/(v+B))^2 := by
  have hd := (harmonicBarrierDenominator_pos hB ht hr hv).ne'
  unfold reciprocalSquareFloor harmonicBarrierRadius
  rw [sub_add_cancel]
  field_simp

theorem harmonicBarrierRadius_density_jensen {A B t r v : ℝ}
    (hA : 0 ≤ A) (hB : 0<B) (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : 0 ≤ r) (hv : 0 ≤ v) :
    reciprocalSquareFloor A B (harmonicBarrierRadius B t r v) ≤ 
      (1-t)*reciprocalSquareFloor A B r+t*reciprocalSquareFloor A B v := by
  rw [harmonicBarrierRadius_floor hB ht hr hv]
  let R := (r+B)⁻¹
  let V := (v+B)⁻¹
  have hh : ((1-t)*R+t*V)^2 ≤ (1-t)*R^2+t*V^2 := by
    nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (R-V))]
  have hm := mul_le_mul_of_nonneg_left hh hA
  convert hm using 1 <;> simp only [reciprocalSquareFloor,div_eq_mul_inv,inv_pow,R,V] <;> ring

theorem harmonicBarrierRadius_derivative {B t s : ℝ} {r v : ℝ → ℝ} {dr dv : ℝ}
    (hr : HasDerivAt r dr s) (hv : HasDerivAt v dv s)
    (hR : r s+B ≠ 0) (hV : v s+B ≠ 0)
    (hD : (1-t)/(r s+B)+t/(v s+B) ≠ 0) :
    HasDerivAt (fun u => harmonicBarrierRadius B t (r u) (v u))
      (harmonicBarrierDerivative B t (r s) (v s) dr dv) s := by
  have hden := (((hr.add_const B).inv hR).const_mul (1-t)).add (((hv.add_const B).inv hV).const_mul t)
  have hi := (hden.inv hD).sub_const B
  convert hi using 1
  · ext u
    simp only [harmonicBarrierRadius,Pi.add_apply,Pi.inv_apply,div_eq_mul_inv]
  · simp only [harmonicBarrierDerivative,Pi.add_apply,Pi.inv_apply,div_eq_mul_inv]
    ring

theorem harmonicBarrierDerivative_floor_identity {A B t r v dr dv : ℝ}
    (hB : 0<B) (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : 0 ≤ r) (hv : 0 ≤ v) :
    reciprocalSquareFloor A B (harmonicBarrierRadius B t r v)*
        harmonicBarrierDerivative B t r v dr dv=
      (1-t)*reciprocalSquareFloor A B r*dr+t*reciprocalSquareFloor A B v*dv := by
  let d := (1-t)/(r+B)+t/(v+B)
  have hd : d ≠ 0 := (harmonicBarrierDenominator_pos hB ht hr hv).ne'
  rw [harmonicBarrierRadius_floor hB ht hr hv]
  unfold harmonicBarrierDerivative reciprocalSquareFloor
  change A*d^2*(((1-t)*dr/(r+B)^2+t*dv/(v+B)^2)/d^2)=_
  have hc : d^2*(((1-t)*dr/(r+B)^2+t*dv/(v+B)^2)/d^2)=
      (1-t)*dr/(r+B)^2+t*dv/(v+B)^2 := by
    rw [div_eq_mul_inv,←mul_assoc,mul_comm (d^2) _,mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 2 hd),mul_one]
  rw [mul_assoc,hc]
  ring

theorem harmonicBarrierDerivative_slope_bounds {A B t r v dr dv lower : ℝ}
    (hA : 0<A) (hB : 0<B) (ht : t ∈ Set.Icc (0:ℝ) 1) (hr : 0 ≤ r) (hv : 0 ≤ v)
    (hlower : 0 ≤ lower)
    (hdr : dr ∈ Set.Icc lower (reciprocalSquareFloor A B r)⁻¹)
    (hdv : dv ∈ Set.Icc lower (reciprocalSquareFloor A B v)⁻¹) :
    harmonicBarrierDerivative B t r v dr dv ∈ 
      Set.Icc lower (reciprocalSquareFloor A B (harmonicBarrierRadius B t r v))⁻¹ := by
  have hkR : 0<reciprocalSquareFloor A B r := by unfold reciprocalSquareFloor; positivity
  have hkV : 0<reciprocalSquareFloor A B v := by unfold reciprocalSquareFloor; positivity
  have hkH : 0<reciprocalSquareFloor A B (harmonicBarrierRadius B t r v) := by
    rw [harmonicBarrierRadius_floor hB ht hr hv]
    exact mul_pos hA (sq_pos_of_pos (harmonicBarrierDenominator_pos hB ht hr hv))
  have he := harmonicBarrierDerivative_floor_identity (A := A) (dr := dr) (dv := dv) hB ht hr hv
  have hlowR := mul_le_mul_of_nonneg_left hdr.1 hkR.le
  have hlowV := mul_le_mul_of_nonneg_left hdv.1 hkV.le
  have hl := add_le_add (mul_le_mul_of_nonneg_left hlowR (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hlowV ht.1)
  have hj := mul_le_mul_of_nonneg_right (harmonicBarrierRadius_density_jensen hA.le hB ht hr hv) hlower
  have hupR : reciprocalSquareFloor A B r*dr ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdr.2 hkR.le
    simpa only [mul_inv_cancel₀ hkR.ne'] using hh
  have hupV : reciprocalSquareFloor A B v*dv ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hdv.2 hkV.le
    simpa only [mul_inv_cancel₀ hkV.ne'] using hh
  have hu := add_le_add (mul_le_mul_of_nonneg_left hupR (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hupV ht.1)
  constructor
  · have hstep : reciprocalSquareFloor A B (harmonicBarrierRadius B t r v)*lower ≤ 
        reciprocalSquareFloor A B (harmonicBarrierRadius B t r v)*harmonicBarrierDerivative B t r v dr dv := by
      rw [he]
      nlinarith
    exact (mul_le_mul_iff_right₀ hkH).mp hstep
  · have hstep : reciprocalSquareFloor A B (harmonicBarrierRadius B t r v)*
        harmonicBarrierDerivative B t r v dr dv ≤ 1 := by rw [he]; nlinarith
    simpa only [mul_one] using (le_inv_mul_iff₀ hkH).mpr hstep

end OAI.SKFluctuations.LaplaceWindowFormalization
