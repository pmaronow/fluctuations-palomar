module

public import ComparisonSignedCavityActualOriginalHighResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity

theorem native_numeric_two_gram_add
    (PA PB FA FB k LA LB : ℝ) (hPA : 0 ≤ PA) (hPB : 0 ≤ PB)
    (hFA : 0 ≤ FA) (hFB : 0 ≤ FB)
    (hA : LA^2 ≤ k^2*PA*FA) (hB : LB^2 ≤ k^2*PB*FB) :
    (LA+LB)^2 ≤ k^2*(PA+PB)*(FA+FB) := by
  let a:=Real.sqrt PA
  let b:=Real.sqrt PB
  let u:=Real.sqrt FA
  let v:=Real.sqrt FB
  have ha : 0 ≤ a:=Real.sqrt_nonneg _
  have hb : 0 ≤ b:=Real.sqrt_nonneg _
  have hu : 0 ≤ u:=Real.sqrt_nonneg _
  have hv : 0 ≤ v:=Real.sqrt_nonneg _
  have ha2 : a^2=PA:=Real.sq_sqrt hPA
  have hb2 : b^2=PB:=Real.sq_sqrt hPB
  have hu2 : u^2=FA:=Real.sq_sqrt hFA
  have hv2 : v^2=FB:=Real.sq_sqrt hFB
  have HCa : (abs k*a*u)^2=k^2*PA*FA:=by rw [mul_pow,mul_pow,sq_abs,ha2,hu2]
  have HCb : (abs k*b*v)^2=k^2*PB*FB:=by rw [mul_pow,mul_pow,sq_abs,hb2,hv2]
  have hLa : abs LA ≤ abs k*a*u:=by
    have hp : 0 ≤ abs k*a*u:=mul_nonneg (mul_nonneg (abs_nonneg _) ha) hu
    rw [←HCa] at hA
    nlinarith [sq_abs LA,abs_nonneg LA]
  have hLb : abs LB ≤ abs k*b*v:=by
    have hp : 0 ≤ abs k*b*v:=mul_nonneg (mul_nonneg (abs_nonneg _) hb) hv
    rw [←HCb] at hB
    nlinarith [sq_abs LB,abs_nonneg LB]
  have HC : (a*u+b*v)^2 ≤ (PA+PB)*(FA+FB):=by
    have HI : (PA+PB)*(FA+FB)-(a*u+b*v)^2=(a*v-b*u)^2:=by
      rw [←ha2,←hb2,←hu2,←hv2]
      ring
    nlinarith [sq_nonneg (a*v-b*u)]
  have HS : abs (LA+LB) ≤ abs k*(a*u+b*v):=by
    calc
      _ ≤ abs LA+abs LB:=abs_add_le _ _
      _ ≤ abs k*a*u+abs k*b*v:=add_le_add hLa hLb
      _ = _:=by ring
  have HP : 0 ≤ abs k*(a*u+b*v):=mul_nonneg (abs_nonneg _) (add_nonneg (mul_nonneg ha hu) (mul_nonneg hb hv))
  have HS2 : (LA+LB)^2 ≤ (abs k*(a*u+b*v))^2:=by nlinarith [sq_abs (LA+LB),abs_nonneg (LA+LB)]
  calc
    _ ≤ _:=HS2
    _ = k^2*(a*u+b*v)^2:=by rw [mul_pow,sq_abs]
    _ ≤ k^2*((PA+PB)*(FA+FB)):=mul_le_mul_of_nonneg_left HC (sq_nonneg _)
    _ = _:=by ring

theorem native_numeric_gram_coefficient_mono
    (P F kt k L : ℝ) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (hkt : 0 ≤ kt) (hk : kt ≤ k) (H : L^2 ≤ kt^2*P*F) :
    L^2 ≤ k^2*P*F := by
  have Hsq : kt^2 ≤ k^2:=by nlinarith
  exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right Hsq hP) hF)

end OAI.SKFluctuations.Cavity
