module

public import ComparisonSignedCavityWholeLawHolder
public import ComparisonSignedCavitySmallCutAtomicKernels

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S]

theorem disorderExpect_initial_low_even_moment_interpolate
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (F : T.Assignment→ℝ) (p : ℕ) (hp : 0<p)
    {D R : ℝ} (hD : 0≤D) (hR : 0≤R)
    (Htwo : T.disorderExpect w φ v q (fun σ=>(F σ)^2) x≤D^2)
    (Hhigh : T.disorderExpect w φ v q (fun σ=>|F σ|^(4*p-2)) x≤R^(4*p-2)) :
    T.disorderExpect w φ v q (fun σ=>|F σ|^(2*p)) x≤D*R^(2*p-1) := by
  have hexp : 2*p-1+1=2*p:=by omega
  have hexp2 : (2*p-1)*2=4*p-2:=by omega
  have H:=T.disorderExpect_mul_sq_le hw φ ho v q
    (fun σ=>|F σ|) (fun σ=>|F σ|^(2*p-1)) x
  have Hprod : (fun σ=>|F σ| *|F σ|^(2*p-1))=(fun σ=>|F σ|^(2*p)):=by
    funext σ
    rw [←pow_succ',hexp]
  have Hpow : (fun σ=>(|F σ|^(2*p-1))^2)=(fun σ=>|F σ|^(4*p-2)):=by
    funext σ
    rw [←pow_mul,hexp2]
  simp_rw [sq_abs] at H
  rw [Hprod,Hpow] at H
  have Hnonneg:=wholeLaw_disorderExpect_nonneg hw φ T ho v q
    (fun σ=>|F σ|^(4*p-2)) (fun σ=>pow_nonneg (abs_nonneg _) _) x
  have HB : (T.disorderExpect w φ v q (fun σ=>|F σ|^(2*p)) x)^2≤(D*R^(2*p-1))^2:=by
    apply H.trans
    calc
      _ ≤ D^2*T.disorderExpect w φ v q (fun σ=>|F σ|^(4*p-2)) x :=
        mul_le_mul_of_nonneg_right Htwo Hnonneg
      _ ≤ D^2*R^(4*p-2):=mul_le_mul_of_nonneg_left Hhigh (sq_nonneg D)
      _ = _:=by rw [mul_pow,←pow_mul,hexp2]
  exact (sq_le_sq₀ (wholeLaw_disorderExpect_nonneg hw φ T ho v q
    (fun σ=>|F σ|^(2*p)) (fun σ=>pow_nonneg (abs_nonneg _) _) x)
    (mul_nonneg hD (pow_nonneg hR _))).mp HB

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

def originalInitialLowMomentModulus (D R : ℝ) (order : ℕ) : ℝ :=
  (D/R)^(((order:ℝ))⁻¹)

theorem original_initial_low_moment_modulus_nonneg {D R : ℝ} (hD : 0≤D) (hR : 0≤R) (order : ℕ) :
    0≤originalInitialLowMomentModulus D R order := Real.rpow_nonneg (div_nonneg hD hR) _

theorem original_initial_low_moment_modulus_pow {D R : ℝ} (hD : 0≤D) (hR : 0<R)
    (order : ℕ) (horder : 0<order) :
    (originalInitialLowMomentModulus D R order)^order=D/R :=
  Real.rpow_inv_natCast_pow (div_nonneg hD hR.le) horder.ne'

theorem original_initial_low_interpolation_scale_pow {D R : ℝ} (hD : 0≤D) (hR : 0<R)
    (order : ℕ) (horder : 0<order) :
    (R*originalInitialLowMomentModulus D R order)^order=D*R^(order-1) := by
  rw [mul_pow,original_initial_low_moment_modulus_pow hD hR order horder]
  have he : order-1+1=order:=by omega
  rw [←he,pow_succ]
  field_simp
  simp only [Nat.add_sub_cancel_right]
  ring

theorem native_initial_old_error_abs_eq_centered_low
    (n U : ℕ) (b h S : ℕ→ℝ) {j : ℕ} (hj : j<U) (σ τ : Spin n×Bool) :
    |nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h
      (fun k=>h k+b k*S k)) j σ τ| =
      |b j| *|deletedOverlap n (joinSpin σ) (joinSpin τ)-S j| := by
  unfold nativeRestRowKernel nativeSmallCutOldErrorRestKernel
  rw [ite_eq_left hj]
  rw [show h j+b j*deletedOverlap n (joinSpin (σ.1,false)) (joinSpin (τ.1,false))-
      (h j+b j*S j)=b j*(deletedOverlap n (joinSpin (σ.1,false)) (joinSpin (τ.1,false))-S j) by ring]
  rw [←native_deletedOverlap_row_independent n σ τ]
  simp only [abs_mul,abs_spinValue,mul_one]

end OAI.SKFluctuations.Cavity
