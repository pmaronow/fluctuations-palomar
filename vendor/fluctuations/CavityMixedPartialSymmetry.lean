module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Filter Set
open scoped Topology

def pairGradientMap : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem actual_mixed_partials_eq (f A B AA AB BA BB : ℝ × ℝ → ℝ)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (h0 : (0,0) ∈ U)
    (hA : Continuous A) (hB : Continuous B)
    (hAA : Continuous AA) (hAB : Continuous AB)
    (hBA : Continuous BA) (hBB : Continuous BB)
    (dfA : ∀ p ∈ U, HasDerivAt (fun s => f (s,p.2)) (A p) p.1)
    (dfB : ∀ p ∈ U, HasDerivAt (fun t => f (p.1,t)) (B p) p.2)
    (dAA : ∀ p ∈ U, HasDerivAt (fun s => A (s,p.2)) (AA p) p.1)
    (dAB : ∀ p ∈ U, HasDerivAt (fun t => A (p.1,t)) (AB p) p.2)
    (dBA : ∀ p ∈ U, HasDerivAt (fun s => B (s,p.2)) (BA p) p.1)
    (dBB : ∀ p ∈ U, HasDerivAt (fun t => B (p.1,t)) (BB p) p.2) :
    AB (0,0) = BA (0,0) := by
  have total (g X Y : ℝ × ℝ → ℝ) (hX : Continuous X) (hY : Continuous Y)
      (dx : ∀ p ∈ U, HasDerivAt (fun s => g (s,p.2)) (X p) p.1)
      (dy : ∀ p ∈ U, HasDerivAt (fun t => g (p.1,t)) (Y p) p.2)
      (p : ℝ × ℝ) (hp : p ∈ U) :
      HasFDerivAt g (pairGradientMap (X p,Y p)) p := by
    have h := hasStrictFDerivAt_uncurry_coprod
      (f := fun s t => g (s,t))
      (f₁ := fun s t => X (s,t) • (1 : ℝ →L[ℝ] ℝ))
      (f₂ := fun s t => Y (s,t) • (1 : ℝ →L[ℝ] ℝ))
      (by
        filter_upwards [hU.mem_nhds hp] with z hz
        change HasFDerivAt (fun s => g (s,z.2)) (X z • (1 : ℝ →L[ℝ] ℝ)) z.1
        apply (dx z hz).hasFDerivAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro r
        simp [smul_eq_mul,mul_comm])
      (by
        filter_upwards [hU.mem_nhds hp] with z hz
        change HasFDerivAt (fun t => g (z.1,t)) (Y z • (1 : ℝ →L[ℝ] ℝ)) z.2
        apply (dy z hz).hasFDerivAt.congr_fderiv
        apply ContinuousLinearMap.ext
        intro r
        simp [smul_eq_mul,mul_comm])
      (by fun_prop) (by fun_prop)
    have he : ((X p • (1 : ℝ →L[ℝ] ℝ)).coprod (Y p • (1 : ℝ →L[ℝ] ℝ))) =
        pairGradientMap (X p,Y p) := by
      apply ContinuousLinearMap.ext
      intro z
      simp [pairGradientMap,ContinuousLinearMap.coprod_apply,mul_comm]
    exact he ▸ h.hasFDerivAt
  have hf : ∀ᶠ p in 𝓝 (0,0), HasFDerivAt f (pairGradientMap (A p,B p)) p := by
    filter_upwards [hU.mem_nhds h0] with p hp
    exact total f A B hA hB dfA dfB p hp
  have hx := total A AA AB hAA hAB dAA dAB (0,0) h0
  have hy := total B BA BB hBA hBB dBA dBB (0,0) h0
  have hsecond := pairGradientMap.hasFDerivAt.comp (0,0) (hx.prodMk hy)
  have hs := second_derivative_symmetric_of_eventually hf hsecond (1,0) (0,1)
  simpa [pairGradientMap,ContinuousLinearMap.coprod_apply] using hs.symm

end OAI.SKFluctuations.Cavity
