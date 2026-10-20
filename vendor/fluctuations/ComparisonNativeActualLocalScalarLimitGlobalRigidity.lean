module

public import ComparisonGlobalScalarRigidity
public import ComparisonNativeActualLocalScalarLimitLawIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open NativeOverlapMinimum
open scoped Topology
set_option maxHeartbeats 8000000

namespace ActualInheritedLocalScalarLimitData

theorem global_profile_rigidity_of_coupled_laws
    {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualInheritedLocalScalarLimitData hT S M htotal)
    (hUV : d.U.mass =ᵐ[volume] d.V.mass) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0))
    (hvirtual : ∀a b,0 ≤ a → a < b →
      a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma) a b)) :
    (∀t > 0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) ∧
    (∀t > 0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) := by
  let A := S^3*(scalarTailSpatialJet hT d.beta 4 0 0)^2
  let B := 2*S^2*(scalarTailSpatialJet hT d.beta 2 0 0)^3
  have hresponse : comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma=
      comparisonGlobalScalarResponse d.U.mass A B d.sigma := rfl
  have hzero : ∀t∈comparisonIncrementSupport d.V.mass,
      comparisonGlobalScalarResponse d.U.mass A B d.sigma t=0 := by
    intro t ht
    rw [←hresponse]
    by_cases htp : 0 < t
    · exact d.support_zero t htp ht
    · have ht0 : t=0 := le_antisymm (not_lt.mp htp)
        (comparison_increment_support_nonnegative d.radius_negative_axis_zero ht)
      simp only [ht0,comparisonLocalScalarLimitResponse,intervalIntegral.integral_same]
  have H := comparison_global_scalar_primitives_rigidity
    d.U.monotone d.V.monotone hUV (fun t _ => d.U.nonneg t) d.radius_negative_axis_zero
    d.positive_coefficients.1 d.positive_coefficients.2 hcl
    (fun t ht => (d.radius_outer_growth hAz hxs t ht).1) hzero
    (fun a b ha hab has hbs hgap _ => by
      rw [←hresponse]
      exact hvirtual a b ha hab has hbs hgap)
  simpa only [d.coefficient_ratio] using H

theorem global_profile_rigidity_of_actual_history
    {m delta cl cu Az C0 Ct D Bclock T c0 epsilon : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualInheritedLocalScalarLimitData hT (T-epsilon) M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    (root : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcanonical : Tendsto (fun n => (M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hlocal : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hvirtual : ∀a b,0 ≤ a → a < b →
      a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT (T-epsilon) d.beta d.U d.sigma) a b)) :
    (∀t > 0,d.U.mass t=(((T-epsilon)/T)*scalarInitialDensityConstant hT d.beta)*t) ∧
    (∀t > 0,d.V.mass t=(((T-epsilon)/T)*scalarInitialDensityConstant hT d.beta)*t) := by
  have hUV := d.scalar_radius_laws_ae_eq_of_actual_history
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin hdim
    root hcanonical shell hepsilon hshell hlocal hb hh Hhistory
  have hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0) :=
    squeeze_zero (fun n => (M n).hxs.le)
      (fun n => (M n).canonical_direct_test_band_ge_scale) hcanonical
  exact d.global_profile_rigidity_of_coupled_laws hUV hcl hAz hxs hvirtual

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
