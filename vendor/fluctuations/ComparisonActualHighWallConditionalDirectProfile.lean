module

public import ComparisonActualHighWallLimitRigidity
public import ComparisonNativeActualLocalScalarLimitLawIdentification
public import ComparisonNativeActualLocalScalarDensityBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal
set_option maxHeartbeats 18000000

namespace ActualHighWallLocalScalarLimitData
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ} {hT : 0<T}
  {dim : ℕ→ℕ}
  {M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,((M n).hf u:ℝ)+((M n).bf u:ℝ)≤T}

theorem complete_direct_profile_of_coupled_laws
    (d : ActualHighWallLocalScalarLimitData hT T M htotal)
    (hUV : d.U.mass =ᵐ[volume] d.V.mass)
    (hcl : 0<cl) (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hvirtual : ∀a b,0≤a→a<b→
      a∈comparisonIncrementSupport d.V.mass→b∈comparisonIncrementSupport d.V.mass→
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass)→
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma) a b)) :
    let kappa := scalarInitialDensityConstant hT d.beta
    (∀t>0,d.U.mass t=kappa*t) ∧
    (∀t>0,d.V.mass t=kappa*t) ∧
    cl≤kappa ∧ kappa≤cu ∧
    2*T*Real.exp (-12*T)≤kappa ∧
    kappa≤T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) ∧
    TendstoLocallyUniformlyOn
      (fun n v=>(M n).data.wallRadius (M n).alpha ((M n).xs*v)/(M n).xs)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧
    d.sigma=0 ∧
    (∀t≥0,comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t=0) ∧
    (∀t≥0,comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma t=0) ∧
    ∀R : ℝ,0<R→
      TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT T
        ((M n).inheritedScalarMassProfile hT (htotal n)) (M n).xs)
        (fun _=>0) atTop (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n)))
        T (M n).xs) (fun _=>0) atTop (Icc (0:ℝ) R) := by
  have Hlinear := d.global_profile_rigidity_of_coupled_laws hUV hcl hxs hvirtual
  have Hzero := d.scalar_primitives_zero_of_linear_profiles Hlinear.1 Hlinear.2
  have Hdensity := comparison_local_scalar_initial_density_uniform_bounds hT hT.le d.beta
  have Hdensity' : 2*T*Real.exp (-12*T) ≤ scalarInitialDensityConstant hT d.beta ∧
      scalarInitialDensityConstant hT d.beta≤
        T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) := by
    simpa only [div_self hT.ne',one_mul] using Hdensity
  have HUl : ∀t>0,d.U.mass t=scalarInitialDensityConstant hT d.beta*t := by
    intro t ht
    simpa only [div_self hT.ne',one_mul] using Hlinear.1 t ht
  have HVl : ∀t>0,d.V.mass t=scalarInitialDensityConstant hT d.beta*t := by
    intro t ht
    simpa only [div_self hT.ne',one_mul] using Hlinear.2 t ht
  have Hlo : cl ≤ scalarInitialDensityConstant hT d.beta := by
    let t := max Az 1
    have ht : 0<t := zero_lt_one.trans_le (le_max_right _ _)
    have Hgrowth := (d.radius_outer_growth hxs t (le_max_left _ _)).1
    rw [HVl t ht] at Hgrowth
    exact le_of_mul_le_mul_right Hgrowth ht
  have Hup : scalarInitialDensityConstant hT d.beta≤cu := by
    let t := max Az 1
    have ht : 0<t := zero_lt_one.trans_le (le_max_right _ _)
    have Hgrowth := (d.radius_outer_growth hxs t (le_max_left _ _)).2
    rw [HVl t ht] at Hgrowth
    exact le_of_mul_le_mul_right Hgrowth ht
  exact ⟨HUl,HVl,Hlo,Hup,Hdensity'.1,Hdensity'.2,
    d.original_radius_locally_uniform_of_linear_profile
      (hcl.trans_le Hlo) hxs HVl,
    Hzero.1,Hzero.2.1,Hzero.2.2,
    d.compact_scalar_zero_limits_of_linear_profiles Hlinear.1 Hlinear.2⟩

end ActualHighWallLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
