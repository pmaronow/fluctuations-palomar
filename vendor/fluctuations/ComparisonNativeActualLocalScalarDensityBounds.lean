module

public import ComparisonScalarInitialDensityBoundsPrerequisite

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Scalar
set_option maxHeartbeats 800000

theorem comparison_local_scalar_initial_density_uniform_bounds
    {T S : ℝ} (hT : 0 < T) (hS : 0 ≤ S) (beta : boundedMassProfiles) :
    2*S*Real.exp (-12*T) ≤ (S/T)*scalarInitialDensityConstant hT beta ∧
      (S/T)*scalarInitialDensityConstant hT beta ≤
        S*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) := by
  have H := scalarInitialDensityConstant_uniform_bounds hT beta
  have hratio : 0 ≤ S/T := div_nonneg hS hT.le
  have hlo := mul_le_mul_of_nonneg_left H.1 hratio
  have hup := mul_le_mul_of_nonneg_left H.2 hratio
  have hel : (S/T)*(2*T*Real.exp (-12*T))=2*S*Real.exp (-12*T) := by
    field_simp [hT.ne']
  have heu : (S/T)*(T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)))=
      S*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) := by
    field_simp [hT.ne']
  exact ⟨hel ▸ hlo,heu ▸ hup⟩

theorem comparison_local_scalar_initial_density_strict_margins
    {T epsilon cl cu : ℝ} (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hhalf : epsilon ≤ T/2)
    (hcl : cl < T*Real.exp (-12*T))
    (hcu : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (beta : boundedMassProfiles) :
    cl < ((T-epsilon)/T)*scalarInitialDensityConstant hT beta ∧
      ((T-epsilon)/T)*scalarInitialDensityConstant hT beta < cu := by
  have hS : 0 ≤ T-epsilon := by linarith
  have H := comparison_local_scalar_initial_density_uniform_bounds hT hS beta
  have hlo : T*Real.exp (-12*T) ≤ 2*(T-epsilon)*Real.exp (-12*T) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
  have hup : (T-epsilon)*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) ≤
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (sub_le_self T hepsilon) (sq_nonneg _)) (by positivity)
  exact ⟨hcl.trans_le (hlo.trans H.1),(H.2.trans hup).trans_lt hcu⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
