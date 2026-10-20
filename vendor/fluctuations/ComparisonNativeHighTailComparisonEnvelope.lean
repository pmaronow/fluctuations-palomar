module

public import ComparisonNativeMassEdgeRealMoment
public import ComparisonSignedCavityActualLowErrorTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def nativeOriginalHighTailEnvelope (n U : ℕ) (b h : ℝ→ℝ≥0)
    (as : List PositiveMass) (C : ℝ) (j : ℕ) : ℝ :=
  if j<U then 0 else C*(nativeOriginalCutLowErrorRadius n b h as j+1/(n+1:ℕ))

theorem native_high_tail_envelope_second_le {as : List PositiveMass}
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) (U : ℕ)
    (D : ℕ→ℝ) (_hD : ∀j,0≤D j) {C epsSite B : ℝ}
    (_hC : 0≤C) (hsite : 0≤epsSite) (_hB : 0≤B) (hsiteB : epsSite≤B)
    (hsecond : ClockTree.edgeBudget 0 as (fun j=>if j<U then 0 else (D j)^2)≤B^2) :
    ClockTree.edgeBudget 0 as (fun j=>(if j<U then 0 else C*(D j+epsSite))^2)≤(2*C*B)^2 := by
  have Hpoint j (_hj : j≤as.length) :
      (if j<U then 0 else C*(D j+epsSite))^2≤
        (2*C^2)*(if j<U then 0 else (D j)^2)+(2*C^2*epsSite^2)*1 := by
    by_cases hj : j<U
    · simp only [hj,ite_true,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_add,mul_one]
      positivity
    · simp only [hj,ite_false,mul_one,mul_pow]
      have H:=mul_nonneg (sq_nonneg C) (sq_nonneg (D j-epsSite))
      nlinarith only [H]
  have Hmono:=Cavity.actual_low_edgeBudget_mono ho Hpoint
  rw [Cavity.actual_low_edgeBudget_linear] at Hmono
  have Hones : ClockTree.edgeBudget 0 as (fun _=>(1:ℝ))=1 := by
    rw [native_edgeBudget_eq_cells_add_terminal,he,sub_self,zero_mul,add_zero,massCellSum_const,he]
    norm_num
  rw [Hones,mul_one] at Hmono
  have Hbudget:=mul_le_mul_of_nonneg_left hsecond (show 0≤2*C^2 by positivity)
  have Hsite:=pow_le_pow_left₀ hsite hsiteB 2
  have Hsite':=mul_le_mul_of_nonneg_left Hsite (show 0≤2*C^2 by positivity)
  nlinarith only [Hmono,Hbudget,Hsite']

end OAI.SKFluctuations.LaplaceWindowFormalization
