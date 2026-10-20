module

public import ComparisonContinuumSideKernel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory Set
open scoped BigOperators

theorem weighted_sqrt_product_le {I : Type*} [Fintype I]
    (P C D : I → ℝ) (hP : ∀i,0 ≤ P i) (hC : ∀i,0 ≤ C i) (hD : ∀i,0 ≤ D i) :
    (∑i,P i*Real.sqrt (C i)*Real.sqrt (D i)) ≤ Real.sqrt (∑i,P i*C i)*Real.sqrt (∑i,P i*D i) := by
  have hCsum : 0 ≤ ∑i,P i*C i := Finset.sum_nonneg (fun i _=>mul_nonneg (hP i) (hC i))
  have hDsum : 0 ≤ ∑i,P i*D i := Finset.sum_nonneg (fun i _=>mul_nonneg (hP i) (hD i))
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset I)
    (r:=fun i=>P i*Real.sqrt (C i)*Real.sqrt (D i))
    (f:=fun i=>P i*C i) (g:=fun i=>P i*D i)
    (fun i _=>mul_nonneg (hP i) (hC i)) (fun i _=>mul_nonneg (hP i) (hD i))
    (fun i _=>by rw [mul_pow,mul_pow,Real.sq_sqrt (hC i),Real.sq_sqrt (hD i)]; nlinarith)
  have hrC := Real.sq_sqrt hCsum
  have hrD := Real.sq_sqrt hDsum
  have hn : 0 ≤ ∑i,P i*Real.sqrt (C i)*Real.sqrt (D i) :=
    Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (hP i) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  have hroot : 0 ≤ Real.sqrt (∑i,P i*C i)*Real.sqrt (∑i,P i*D i) := by positivity
  have hsRoot : (Real.sqrt (∑i,P i*C i)*Real.sqrt (∑i,P i*D i))^2=
      (∑i,P i*C i)*(∑i,P i*D i) := by rw [mul_pow,hrC,hrD]
  rw [← hsRoot] at hs
  exact (sq_le_sq₀ hn hroot).mp hs

theorem joint_marginal_energy_le {I : Type*} [Fintype I]
    (P : I → I → ℝ) (mass E : I → ℝ) {L : ℝ}
    (hE : ∀i,0 ≤ E i) (hrow : ∀i,(∑j,P i j) ≤ mass i)
    (hcol : ∀j,(∑i,P i j) ≤ L*mass j) :
    (∑i,∑j,P i j*(E i+E j)) ≤ (1+L)*(∑i,mass i*E i) := by
  have hR : (∑i,∑j,P i j*E i) ≤ ∑i,mass i*E i := by
    simp_rw [← Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hrow i) (hE i))
  have hC : (∑i,∑j,P i j*E j) ≤ L*(∑j,mass j*E j) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    calc
      _ ≤ ∑j,(L*mass j)*E j := Finset.sum_le_sum
        (fun j _=>mul_le_mul_of_nonneg_right (hcol j) (hE j))
      _ = _ := by simp_rw [mul_assoc]; rw [Finset.mul_sum]
  simp only [mul_add,Finset.sum_add_distrib]
  linarith

theorem joint_total_mass_le {I : Type*} [Fintype I]
    (P : I → I → ℝ) (mass : I → ℝ)
    (hrow : ∀i,(∑j,P i j) ≤ mass i) :
    (∑i,∑j,P i j) ≤ ∑i,mass i := Finset.sum_le_sum (fun i _=>hrow i)

theorem joint_sqrt_energy_le {I : Type*} [Fintype I]
    (P : I → I → ℝ) (mass C D : I → ℝ) {L : ℝ}
    (hP : ∀i j,0 ≤ P i j) (hmass : ∀i,0 ≤ mass i)
    (hC : ∀i,0 ≤ C i) (hD : ∀i,0 ≤ D i) (hL : 0 ≤ L)
    (hrow : ∀i,(∑j,P i j) ≤ mass i) (hcol : ∀j,(∑i,P i j) ≤ L*mass j) :
    (∑i,∑j,P i j*Real.sqrt (C i+C j)*Real.sqrt (D i+D j)) ≤ (1+L)*Real.sqrt (∑i,mass i*C i)*Real.sqrt (∑i,mass i*D i) := by
  have h := weighted_sqrt_product_le
    (fun p:I×I=>P p.1 p.2) (fun p=>C p.1+C p.2) (fun p=>D p.1+D p.2)
    (fun p=>hP p.1 p.2) (fun p=>add_nonneg (hC p.1) (hC p.2))
    (fun p=>add_nonneg (hD p.1) (hD p.2))
  simp only [Fintype.sum_prod_type] at h
  have hCE := joint_marginal_energy_le P mass C hC hrow hcol
  have hDE := joint_marginal_energy_le P mass D hD hrow hcol
  have hsC := Real.sqrt_le_sqrt hCE
  have hsD := Real.sqrt_le_sqrt hDE
  have hr : Real.sqrt ((1+L)*(∑i,mass i*C i))*Real.sqrt ((1+L)*(∑i,mass i*D i))=
      (1+L)*Real.sqrt (∑i,mass i*C i)*Real.sqrt (∑i,mass i*D i) := by
    rw [Real.sqrt_mul (by linarith : 0 ≤ 1+L),Real.sqrt_mul (by linarith : 0 ≤ 1+L)]
    rw [show Real.sqrt (1+L)*Real.sqrt (∑i,mass i*C i)*
      (Real.sqrt (1+L)*Real.sqrt (∑i,mass i*D i))=
        (Real.sqrt (1+L))^2*Real.sqrt (∑i,mass i*C i)*Real.sqrt (∑i,mass i*D i) by ring,
      Real.sq_sqrt (by linarith : 0 ≤ 1+L)]
  exact h.trans ((mul_le_mul hsC hsD (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)).trans_eq hr)

theorem joint_constant_noise_le {I : Type*} [Fintype I]
    (P : I → I → ℝ) (mass C : I → ℝ) {L eta : ℝ}
    (hP : ∀i j,0 ≤ P i j) (hC : ∀i,0 ≤ C i)
    (hrow : ∀i,(∑j,P i j) ≤ mass i) (hcol : ∀j,(∑i,P i j) ≤ L*mass j) :
    (∑i,∑j,P i j*Real.sqrt (C i+C j)*eta) ≤
      ((1+L)*(∑i,mass i*C i)+eta^2*(∑i,mass i))/2 := by
  have hpoint (i j : I) : P i j*Real.sqrt (C i+C j)*eta ≤
      (P i j*(C i+C j)+eta^2*P i j)/2 := by
    have hroot := Real.sq_sqrt (add_nonneg (hC i) (hC j))
    have hq : 2*Real.sqrt (C i+C j)*eta ≤ C i+C j+eta^2 := by
      nlinarith [sq_nonneg (Real.sqrt (C i+C j)-eta)]
    have hm := mul_le_mul_of_nonneg_left hq (hP i j)
    nlinarith
  calc
    _ ≤ ∑i,∑j,(P i j*(C i+C j)+eta^2*P i j)/2 :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hpoint i j))
    _ = ((∑i,∑j,P i j*(C i+C j))+eta^2*(∑i,∑j,P i j))/2 := by
      simp_rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num : 0 ≤ (2:ℝ))
      exact add_le_add (joint_marginal_energy_le P mass C hC hrow hcol)
        (mul_le_mul_of_nonneg_left (joint_total_mass_le P mass hrow) (sq_nonneg eta))

theorem joint_noise_sum_le {I : Type*} [Fintype I]
    (P : I → I → ℝ) (mass C D : I → ℝ) (noise : I → I → ℝ)
    {L eta v tau : ℝ} (hP : ∀i j,0 ≤ P i j) (hmass : ∀i,0 ≤ mass i)
    (hC : ∀i,0 ≤ C i) (hD : ∀i,0 ≤ D i) (hL : 0 ≤ L) (hv : 0 ≤ v) (htau : 0 ≤ tau)
    (hrow : ∀i,(∑j,P i j) ≤ mass i) (hcol : ∀j,(∑i,P i j) ≤ L*mass j)
    (hmassv : ∑i,mass i=v) (htrace : (∑i,mass i*C i) ≤ v*tau)
    (hnoise : ∀i j,noise i j ≤ Real.sqrt (C i+C j)*(eta+4*Real.sqrt (D i+D j))) :
    (∑i,∑j,P i j*noise i j) ≤
      (1+L)*v*(eta^2+tau)/2+
        4*(1+L)*Real.sqrt (∑i,mass i*D i)*Real.sqrt (v*tau) := by
  have hj := joint_sqrt_energy_le P mass C D hP hmass hC hD hL hrow hcol
  have hc := joint_constant_noise_le P mass C hP hC hrow hcol (eta:=eta)
  rw [hmassv] at hc
  have hsC : Real.sqrt (∑i,mass i*C i) ≤ Real.sqrt (v*tau) := Real.sqrt_le_sqrt htrace
  have hj' : (∑i,∑j,P i j*Real.sqrt (C i+C j)*Real.sqrt (D i+D j)) ≤
      (1+L)*Real.sqrt (∑i,mass i*D i)*Real.sqrt (v*tau) := by
    apply hj.trans
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsC (by linarith : 0 ≤ 1+L))
      (Real.sqrt_nonneg (∑i,mass i*D i))
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hmul
  have hconst : ((1+L)*(∑i,mass i*C i)+eta^2*v)/2 ≤
      (1+L)*v*(eta^2+tau)/2 := by
    have htr := mul_le_mul_of_nonneg_left htrace (by linarith : 0 ≤ 1+L)
    have hmore : eta^2*v ≤ (1+L)*v*eta^2 := by
      nlinarith [mul_nonneg hL (mul_nonneg hv (sq_nonneg eta))]
    nlinarith
  calc
    _ ≤ ∑i,∑j,P i j*(Real.sqrt (C i+C j)*(eta+4*Real.sqrt (D i+D j))) :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum
        (fun j _=>mul_le_mul_of_nonneg_left (hnoise i j) (hP i j)))
    _ = (∑i,∑j,P i j*Real.sqrt (C i+C j)*eta)+
        4*(∑i,∑j,P i j*Real.sqrt (C i+C j)*Real.sqrt (D i+D j)) := by
      simp_rw [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      apply congrArg₂ (·+·)
      all_goals
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ _ := add_le_add (hc.trans hconst) (by
      have hmul := mul_le_mul_of_nonneg_left hj' (by norm_num : 0 ≤ (4:ℝ))
      simpa only [mul_assoc] using hmul)

end OAI.SKFluctuations.WholeUnitSideKernel
