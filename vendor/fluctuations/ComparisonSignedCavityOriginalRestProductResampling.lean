module

public import ComparisonSignedCavityCanonicalRestFactorMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_original_full_rest_resampling_le (n l : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ → RestCoordinate n → ℝ) (b s e : T.Slot) (hse : s≠e)
    (hlow : T.splitIndex b s=T.splitIndex b e)
    (hgap : T.splitIndex b s<T.splitIndex s e) {r : ℝ}
    (hres : originalBoundaryResamplingMoment n l as
      (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex b s) (T.splitIndex s e) ≤ r^(2*l)) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot b),false))
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot b),false))
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false))|^(2*l)) 0 ≤ r^(2*l) := by
  rw [native_original_full_rest_resampling_eq_physical n l hn T ho q b s e hse hlow hgap]
  have hk0 : 0 ≤ (n:ℝ)/(n+1:ℕ):=by positivity
  have hk1 : (n:ℝ)/(n+1:ℕ) ≤ 1:=by
    apply (div_le_one (by positivity : (0:ℝ)<(n+1:ℕ))).mpr
    push_cast
    linarith
  exact (mul_le_mul_of_nonneg_left hres (pow_nonneg hk0 _)).trans
    (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (pow_le_one₀ (n:=2*l) hk0 hk1) (by rw [pow_mul]; exact pow_nonneg (sq_nonneg r) l : 0 ≤ r^(2*l))))

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem restFactor_retarget_difference (G : ActualNaturalBoundaryShape n a T)
    (j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e) (e : Fin a)
    (σ : T.cavityLeft.Assignment) :
    G.restFactor e σ-(G.retarget j' hne).restFactor e σ=
      G.β e*(deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false))
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.j e)),false))-
        deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false))
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (j' e)),false))) := by
  have hsymm (σ τ : Spin (n+1)) : deletedOverlap n σ τ=deletedOverlap n τ σ := by
    simp only [deletedOverlap,mul_comm]
  simp only [restFactor,retarget,fullBoundaryAffineFactor]
  rw [hsymm (joinSpin (_,false)) (joinSpin (_,false)),
    hsymm (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (j' e)),false))]
  ring

theorem restFactor_retarget_error_moment (G : ActualNaturalBoundaryShape n a T)
    (hn : 0 < n) (ho : MassOrdered 0 as) (q : ℕ → RestCoordinate n → ℝ)
    (j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))
    (hgap : ∀e,G.j e≠j' e → T.splitIndex (G.i e) (G.j e)<T.splitIndex (G.j e) (j' e))
    (l : ℕ) (hl : 0 < l) (e : Fin a) {Cb r : ℝ} (hCb : 0 ≤ Cb) (hr : 0 ≤ r)
    (hb : |G.β e| ≤ Cb)
    (hres : G.j e≠j' e → originalBoundaryResamplingMoment n l as
      (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex (G.i e) (G.j e))
      (T.splitIndex (G.j e) (j' e)) ≤ r^(2*l)) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|G.restFactor e σ-(G.retarget j' hne).restFactor e σ|^(2*l)) 0 ≤ (Cb*r)^(2*l) := by
  by_cases he : G.j e=j' e
  · have hf : ∀σ,G.restFactor e σ=(G.retarget j' hne).restFactor e σ:=by
      intro σ
      simp only [restFactor,retarget,he]
    simp only [hf,sub_self,abs_zero,zero_pow (show 2*l≠0 by omega),
      ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
    positivity
  · have H:=native_original_full_rest_resampling_le n l hn T ho q (G.i e) (G.j e) (j' e)
      he (hlow e) (hgap e he) (hres he)
    simp_rw [G.restFactor_retarget_difference j' hne e,abs_mul,mul_pow]
    unfold ClockTree.disorderExpect at H ⊢
    have hfactor : (∑σ,T.cavityLeft.disorderWeight (restWeight n) (restFeature n) 0 q σ 0*
        (|G.β e|^(2*l)*|deletedOverlap n
          (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false))
          (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.j e)),false))-
          deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false))
          (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (j' e)),false))|^(2*l)))=
        |G.β e|^(2*l)*(∑σ,T.cavityLeft.disorderWeight (restWeight n) (restFeature n) 0 q σ 0*
          |deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false))
            (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.j e)),false))-
            deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (G.i e)),false))
            (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot (j' e)),false))|^(2*l)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    rw [hfactor]
    calc
      _ ≤ |G.β e|^(2*l)*r^(2*l):=mul_le_mul_of_nonneg_left H (by positivity)
      _ ≤ Cb^(2*l)*r^(2*l):=mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) hb _) (by positivity)
      _ = _:=rfl

theorem restProduct_retarget_square (G : ActualNaturalBoundaryShape n a T)
    (hn : 0 < n) (ha : 0 < a) (ho : MassOrdered 0 as) (q : ℕ → RestCoordinate n → ℝ)
    (j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))
    (hgap : ∀e,G.j e≠j' e → T.splitIndex (G.i e) (G.j e)<T.splitIndex (G.j e) (j' e))
    (rho : Fin a → ℝ) (hrho : ∀e,0 < rho e) {xi Cb : ℝ} (hxi : 0 < xi) (hCb : 0 < Cb)
    (hbeta : ∀e,|G.β e| ≤ Cb)
    (hraw : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|G.restFactor e σ|^(2*a)) 0 ≤ (rho e)^(2*a))
    (hraw' : ∀e,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|(G.retarget j' hne).restFactor e σ|^(2*a)) 0 ≤ (rho e)^(2*a))
    (hres : ∀e,G.j e≠j' e → originalBoundaryResamplingMoment n a as
      (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex (G.i e) (G.j e))
      (T.splitIndex (G.j e) (j' e)) ≤ (xi*rho e/Cb)^(2*a)) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>(G.restProduct σ-(G.retarget j' hne).restProduct σ)^2) 0 ≤
        ((a:ℝ)*xi*(∏e,rho e))^2 := by
  apply finite_weighted_resampled_product_square ha
    (fun σ=>T.cavityLeft.disorderWeight (restWeight n) (restFeature n) 0 q σ 0)
    (G.restFactor) ((G.retarget j' hne).restFactor)
    (T.cavityLeft.disorderWeight_probability (restWeight_pos n) (restFeature n) ho 0 q 0).1
    rho hrho hxi hraw hraw'
  intro e
  have H:=G.restFactor_retarget_error_moment hn ho q j' hne hlow hgap a ha e hCb.le
    (by have H:=hrho e; positivity) (hbeta e) (hres e)
  have heq : Cb*(xi*rho e/Cb)=xi*rho e:=by field_simp
  simpa only [heq,ClockTree.disorderExpect] using H

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
