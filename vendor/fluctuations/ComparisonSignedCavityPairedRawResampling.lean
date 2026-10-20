module

public import ComparisonSignedCavityActualOriginalRestResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem finite_weighted_paired_resampled_product_square
    {A : Type} [Fintype A] {a : ℕ} (ha : 0<a)
    (w : A→ℝ) (f g : Fin a→A→ℝ) (d : A→ℝ) (hw : ∀σ,0≤w σ)
    (rho : Fin a→ℝ) (hrho : ∀i,0<rho i) {xi r : ℝ} (hxi : 0<xi) (hr : 0<r)
    (hf : ∀i,(∑σ,w σ*|f i σ|^(2*(a+1)))≤(rho i)^(2*(a+1)))
    (hg : ∀i,(∑σ,w σ*|g i σ|^(2*(a+1)))≤(rho i)^(2*(a+1)))
    (hdiff : ∀i,(∑σ,w σ*|f i σ-g i σ|^(2*(a+1)))≤(xi*rho i)^(2*(a+1)))
    (hd : (∑σ,w σ*|d σ|^(2*(a+1)))≤r^(2*(a+1))) :
    (∑σ,w σ*(d σ*((∏i,f i σ)-(∏i,g i σ)))^2)≤
      ((a:ℝ)*r*xi*(∏i,rho i))^2 := by
  let F : Fin a→Fin a→A→ℝ:=fun i j σ=>
    boundaryTelescopingFactor (fun t=>f t σ) (fun t=>g t σ) i j
  let rs : Fin a→Fin a→ℝ:=fun i j=>if j=i then xi*rho j else rho j
  have hrs (i j : Fin a) : 0<rs i j := by
    dsimp [rs]
    have hj:=hrho j
    split_ifs <;> positivity
  have hm (i j : Fin a) : (∑σ,w σ*|F i j σ|^(2*(a+1)))≤(rs i j)^(2*(a+1)) := by
    dsimp [F,rs,boundaryTelescopingFactor]
    by_cases he : j=i
    · simpa only [ite_eq_left he] using hdiff j
    · simp only [ite_eq_right he]
      split_ifs
      · exact hg j
      · exact hf j
  have hprod (i : Fin a) : (∏j,rs i j)=xi*(∏j,rho j) := by
    calc
      _ = ∏j,(if j=i then xi else 1)*rho j := by
        apply Finset.prod_congr rfl
        intro j _
        dsimp [rs]
        split_ifs <;> simp
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hterm (i : Fin a) :
      (∑σ,w σ*(d σ*(∏j,F i j σ))^2)≤(r*xi*(∏j,rho j))^2 := by
    have H:=finite_weighted_product_square_scales (by omega : 0<a+1) w
      (Fin.cons d (F i)) hw (Fin.cons r (rs i))
      (by intro j; refine Fin.cases hr (fun j=>?_) j; exact hrs i j)
      (by intro j; refine Fin.cases hd (fun j=>?_) j; exact hm i j)
    simpa only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,hprod,mul_assoc] using H
  have hsum (σ : A) :
      (d σ*((∏i,f i σ)-(∏i,g i σ)))^2≤
        (a:ℝ)*(∑i,(d σ*(∏j,F i j σ))^2) := by
    rw [boundary_product_resampling_telescopes,Finset.mul_sum]
    have H:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin a=>(1:ℝ)) (fun i=>d σ*(∏j,F i j σ))
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one] using H
  calc
    _ ≤ ∑σ,w σ*((a:ℝ)*(∑i,(d σ*(∏j,F i j σ))^2)) :=
      Finset.sum_le_sum fun σ _=>mul_le_mul_of_nonneg_left (hsum σ) (hw σ)
    _ = (a:ℝ)*(∑i,∑σ,w σ*(d σ*(∏j,F i j σ))^2) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ ≤ (a:ℝ)*(∑_i : Fin a,(r*xi*(∏j,rho j))^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=>hterm i) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem restProduct_paired_retarget_square (G : ActualNaturalBoundaryShape n a T)
    (hn : 0<n) (ha : 0<a) (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ)
    (j' : Fin a→T.Slot) (hne : ∀e,G.i e≠j' e)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))
    (hgap : ∀e,G.j e≠j' e→T.splitIndex (G.i e) (G.j e)<T.splitIndex (G.j e) (j' e))
    (b s e : T.Slot) (hse : s≠e)
    (hblow : T.splitIndex b s=T.splitIndex b e)
    (hbgap : T.splitIndex b s<T.splitIndex s e)
    (rho : Fin a→ℝ) (hrho : ∀j,0<rho j) {xi Cb r : ℝ}
    (hxi : 0<xi) (hCb : 0<Cb) (hr : 0<r) (hbeta : ∀j,|G.β j|≤Cb)
    (hraw : ∀j,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|G.restFactor j σ|^(2*(a+1))) 0≤(rho j)^(2*(a+1)))
    (hraw' : ∀j,T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|(G.retarget j' hne).restFactor j σ|^(2*(a+1))) 0≤(rho j)^(2*(a+1)))
    (hres : ∀j,G.j j≠j' j → originalBoundaryResamplingMoment n (a+1) as
      (fun k=>restFiniteRealVariance n (q k)) (T.splitIndex (G.i j) (G.j j))
      (T.splitIndex (G.j j) (j' j))≤(xi*rho j/Cb)^(2*(a+1)))
    (hend : originalBoundaryResamplingMoment n (a+1) as
      (fun k=>restFiniteRealVariance n (q k)) (T.splitIndex b s)
      (T.splitIndex s e)≤r^(2*(a+1))) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>(nativeRestEndpointDifference n T b s e σ*
        (G.restProduct σ-(G.retarget j' hne).restProduct σ))^2) 0≤
      ((a:ℝ)*r*xi*(∏j,rho j))^2 := by
  apply finite_weighted_paired_resampled_product_square ha
    (fun σ=>T.cavityLeft.disorderWeight (restWeight n) (restFeature n) 0 q σ 0)
    G.restFactor (G.retarget j' hne).restFactor (nativeRestEndpointDifference n T b s e)
    (T.cavityLeft.disorderWeight_probability (restWeight_pos n) (restFeature n) ho 0 q 0).1
    rho hrho hxi hr hraw hraw'
  · intro j
    have H:=G.restFactor_retarget_error_moment hn ho q j' hne hlow hgap
      (a+1) (by omega) j hCb.le (by have H:=hrho j; positivity) (hbeta j) (hres j)
    have heq : Cb*(xi*rho j/Cb)=xi*rho j:=by field_simp
    simpa only [heq,ClockTree.disorderExpect] using H
  · exact native_original_full_rest_resampling_le n (a+1) hn T ho q b s e hse hblow hbgap hend

end ActualNaturalBoundaryShape
end OAI.SKFluctuations.Cavity
