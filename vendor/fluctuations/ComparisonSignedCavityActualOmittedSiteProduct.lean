module

public import ComparisonSignedCavityCanonicalRestFactorMoments
public import ComparisonSignedCavityActualRestStarRates
public import ComparisonSignedCavityActualFullSitePairAveraging

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def deletedFactor (G : ActualNaturalBoundaryShape n a T) (e : Fin a) (σ : T.Assignment) : ℝ :=
  fullBoundaryAffineFactor n (G.α e) (G.β e) (T.atSlot σ (G.j e)) (T.atSlot σ (G.i e))

def restoredFactor (G : ActualNaturalBoundaryShape n a T) (e : Fin a) (σ : T.Assignment) : ℝ :=
  G.α e+G.β e*orderedOverlap (n+1) (joinSpin (T.atSlot σ (G.j e))) (joinSpin (T.atSlot σ (G.i e)))

def restoredProduct (G : ActualNaturalBoundaryShape n a T) (σ : T.Assignment) : ℝ :=
  ∏ e,G.restoredFactor e σ

theorem product_eq_prod_deletedFactor (G : ActualNaturalBoundaryShape n a T) (σ : T.Assignment) :
    G.product σ=∏ e,G.deletedFactor e σ := rfl

theorem restoredFactor_sub_abs (G : ActualNaturalBoundaryShape n a T) (e : Fin a) (σ : T.Assignment) :
    |G.restoredFactor e σ-G.deletedFactor e σ|=|G.β e|/(n+1:ℕ) := by
  have HE : G.restoredFactor e σ-G.deletedFactor e σ=
      G.β e*(orderedOverlap (n+1) (joinSpin (T.atSlot σ (G.j e)))
        (joinSpin (T.atSlot σ (G.i e)))-deletedOverlap n (joinSpin (T.atSlot σ (G.j e)))
          (joinSpin (T.atSlot σ (G.i e)))) := by
    unfold restoredFactor deletedFactor fullBoundaryAffineFactor
    ring
  rw [HE,abs_mul,abs_sub_comm,abs_deletedOverlap_sub]
  ring

end ActualNaturalBoundaryShape

theorem finite_weighted_shifted_factor_moment {A : Type*} [Fintype A]
    (w F G : A→ℝ) (hw : ∀ σ,0 ≤ w σ) (hmass : ∑ σ,w σ=1)
    (m : ℕ) (hm : 0 < m) (rho : ℝ) (hrho : 0 ≤ rho)
    (hF : (∑ σ,w σ*|F σ|^m) ≤ rho^m) (hchange : ∀ σ,|G σ-F σ| ≤ rho) :
    (∑ σ,w σ*|G σ|^m) ≤ (2*rho)^m := by
  have HP (σ : A) : |G σ|^m ≤ (2:ℝ)^(m-1)*(|F σ|^m+rho^m) := by
    have HA : |G σ| ≤ |F σ|+rho := by
      calc
        _=|F σ+(G σ-F σ)|:=by congr 1;ring
        _ ≤ |F σ|+|G σ-F σ|:=abs_add_le _ _
        _ ≤ _:=add_le_add le_rfl (hchange σ)
    exact (pow_le_pow_left₀ (abs_nonneg _) HA m).trans
      (add_pow_le (abs_nonneg _) hrho m)
  have H:=Finset.sum_le_sum fun σ (_ : σ∈Finset.univ)=>
    mul_le_mul_of_nonneg_left (HP σ) (hw σ)
  have HE : (∑ σ,w σ*((2:ℝ)^(m-1)*(|F σ|^m+rho^m)))=
      (2:ℝ)^(m-1)*((∑ σ,w σ*|F σ|^m)+rho^m) := by
    calc
      _=(2:ℝ)^(m-1)*((∑ σ,w σ*|F σ|^m)+rho^m*(∑ σ,w σ)) := by
        simp only [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        ring
      _=_:=by rw [hmass,mul_one]
  rw [HE] at H
  apply H.trans
  have HH:=mul_le_mul_of_nonneg_left hF (show 0 ≤ (2:ℝ)^(m-1) by positivity)
  have Hpow : (2:ℝ)^(m-1)*2=(2:ℝ)^m := by rw [←pow_succ];congr 1;omega
  calc
    _ ≤ (2:ℝ)^(m-1)*(rho^m+rho^m):=by linarith
    _=(2*rho)^m:=by rw [mul_pow,show rho^m+rho^m=2*rho^m by ring,←mul_assoc,Hpow]

theorem native_omitted_site_product_square (n a : ℕ) (ha : 0 < a)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (xroot : FullCoordinate n→ℝ)
    (G : ActualNaturalBoundaryShape n a T)
    (scale : Fin a→ℝ) (x C Cb : ℝ) (hx : 0 < x) (hC : 0 < C) (hCb : 0 < Cb)
    (hscale : ∀ e,x ≤ scale e) (hsite : 1/(n+1:ℕ) ≤ x)
    (hbeta : ∀ e,|G.β e| ≤ Cb)
    (hmoment : ∀ e,T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>|G.deletedFactor e σ|^(2*a)) xroot ≤ (C*scale e)^(2*a)) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>(G.product σ-G.restoredProduct σ)^2) xroot ≤
      (((a:ℝ)*(Cb/((n+1:ℕ)*x)))*((2*(C+Cb+1))^a*(∏ e,scale e)))^2 := by
  let w:=fun σ=>T.disorderWeight (fullWeight n) (fullFeature n) v q σ xroot
  have hw:=T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q xroot
  let rho:=fun e=>(C+Cb+1)*scale e
  let rho2:=fun e=>2*rho e
  let xi:=Cb/((n+1:ℕ)*x)
  have hsp (e : Fin a) : 0 < scale e:=hx.trans_le (hscale e)
  have hrho (e : Fin a) : 0 < rho e:=by dsimp [rho];have Hs:=hsp e;positivity
  have hrho2 (e : Fin a) : 0 < rho2 e:=by dsimp [rho2];exact mul_pos (by norm_num) (hrho e)
  have HF (e : Fin a) : (∑ σ,w σ*|G.deletedFactor e σ|^(2*a)) ≤ (rho e)^(2*a) := by
    exact (hmoment e).trans (pow_le_pow_left₀ (by have Hs:=hsp e;positivity)
      (by dsimp [rho];nlinarith [hsp e]) _)
  have Hchange (e : Fin a) (σ : T.Assignment) : |G.restoredFactor e σ-G.deletedFactor e σ| ≤ rho e := by
    rw [G.restoredFactor_sub_abs]
    have H₁:=div_le_div_of_nonneg_right (hbeta e) (show (0:ℝ) ≤ (n+1:ℕ) by positivity)
    have H₂:=mul_le_mul_of_nonneg_left hsite hCb.le
    have H₃:=mul_le_mul_of_nonneg_left (hscale e) hCb.le
    calc
      _ ≤ Cb/(n+1:ℕ):=H₁
      _=Cb*(1/(n+1:ℕ)):=by ring
      _ ≤ Cb*x:=H₂
      _ ≤ Cb*scale e:=H₃
      _ ≤ rho e:=mul_le_mul_of_nonneg_right (show Cb ≤ C+Cb+1 by linarith) (hsp e).le
  have HG (e : Fin a) : (∑ σ,w σ*|G.restoredFactor e σ|^(2*a)) ≤ (rho2 e)^(2*a) := by
    exact finite_weighted_shifted_factor_moment w _ _ hw.1 hw.2 (2*a) (by omega)
      (rho e) (hrho e).le (HF e) (Hchange e)
  have HF2 (e : Fin a) : (∑ σ,w σ*|G.deletedFactor e σ|^(2*a)) ≤ (rho2 e)^(2*a) :=
    (HF e).trans (pow_le_pow_left₀ (hrho e).le (by dsimp [rho2];linarith [hrho e]) _)
  have HD (e : Fin a) : (∑ σ,w σ*|G.deletedFactor e σ-G.restoredFactor e σ|^(2*a)) ≤ (xi*rho2 e)^(2*a) := by
    have HDp (σ : T.Assignment) : |G.deletedFactor e σ-G.restoredFactor e σ| ≤ xi*rho2 e := by
      rw [abs_sub_comm,G.restoredFactor_sub_abs]
      have Hsc : x ≤ rho2 e:=by dsimp [rho2,rho];nlinarith [hsp e,hscale e]
      calc
        _ ≤ Cb/(n+1:ℕ):=div_le_div_of_nonneg_right (hbeta e) (by positivity)
        _=(Cb/((n+1:ℕ)*x))*x:=by field_simp [hx.ne']
        _ ≤ xi*rho2 e:=mul_le_mul_of_nonneg_left Hsc (show 0 ≤ Cb/((n+1:ℕ)*x) by positivity)
    calc
      _ ≤ ∑ σ,w σ*(xi*rho2 e)^(2*a):=Finset.sum_le_sum fun σ _=>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (HDp σ) _) (hw.1 σ)
      _=(xi*rho2 e)^(2*a):=by rw [←Finset.sum_mul,hw.2,one_mul]
  have H:=finite_weighted_resampled_product_square ha w G.deletedFactor G.restoredFactor hw.1
    rho2 hrho2 (show 0 < xi by dsimp [xi];positivity) HF2 HG HD
  have HR : (∏ e,rho2 e)=(2*(C+Cb+1))^a*(∏ e,scale e) := by
    simp only [rho2,rho,←mul_assoc,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin]
    rw [mul_pow]
  rw [HR] at H
  simpa only [ActualNaturalBoundaryShape.product_eq_prod_deletedFactor,
    ActualNaturalBoundaryShape.restoredProduct,xi,mul_assoc,ClockTree.disorderExpect,w] using H

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem restoredProduct_site_permutation (G : ActualNaturalBoundaryShape n a T)
    (π : Fin (n+1)≃Fin (n+1)) (σ : T.Assignment) :
    G.restoredProduct (T.assignmentGauge (nativeFullSiteSpinPerm π) σ)=G.restoredProduct σ := by
  unfold restoredProduct restoredFactor
  simp only [ClockTree.atSlot_assignmentGauge,full_orderedOverlap_nativeSitePerm]

end ActualNaturalBoundaryShape

theorem native_original_canonical_restored_site_pair_eq_overlap
    (n a U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (b h K : ℕ→ℝ) (G : ActualNaturalBoundaryShape n a T)
    (s t : T.Slot) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2*G.restoredProduct σ) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))*G.restoredProduct σ) 0 := by
  simpa only [joinSpin_last] using native_actual_full_site_pair_eq_overlap T ho U b h K
    G.restoredProduct G.restoredProduct_site_permutation s t (Fin.last n)

theorem native_original_deleted_site_pair_eq_overlap_add_omission
    (n a U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (b h K : ℕ→ℝ) (G : ActualNaturalBoundaryShape n a T)
    (s t : T.Slot) :
    let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2*G.product σ) 0=
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))*G.product σ) 0+
    T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>(spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2-
        orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t)))*
        (G.product σ-G.restoredProduct σ)) 0 := by
  have H:=native_original_canonical_restored_site_pair_eq_overlap n a U T ho b h K G s t
  dsimp only [ClockTree.disorderExpect] at H ⊢
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib]
  simp only [←mul_assoc] at H ⊢
  linear_combination H

theorem native_original_omitted_site_row_abs_le
    (n a U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (b h K : ℕ→ℝ) (G : ActualNaturalBoundaryShape n a T)
    (s t : T.Slot) (B : ℝ) (hB : 0 ≤ B)
    (hprod : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>(G.product σ-G.restoredProduct σ)^2) 0 ≤ B^2) :
    |T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K)
      (fun σ=>(spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2-
        orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t)))*
        (G.product σ-G.restoredProduct σ)) 0| ≤ 2*B := by
  let q:=cavityPath n U 1 1 (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) b h K
  let A:=fun σ : T.Assignment=>spinValue (T.atSlot σ s).2*spinValue (T.atSlot σ t).2-
    orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))
  let D:=fun σ : T.Assignment=>G.product σ-G.restoredProduct σ
  have HP (σ : T.Assignment) : (A σ)^2 ≤ 4 := by
    have H : |A σ| ≤ 2 := by
      dsimp only [A]
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_spinValue,abs_spinValue,one_mul]
      linarith [orderedOverlap_abs_le_one (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))]
    nlinarith [sq_abs (A σ),abs_nonneg (A σ)]
  have hw:=T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 q 0
  have HA : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(A σ)^2) 0 ≤ 4 := by
    unfold ClockTree.disorderExpect
    calc
      _ ≤ ∑ σ,T.disorderWeight (fullWeight n) (fullFeature n) 0 q σ 0*4 :=
        Finset.sum_le_sum fun σ _=>mul_le_mul_of_nonneg_left (HP σ) (hw.1 σ)
      _=4:=by rw [←Finset.sum_mul,hw.2,one_mul]
  have HD0 : 0 ≤ T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(D σ)^2) 0 := by
    unfold ClockTree.disorderExpect
    exact Finset.sum_nonneg fun σ _=>mul_nonneg (hw.1 σ) (sq_nonneg _)
  have H:=T.disorderExpect_mul_sq_le (fullWeight_pos n) (fullFeature n) ho 0 q A D 0
  have HC:=mul_le_mul HA hprod HD0 (by norm_num : (0:ℝ) ≤ 4)
  change |T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>A σ*D σ) 0| ≤ 2*B
  nlinarith [sq_abs (T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>A σ*D σ) 0),
    abs_nonneg (T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>A σ*D σ) 0)]

theorem native_full_endpoint_scalar_clock_independent (n U : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (b h K K' : ℕ→ℝ) :
    cavityPath n U 1 1 q b h K=cavityPath n U 1 1 q b h K' := by
  funext j i
  rcases i with (i|i)|(i|i) <;>
    simp only [cavityPath,relocatedClock_one,fullVariance,one_mul,sub_self,zero_mul]

end OAI.SKFluctuations.Cavity
