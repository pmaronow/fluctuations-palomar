module

public import ComparisonSignedCavityWholeLawLowProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

theorem disorderExpect_mixed_profile_wholeLaw_moment {w : S→ℝ} (hw : ∀σ,0 < w σ)
    (φ : S→(ι→ℝ)→L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (r k : ℕ) (hr : 0 < r) (hk : 0 < k) (P : T.Assignment→ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^(4*r)) x ≤ C^(4*r))
    (E : Fin k→S→S→ℝ) (s t : Fin k→T.Slot) (hst : ∀i,s i≠t i)
    (rho : Fin k→ℝ) (hrho : ∀i,0 < rho i)
    (hmoment : ∀i,(pairClock as (T.splitIndex (s i) (t i))).disorderExpect w φ v q
      (fun σ=>|E i (pairSpin as (T.splitIndex (s i) (t i)) σ).1
        (pairSpin as (T.splitIndex (s i) (t i)) σ).2|^(4*r*k)) x ≤ (rho i)^(4*r*k)) :
    T.disorderExpect w φ v q
      (fun σ=>|P σ*(∏i,E i (T.atSlot σ (s i)) (T.atSlot σ (t i)))|^(2*r)) x ≤
      (C*(∏i,rho i))^(2*r) := by
  let L:=fun σ=>∏i,E i (T.atSlot σ (s i)) (T.atSlot σ (t i))
  have hExp : ((4*r:ℕ):ℝ)*(k:ℝ)=((4*r*k:ℕ):ℝ):=by push_cast;ring
  have HL:=T.disorderExpect_pair_product_rpow_scales hw φ ho v q x hk E s t hst rho hrho
    (p:=((4*r:ℕ):ℝ)) (by exact_mod_cast (show 0 < 4*r by omega))
    (fun i=>by simpa only [hExp,Real.rpow_natCast] using hmoment i)
  have hDouble : (2:ℝ)*((2*r:ℕ):ℝ)=((4*r:ℕ):ℝ):=by push_cast;ring
  have HP : T.disorderExpect w φ v q (fun σ=>|P σ|^(2*((2*r:ℕ):ℝ))) x ≤ C^(2*((2*r:ℕ):ℝ)) := by
    simpa only [hDouble,Real.rpow_natCast] using hP
  have HLow : T.disorderExpect w φ v q (fun σ=>|L σ|^(2*((2*r:ℕ):ℝ))) x ≤ (∏i,rho i)^(2*((2*r:ℕ):ℝ)) := by
    simpa only [hDouble,L] using HL
  have H:=T.disorderExpect_product_wholeLaw_rpow_le hw φ ho v q x P L hC
    (Finset.prod_nonneg fun i _=>(hrho i).le) HP HLow
  simpa only [Real.rpow_natCast,L] using H

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_wholeLaw_mixed_profile_moment
    (a r k : ℕ) (ha : 0 < a) (hr : 0 < r) (hk : 0 < k)
    (Bclock Btotal Bbond CmassOld CmassLow ChOld ChLow CbOld : ℝ)
    (hBbond : 0 ≤ Bbond) (hCmOld : 0 ≤ CmassOld) (hCmLow : 0 ≤ CmassLow)
    (hChOld : 0 ≤ ChOld) (hChLow : 0 ≤ ChLow) (hCbOld : 0 ≤ CbOld)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp Cq : ℝ,0 < Cp ∧ 0 < Cq ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
        ∀ᶠ jGrid : ℕ in atTop,
          let as:=finiteCutMasses us jGrid
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t s : ℝ),
            l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → s∈Icc (0:ℝ) 1 →
          ∀(G : ActualNaturalBoundaryShape n a T) (initial : Finset (Fin a))
            (x W : ℝ) (field : Fin a→ℝ),M.xs ≤ x → x ≤ W →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal →
            b as.length ≤ Bbond →
            (∀e,partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)) ≤ CmassOld*sourceFactorScale x W initial e) →
            (∀e,|field e| ≤ ChOld*sourceFactorScale x W initial e) →
            (∀e,|G.β e| ≤ CbOld) →
            (∀e,G.α e=field e-G.β e*pathPairMoment (uniformWeight (n+1))
              (finiteFeature (n+1)) (completedPathClock (n+1) M.bf M.hf)
              (orderedOverlap (n+1)) (partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))) →
            (∀j,j ≤ as.length → j < U → |h j| ≤ ChLow*(M.xs+partitionPoint 0 as j)) →
            (∀j,j ≤ as.length → j < U → partitionPoint 0 as j ≤ CmassLow*W) →
          ∀(left right : Fin k→T.Slot),(∀e,left e≠right e) →
            T.disorderExpect (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t)
              (fun σ=>|G.product σ*(∏e,finitePhysicalSquareLowKernel n U as b h s
                (T.splitIndex (left e) (right e)) (T.atSlot σ (left e)) (T.atSlot σ (right e)))|^(2*r)) 0 ≤
              (Cp^a*sourceMonomialScale x W initial*(Cq*W)^k)^(2*r) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_source_centered_square_repeated_forest_product
    (D:=D) a (2*r) ha (by omega) Bclock Btotal Bbond CmassOld ChOld CbOld
    hCmOld hChOld hCbOld hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Clow,hClow,HQ⟩:=eventually_actual_minimum_wholeLaw_low_profile_moment
    (D:=D) (2*r*k) (by positivity) Bclock Btotal Bbond ChLow hBbond hChLow
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Clow*(1+CmassLow),hCp,by positivity,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M L us hus hret hmesh
  filter_upwards [hnP M L us hus hret hmesh,hnQ M L us hus hret hmesh] with jGrid hgridP hgridQ
  dsimp only at hgridP hgridQ ⊢
  intro U T l t s hl ht hs G initial x W field hxs hxW hclock hbond hmassOld hfieldOld hβ hαeq hfieldLow hmassLow left right hne
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hx : 0 < x:=M.hxs.trans_le hxs
  have hW : 0 < W:=hx.trans_le hxW
  let rho:=Clow*(1+CmassLow)*W
  have hrho : 0 < rho:=by dsimp [rho];positivity
  have hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>|G.product σ|^(4*r)) 0 ≤
      (Cp^a*sourceMonomialScale x W initial)^(4*r) := by
    simpa only [show 2*(2*r)=4*r by omega] using hgridP U T l t hl ht G initial x W field
      hxs hxW hclock hbond hmassOld hfieldOld hβ hαeq
  have hPair : ∀e,(ClockTree.pairClock as (T.splitIndex (left e) (right e))).disorderExpect
      (fullWeight n) (fullFeature n) 0 (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s (T.splitIndex (left e) (right e))
        (ClockTree.pairSpin as (T.splitIndex (left e) (right e)) σ).1
        (ClockTree.pairSpin as (T.splitIndex (left e) (right e)) σ).2|^(4*r*k)) 0 ≤ rho^(4*r*k) := by
    intro e
    let j:=T.splitIndex (left e) (right e)
    have hj : j ≤ as.length:=T.splitIndex_le_clockLength _ _
    change (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*r*k)) 0 ≤ _
    by_cases hlow : j < U
    · have H:=hgridQ U l t s hl ht hs j hj hclock hbond (hfieldLow j hj)
      have hExp : 2*(2*r*k)=4*r*k:=by ring
      rw [hExp] at H
      apply H.trans
      apply pow_le_pow_left₀
        (mul_nonneg hClow.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      have Hmass : M.xs+partitionPoint 0 as j ≤ (1+CmassLow)*W:=by
        have Hm:=hmassLow j hj hlow
        nlinarith
      simpa only [rho,mul_assoc] using mul_le_mul_of_nonneg_left Hmass hClow.le
    · simp_rw [finitePhysicalSquareLowKernel_at_high n U as b h s hlow,
        abs_zero,zero_pow (by positivity : 4*r*k≠0)]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hrho.le _
  have hPscale : 0 ≤ Cp^a*sourceMonomialScale x W initial := by
    rw [←source_factor_scale_product]
    exact mul_nonneg (pow_nonneg hCp.le _) (Finset.prod_nonneg fun e _=>(source_factor_scale_pos hx hW initial e).le)
  have H:=T.disorderExpect_mixed_profile_wholeLaw_moment (fullWeight_pos n) (fullFeature n) ho
    0 (finitePhysicalCavitySquareVariance n U as b h l t) 0 r k hr hk G.product hPscale hP
    (fun e=>finitePhysicalSquareLowKernel n U as b h s (T.splitIndex (left e) (right e)))
    left right hne (fun _=>rho) (fun _=>hrho) hPair
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,rho,mul_assoc] using H

end OAI.SKFluctuations.Cavity
