module

public import ComparisonSignedCavityWholeLawTransientPhysical
public import ComparisonSignedCavityWholeLawMixedProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 7500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_wholeLaw_first_profile_error
    (a k rBound : ℕ) (ha : 0 < a) (hk : 0 < k)
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
          ∀(A : ℕ→FullCoordinate n→ℝ),T.leaves ≤ rBound →
            |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t) 0
              ((A::List.replicate k (cutLSlope n U s b h (finitePhysicalMixedClock (n+1) as b h))).map
                (ReplicaTree.coordinateProfile (fullFeature n))) T G.product| ≤
              ClockTree.pairForkVariation rBound*ClockTree.absJetVariation (rBound+2) k*
                (Cp^a*sourceMonomialScale x W initial)*(Cq*W)^k*
                nativeWholeLawProfileCost n (finitePhysicalCavitySquareVariance n U as b h l t) A T 1 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_source_centered_square_repeated_forest_product
    (D:=D) a 2 ha (by omega) Bclock Btotal Bbond CmassOld ChOld CbOld
    hCmOld hChOld hCbOld hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Clow,hClow,HQ⟩:=eventually_actual_minimum_wholeLaw_low_profile_moment
    (D:=D) (2*k) (by omega) Bclock Btotal Bbond ChLow hBbond hChLow
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Clow*(1+CmassLow),hCp,by positivity,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M L us hus hret hmesh
  filter_upwards [hnP M L us hus hret hmesh,hnQ M L us hus hret hmesh] with jGrid hgridP hgridQ
  dsimp only at hgridP hgridQ ⊢
  intro U T l t s hl ht hs G initial x W field hxs hxW hclock hbond hmassOld hfieldOld hβ hαeq hfieldLow hmassLow A hT
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hx : 0 < x:=M.hxs.trans_le hxs
  have hW : 0 < W:=hx.trans_le hxW
  let rho:=Clow*(1+CmassLow)*W
  have hrho : 0 < rho:=by dsimp [rho];positivity
  have hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>|G.product σ|^4) 0 ≤
      (Cp^a*sourceMonomialScale x W initial)^4 :=
    hgridP U T l t hl ht G initial x W field hxs hxW hclock hbond hmassOld hfieldOld hβ hαeq
  have hLow : ∀j,j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 (finitePhysicalCavitySquareVariance n U as b h l t)
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(4*k)) 0 ≤ rho^(4*k) := by
    intro j hj
    by_cases hlow : j < U
    · have H:=hgridQ U l t s hl ht hs j hj hclock hbond (hfieldLow j hj)
      rw [show 2*(2*k)=4*k by omega] at H
      apply H.trans
      apply pow_le_pow_left₀
        (mul_nonneg hClow.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      have Hmass : M.xs+partitionPoint 0 as j ≤ (1+CmassLow)*W:=by
        have Hm:=hmassLow j hj hlow
        nlinarith
      simpa only [rho,mul_assoc] using mul_le_mul_of_nonneg_left Hmass hClow.le
    · simp_rw [finitePhysicalSquareLowKernel_at_high n U as b h s hlow,
        abs_zero,zero_pow (by omega : 4*k≠0)]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hrho.le _
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  have hPscale : 0 ≤ Cp^a*sourceMonomialScale x W initial := by
    rw [←source_factor_scale_product]
    exact mul_nonneg (pow_nonneg hCp.le _) (Finset.prod_nonneg fun e _=>(source_factor_scale_pos hx hW initial e).le)
  exact nativeWholeLaw_first_profile_error_bound n U k hk ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hl ht T hT G.product
    hPscale hrho hP hLow A

theorem eventually_actual_minimum_wholeLaw_two_profile_error
    (a k rBound dOld ellLow : ℕ) (ha : 0 < a) (hdOld : 0 < dOld) (hellLow : 0 < ellLow)
    (p : ℝ) (hp : 2 < p) (hOldOrder : p/(p-2) ≤ (dOld:ℝ))
    (hLowOrder : (2*(p/(p-2)))*(k:ℝ) ≤ ((2*ellLow:ℕ):ℝ))
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
          ∀(A : ℕ→FullCoordinate n→ℝ) (E : ℝ),0 ≤ E →
            (∀j,j ≤ as.length → ∀σ τ,|ReplicaTree.coordinateProfile (fullFeature n) A j σ τ| ≤ E) →
            T.leaves ≤ rBound →
            |ClockTree.disorderProfileJets (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t) 0
              ((A::A::List.replicate k (cutLSlope n U s b h (finitePhysicalMixedClock (n+1) as b h))).map
                (ReplicaTree.coordinateProfile (fullFeature n))) T G.product| ≤
              ClockTree.pairForkVariation rBound*ClockTree.pairForkVariation (rBound+2)*
                ClockTree.absJetVariation (rBound+4) k*
                (Cp^a*sourceMonomialScale x W initial)*E^((p-2)/p)*E^((p-2)/p)*(Cq*W)^k*
                nativeWholeLawProfileCost n (finitePhysicalCavitySquareVariance n U as b h l t) A T (4/p) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_source_centered_square_repeated_forest_product
    (D:=D) a dOld ha hdOld Bclock Btotal Bbond CmassOld ChOld CbOld
    hCmOld hChOld hCbOld hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Clow,hClow,HQ⟩:=eventually_actual_minimum_wholeLaw_low_profile_moment
    (D:=D) ellLow hellLow Bclock Btotal Bbond ChLow hBbond hChLow
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Clow*(1+CmassLow),hCp,by positivity,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M L us hus hret hmesh
  filter_upwards [hnP M L us hus hret hmesh,hnQ M L us hus hret hmesh] with jGrid hgridP hgridQ
  dsimp only at hgridP hgridQ ⊢
  intro U T l t s hl ht hs G initial x W field hxs hxW hclock hbond hmassOld hfieldOld hβ hαeq hfieldLow hmassLow A E hE hA hT
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let q:=finitePhysicalCavitySquareVariance n U as b h l t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hx : 0 < x:=M.hxs.trans_le hxs
  have hW : 0 < W:=hx.trans_le hxW
  let rho:=Clow*(1+CmassLow)*W
  have hrho : 0 < rho:=by dsimp [rho];positivity
  have hPscale : 0 ≤ Cp^a*sourceMonomialScale x W initial := by
    rw [←source_factor_scale_product]
    exact mul_nonneg (pow_nonneg hCp.le _) (Finset.prod_nonneg fun e _=>(source_factor_scale_pos hx hW initial e).le)
  have hqpos : 0 < p/(p-2):=div_pos (by linarith) (by linarith)
  have hPbig : T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>|G.product σ|^(2*dOld)) 0 ≤ (Cp^a*sourceMonomialScale x W initial)^(2*dOld) :=
    hgridP U T l t hl ht G initial x W field hxs hxW hclock hbond hmassOld hfieldOld hβ hαeq
  have hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>|G.product σ|^(2*(p/(p-2)))) 0 ≤ (Cp^a*sourceMonomialScale x W initial)^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 q 0 G.product
      (by positivity) (show 2*(p/(p-2)) ≤ ((2*dOld:ℕ):ℝ) by push_cast;linarith) hPscale
    simpa only [Real.rpow_natCast] using hPbig
  have hLowBig : ∀j,j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 q
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^(2*ellLow)) 0 ≤ rho^(2*ellLow) := by
    intro j hj
    by_cases hlow : j < U
    · have H:=hgridQ U l t s hl ht hs j hj hclock hbond (hfieldLow j hj)
      apply H.trans
      apply pow_le_pow_left₀
        (mul_nonneg hClow.le (add_nonneg M.hxs.le (partitionPoint_mem as ho j).1))
      have Hmass : M.xs+partitionPoint 0 as j ≤ (1+CmassLow)*W:=by
        have Hm:=hmassLow j hj hlow
        nlinarith
      simpa only [rho,mul_assoc] using mul_le_mul_of_nonneg_left Hmass hClow.le
    · change (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavitySquareVariance n U as b h l t) _ 0 ≤ _
      simp_rw [finitePhysicalSquareLowKernel_at_high n U as b h s hlow,
        abs_zero,zero_pow (by omega : 2*ellLow≠0)]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hrho.le _
  have hLow : ∀j,j ≤ as.length → (ClockTree.pairClock as j).disorderExpect
      (fullWeight n) (fullFeature n) 0 q
      (fun σ=>|finitePhysicalSquareLowKernel n U as b h s j
        (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2|^((2*(p/(p-2)))*(k:ℝ))) 0 ≤ rho^((2*(p/(p-2)))*(k:ℝ)) := by
    intro j hj
    by_cases hk : k=0
    · simp only [hk,Nat.cast_zero,mul_zero,Real.rpow_zero,
        (ClockTree.pairClock as j).disorderExpect_one (fullWeight_pos n) (fullFeature n) ho]
      exact le_rfl
    · apply (ClockTree.pairClock as j).disorderExpect_rpow_moment_le
        (fullWeight_pos n) (fullFeature n) ho 0 q 0
        (fun σ=>finitePhysicalSquareLowKernel n U as b h s j
          (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2)
        (by positivity) hLowOrder hrho.le
      simpa only [Real.rpow_natCast] using hLowBig j hj
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  exact nativeWholeLaw_two_profile_error_bound n U k ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hl ht T hT G.product
    hPscale hrho hE hp hP hLow A hA

end OAI.SKFluctuations.Cavity
