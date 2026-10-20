module

public import ComparisonActualHighWallTransientLowZeroBudget
public import ComparisonActualHighWallTransientLowPartBudget
public import ComparisonActualHighWallScalarLowJets
public import ComparisonSignedCavityInheritedCenteredTransientLowPart

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_canonical_centered_transient_LOW_part_budget
    (aDegree rBound : ℕ)
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d → M.data.d ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i star U : ℕ) (part : NativeTransientLowErrorPart) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),U≤as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀a z : T.Slot,
          |nativeTransientCenteredLowErrorPart n q i star U b h K T
              (G.canonicalHighWallSource M forms).restProduct (sitePair T a z) 0 part l t|≤
            C*M.data.d^2*M.data.d^aDegree*
              (T.forkCost (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))+
              edgeBudget 0 as (nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
                (nativeTransientLowErrorPartDirection n U i star b h K part))) := by
  obtain ⟨Cp0,hCp0,H0⟩:=eventually_actual_high_wall_canonical_transient_low_part_zero_budget
    (D:=D) aDegree rBound Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,Cq1,hCp1,hCq1,H1⟩:=eventually_actual_high_wall_canonical_transient_low_part_budget
    (D:=D) aDegree 1 rBound (by norm_num) Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp2,Cq2,hCp2,hCq2,H2⟩:=eventually_actual_high_wall_canonical_transient_low_part_budget
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp3,Cq3,hCp3,hCq3,H3⟩:=eventually_actual_high_wall_canonical_transient_low_part_budget
    (D:=D) aDegree 3 rBound (by norm_num) Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_high_wall_original_scalar_low_jets
    (D:=D) rBound Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=2*max Bclock 0
  let a0:=pairForkVariation rBound*(Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp0^aDegree)
  let a1:=pairForkVariation rBound*absJetVariation (rBound+2) 1*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp1^aDegree)*Cq1^1
  let a2:=pairForkVariation rBound*absJetVariation (rBound+2) 2*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp2^aDegree)*Cq2^2
  let a3:=pairForkVariation rBound*absJetVariation (rBound+2) 3*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp3^aDegree)*Cq3^3
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else if i.val=1 then a1 else if i.val=2 then a2 else a3
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have ha0 : 0≤a0:=mul_nonneg (pairForkVariation_nonneg _) (by positivity)
  have ha1 : 0≤a1:=by
    dsimp only [a1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have ha2 : 0≤a2:=by
    dsimp only [a2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have ha3 : 0≤a3:=by
    dsimp only [a3]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _))
      (by positivity)) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let c3:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0
  let c2:=A 2+B 0*A 2+2*B 1*A 1+B 2*A 0
  let C:=c3+3*c2+1
  have hc3 : 0≤c3:=by dsimp only [c3];exact native_centered_LOW_third_coefficient_nonneg hA hB
  have hc2 : 0≤c2:=by dsimp only [c2];exact native_centered_LOW_second_coefficient_nonneg hA hB
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [H0,H1,H2,H3,HG] with n hn0 hn1 hn2 hn3 hng
  intro M hwork hW1 L us hus hret hmesh
  filter_upwards [hn0 M hwork L us hus hret hmesh,hn1 M hwork L us hus hret hmesh,
    hn2 M hwork L us hus hret hmesh,hn3 M hwork L us hus hret hmesh] with jGrid hgrid0 hgrid1 hgrid2 hgrid3
  dsimp only at hgrid0 hgrid1 hgrid2 hgrid3 ⊢
  intro i star U part T l t hU hl ht hT G forms hcut hmass a z
  let W:=M.data.d
  have hxW : M.xs ≤ W:=by change M.xs ≤ M.data.d;rw [hwork]
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalHighWallSource M forms).product
  let Z:=M.data.d^aDegree
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
    (nativeTransientLowErrorPartDirection n U i star b h K part)
  let Cost:=T.forkCost R+edgeBudget 0 as R
  let f : Fin 4→ℝ:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T P 0 part j l t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i l 0
  let J:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T
    (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 part j l t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hZ : 0 ≤ Z:=pow_nonneg M.data.hd.le _
  have hR j : 0≤R j:=nativeWholeLawErrorRadius_nonneg _ _ _ _ _
  have hCost : 0≤Cost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have Hf0:=hgrid0 U T l t hl ht hT G forms hmass i star part []
  have Hf1:=hgrid1 U T l t hU hl ht hT G forms hcut hmass i star part []
  have Hf2:=hgrid2 U T l t hU hl ht hT G forms hcut hmass i star part []
  have Hf3:=hgrid3 U T l t hU hl ht hT G forms hcut hmass i star part []
  simp only [siteMonomial,mul_one] at Hf0 Hf1 Hf2 Hf3
  have hf i : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,R,Mclock,P,q,b,h,K,S,as,W]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,R,Mclock,P,q,b,h,K,S,as,W]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf2 using 1
      dsimp only [f,A,a2,Z,Cost,R,Mclock,P,q,b,h,K,S,as,W]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf3 using 1
      dsimp only [f,A,a3,Z,Cost,R,Mclock,P,q,b,h,K,S,as,W]
      norm_num [mul_pow]
      ring_nf
      simp
  have hg i : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hwork us jGrid hus U T W l hxW hcut hl hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ (j : Fin 4) (hj : j=2 ∨ j=3) : |J j|≤A j*W^(j:ℕ)*Z*Cost:=by
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    rcases hj with rfl | rfl
    · have HH:=hgrid2 U T l t hU hl ht hT G forms hcut hmass i star part [a,z]
      dsimp only [J]
      rw [HE]
      convert HH using 1 <;> dsimp only [A,a2,Z,Cost,R,Mclock,P,q,b,h,K,S,as,W]
      all_goals norm_num [mul_pow]
      all_goals ring_nf
      all_goals simp
    · have HH:=hgrid3 U T l t hU hl ht hT G forms hcut hmass i star part [a,z]
      dsimp only [J]
      rw [HE]
      convert HH using 1 <;> dsimp only [A,a3,Z,Cost,R,Mclock,P,q,b,h,K,S,as,W]
      all_goals norm_num [mul_pow]
      all_goals ring_nf
      all_goals simp
  have HH:=native_centered_LOW_parts_product_bound hW hW1 hZ hCost hl A B f g (J 2) (J 3)
    hA hB (hJ 2 (Or.inl rfl)) (hJ 3 (Or.inr rfl)) hf hg
  have Hleft : nativeTransientCenteredLowErrorPart n q i star U b h K T
      (G.canonicalHighWallSource M forms).restProduct (sitePair T a z) 0 part l t=
      l*(J 3-productJet3 g f 3)+3*(J 2-productJet3 g f 2) := by
    dsimp only [nativeTransientCenteredLowErrorPart,J,f,g]
    simp_rw [←(G.canonicalHighWallSource M forms).product_eq_restProduct]
    simp only [map_zero,P]
  rw [Hleft]
  apply HH.trans
  have HC : c3+3*c2≤C:=by dsimp only [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (pow_nonneg hW 2)) hZ) hCost
  simpa only [Z,Cost,R,q,b,h,K,S,as,c3,c2] using HB

end OAI.SKFluctuations.Cavity
