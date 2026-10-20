module

public import ComparisonSignedCavityInheritedTransientHighZero
public import ComparisonSignedCavityInheritedTransientHighBudget
public import ComparisonSignedCavityCenteredFixedLowHigh
public import ComparisonSignedCavityInheritedFixedLowTwoHigh
public import ComparisonSignedCavityInheritedOriginalScalarLowJets
public import ComparisonSignedCavityGRestorationOriginalBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_canonical_centered_fixed_low_one_two_high_budget
    (aDegree rBound dOld ellLow : ℕ) (ha : 0<aDegree) (hdOld : 0<dOld) (hellLow : 0<ellLow)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOld:ℝ))
    (hLowOrder : 2*(p/(p-2))≤((2*ellLow:ℕ):ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),U≤as.length →
          t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,
          |nativeCenteredFixedLowHigh n q U b h K T (G.canonicalMinimumSource M forms).product a z 1 2 t|≤
            C*W*sourceMonomialScale x W initial*
              nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (4/p) := by
  obtain ⟨Cp0,Cq0,hCp0,hCq0,H0⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_two_high_budget
    (D:=D) aDegree 0 rBound dOld ellLow ha hdOld hellLow p hp hOrder (by norm_num)
    Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,Cq1,hCp1,hCq1,H1⟩:=eventually_actual_minimum_inherited_canonical_fixed_low_two_high_budget
    (D:=D) aDegree 1 rBound dOld ellLow ha hdOld hellLow p hp hOrder (by simpa only [Nat.cast_one,mul_one] using hLowOrder)
    Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let a0:=pairForkVariation rBound*pairForkVariation (rBound+2)*absJetVariation (rBound+4) 0*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp0^aDegree)*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let a1:=pairForkVariation rBound*pairForkVariation (rBound+2)*absJetVariation (rBound+4) 1*
    (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp1^aDegree)*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*(Cq1*(1+Ccut))
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else a1
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have Hpow : 0≤(2*Temp)^((p-2)/p):=Real.rpow_nonneg (mul_nonneg (by norm_num) hTemp) _
  have ha0 : 0≤a0:=by
    dsimp only [a0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _)
      (pairForkVariation_nonneg _)) (absJetVariation_nonneg _ _)) (by positivity)) Hpow) Hpow
  have ha1 : 0≤a1:=by
    dsimp only [a1]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _)
      (pairForkVariation_nonneg _)) (absJetVariation_nonneg _ _)) (by positivity)) Hpow) Hpow) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 1+B 0*A 1+B 1*A 0+1
  have hC : 0<C:=by
    have HH1:=hA 1
    have HH2:=mul_nonneg (hB 0) (hA 1)
    have HH3:=mul_nonneg (hB 1) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H0,H1,HG] with n hn0 hn1 hng
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hsource hxs L us hus hret hmesh,hn1 M hsource hxs L us hus hret hmesh] with jGrid hgrid0 hgrid1
  dsimp only at hgrid0 hgrid1 ⊢
  intro U T t hU ht hT G forms initial x W hxsx hxW hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalMinimumSource M forms).product
  let Z:=sourceMonomialScale x W initial
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (4/p)
  let f : Fin 4→ℝ:=fun i=>nativeFixedLowHighProfile n q U b h K T P i 2 1 0 t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i 0 0
  let J:=nativeFixedLowHighProfile n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 1 2 1 0 t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans (hxsx.trans hxW)
  have hZ : 0≤Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T (4/p)
  have Hf0:=hgrid0 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass []
  have Hf1:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass []
  simp only [siteMonomial,mul_one] at Hf0 Hf1
  have hf i (hi : i.val≤1) : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,Mclock,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · norm_num at hi
    · norm_num at hi
  have hg i (_hi : i.val≤1) : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hsource us jGrid hus U T W 0 (hxsx.trans hxW) hcut (by norm_num) hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 1*W*Z*Cost:=by
    have HH:=hgrid1 U T 0 t 1 hU (by norm_num) ht (by norm_num) hT G forms initial x W hxsx hxW hcut hmass [a,z]
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    convert HH using 1
    dsimp only [J,A,a1,Z,Cost,Mclock,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_fixed_first_product_bound hW A B f g hB hJ hf hg
  apply HH.trans
  have HC : A 1+B 0*A 1+B 1*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    hW) hZ) hCost
  simpa only [nativeCenteredFixedLowHigh,f,g,J,Z,Cost,P,q,b,h,K,S,as] using HB

end OAI.SKFluctuations.Cavity
