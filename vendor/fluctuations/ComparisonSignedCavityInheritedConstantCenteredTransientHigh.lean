module

public import ComparisonSignedCavityCenteredTransientHighThird
public import ComparisonSignedCavityInheritedConstantHighSource
public import ComparisonSignedCavityInheritedOriginalScalarLowJets
public import ComparisonSignedCavityGRestorationOriginalBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_constant_centered_transient_HIGH_budget
    (rBound : ℕ)
    (Bclock Temp Cf Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),U≤as.length →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀W : ℝ,M.xs≤W → partitionPoint 0 as U≤Ccut*W →
        ∀a z : T.Slot,
          |nativeCenteredTransientHighThird n q U b h K T (fun _=>1) a z l t|≤
            C*W^3*
              nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1 := by
  obtain ⟨Cq1,hCq1,H1⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget
    (D:=D) 1 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq2,hCq2,H2⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget
    (D:=D) 2 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq3,hCq3,H3⟩:=eventually_actual_minimum_inherited_constant_fixed_low_one_high_budget
    (D:=D) 3 rBound (by norm_num) Bclock Temp Cf Ccut hTemp hCf hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets
    (D:=D) rBound Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let a0:=pairForkVariation rBound
  let a1:=pairForkVariation rBound*absJetVariation (rBound+2) 1*(Cq1*(1+Ccut))^1
  let a2:=pairForkVariation rBound*absJetVariation (rBound+2) 2*(Cq2*(1+Ccut))^2
  let a3:=pairForkVariation rBound*absJetVariation (rBound+2) 3*(Cq3*(1+Ccut))^3
  let A : Fin 4→ℝ:=fun i=>if i.val=0 then a0 else if i.val=1 then a1 else if i.val=2 then a2 else a3
  let B : Fin 4→ℝ:=fun i=>jetVariation rBound i*Ck^(i:ℕ)
  have ha0 : 0≤a0:=pairForkVariation_nonneg _
  have ha1 : 0≤a1:=by dsimp only [a1];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have ha2 : 0≤a2:=by dsimp only [a2];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have ha3 : 0≤a3:=by dsimp only [a3];exact mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (absJetVariation_nonneg _ _)) (by positivity)
  have hA i : 0≤A i:=by
    dsimp only [A]
    split_ifs <;> first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  have hB i : 0≤B i:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let C:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0+1
  have hC : 0<C:=by
    have H1:=hA 3
    have H2:=mul_nonneg (hB 0) (hA 3)
    have H3:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) (hB 1)) (hA 2)
    have H4:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) (hB 2)) (hA 1)
    have H5:=mul_nonneg (hB 3) (hA 0)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H1,H2,H3,HG] with n hn1 hn2 hn3 hng
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn1 M hsource hxs L us hus hret hmesh,
    hn2 M hsource hxs L us hus hret hmesh,hn3 M hsource hxs L us hus hret hmesh] with jGrid hgrid1 hgrid2 hgrid3
  dsimp only at hgrid1 hgrid2 hgrid3 ⊢
  intro U T l t hU hl ht hT W hxW hcut a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P : T.Assignment→ℝ:=fun _=>1
  let Z : ℝ:=1
  let Cost:=nativeWholeLawProfileCost n (cutFullVariance n q U l t b h K) (cutTSlope n U 0 b h K) T 1
  let f : Fin 4→ℝ:=fun i=>nativeTransientHighJet n q U b h K T P 0 i l t
  let g : Fin 4→ℝ:=fun i=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) i l 0
  let J:=nativeTransientHighJet n q U b h K T (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 3 l t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans hxW
  have hZ : 0≤Z:=by norm_num [Z]
  have hCost : 0≤Cost:=native_whole_law_profile_cost_nonneg n ho _ _ T 1
  have Hfixed (Q : T.Assignment→ℝ) (k : ℕ) : nativeFixedLowHighProfile n q U b h K T Q k 1 t l t=
      nativeTransientHighJet n q U b h K T Q 0 k l t:=rfl
  have Hf0:=native_constant_fixed_zero_high_bound n U rBound q b h K T ho hT [] t l t
  have Hf1:=hgrid1 U T l t t hU hl ht ht hT W hxW hcut []
  have Hf2:=hgrid2 U T l t t hU hl ht ht hT W hxW hcut []
  have Hf3:=hgrid3 U T l t t hU hl ht ht hT W hxW hcut []
  rw [Hfixed] at Hf0 Hf1 Hf2 Hf3
  simp only [siteMonomial] at Hf0 Hf1 Hf2 Hf3
  have hf i : |f i|≤A i*W^(i:ℕ)*Z*Cost:=by
    fin_cases i
    · convert Hf0 using 1
      dsimp only [f,A,a0,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
    · convert Hf1 using 1
      dsimp only [f,A,a1,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf2 using 1
      dsimp only [f,A,a2,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
    · convert Hf3 using 1
      dsimp only [f,A,a3,Z,Cost,P,q,b,h,K,S,as]
      norm_num [mul_pow]
      ring_nf
      simp
  have hg i : |g i|≤B i*W^(i:ℕ):=by
    have HH:=hng M hsource us jGrid hus U T W l hxW hcut hl hT a z (i:ℕ)
    convert HH using 1
    dsimp only [g,B]
    rw [mul_pow]
    ring
  have hJ : |J|≤A 3*W^3*Z*Cost:=by
    have HH:=hgrid3 U T l t t hU hl ht ht hT W hxW hcut [a,z]
    rw [Hfixed] at HH
    have HE : (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2)=
        (fun σ=>P σ*siteMonomial T σ [a,z]):=by
      funext σ
      rw [←nativeScalarTest_pair T a z,nativeScalarTest_full]
    dsimp only [J]
    rw [HE]
    simp only [P,one_mul]
    convert HH using 1
    dsimp only [J,A,a3,Z,Cost,P,q,b,h,K,S,as]
    norm_num [mul_pow]
    ring_nf
    simp
  have HH:=native_centered_third_HIGH_product_bound hW hZ hCost A B f g hA hB hJ hf hg
  apply HH.trans
  have HC : A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0≤C:=by dsimp [C];linarith
  have HB:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right HC
    (pow_nonneg hW 3)) hZ) hCost
  simpa only [nativeCenteredTransientHighThird,f,g,J,Z,Cost,P,q,b,h,K,S,as,mul_one] using HB

end OAI.SKFluctuations.Cavity
