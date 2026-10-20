module

public import ComparisonSignedCavityInitialInheritedJetModulusBudget
public import ComparisonSignedCavityInitialCenteredModulusProduct
public import ComparisonSignedCavityInheritedOriginalScalarLowJets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000

 theorem eventually_actual_minimum_inherited_initial_centered_LOW_modulus_budget
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
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
        let Mclock:=4*Cf+2*Temp
        ∀(U V i star : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀a z : T.Slot,a≠z → V≤T.splitIndex a z →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeTransientCenteredLowErrorPart n q i star U b h K T
            (G.canonicalMinimumSource M forms).restProduct (sitePair T a z) 0 .initial l t|≤
            C*W*M.xs*d*p0 := by
  obtain ⟨Cp0,hCp0,HP0⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget
    (D:=D) aDegree 0 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp1,hCp1,HP1⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget
    (D:=D) aDegree 1 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp2,hCp2,HP2⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget
    (D:=D) aDegree 2 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cp3,hCp3,HP3⟩:=eventually_actual_minimum_inherited_initial_plain_jet_modulus_budget
    (D:=D) aDegree 3 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CJ2,hCJ2,HJ2⟩:=eventually_actual_minimum_inherited_initial_jet_modulus_budget
    (D:=D) aDegree 2 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CJ3,hCJ3,HJ3⟩:=eventually_actual_minimum_inherited_initial_jet_modulus_budget
    (D:=D) aDegree 3 rBound Bclock Temp Cf Cmass Ccut Couter hTemp hCf hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ck,hCk,HG⟩:=eventually_actual_minimum_inherited_original_scalar_low_jets
    (D:=D) rBound Bclock Temp Cf Couter hTemp hCf hCouter hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cp:=Cp0+Cp1+Cp2+Cp3+CJ2+CJ3+1
  have hCp : 0<Cp:=by dsimp [Cp];positivity
  let A : Fin 4→ℝ:=fun j=>absJetVariation rBound (j+1)*Cp
  let B : Fin 4→ℝ:=fun j=>jetVariation rBound j*Ck^(j:ℕ)
  have hA j : 0≤A j:=mul_nonneg (absJetVariation_nonneg _ _) hCp.le
  have hB j : 0≤B j:=mul_nonneg (jetVariation_nonneg _ _) (pow_nonneg hCk.le _)
  let c3:=A 3+B 0*A 3+3*B 1*A 2+3*B 2*A 1+B 3*A 0
  let c2:=A 2+B 0*A 2+2*B 1*A 1+B 2*A 0
  let C:=c3+3*c2+1
  have hc3 : 0≤c3:=native_centered_LOW_third_coefficient_nonneg hA hB
  have hc2 : 0≤c2:=native_centered_LOW_second_coefficient_nonneg hA hB
  have hC : 0<C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HP0,HP1,HP2,HP3,HJ2,HJ3,HG] with n hn0 hn1 hn2 hn3 hnJ2 hnJ3 hng
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn0 M hsource hxs L us hus hret hmesh,hn1 M hsource hxs L us hus hret hmesh,
    hn2 M hsource hxs L us hus hret hmesh,hn3 M hsource hxs L us hus hret hmesh,
    hnJ2 M hsource hxs L us hus hret hmesh,hnJ3 M hsource hxs L us hus hret hmesh]
    with jGrid hgrid0 hgrid1 hgrid2 hgrid3 hgridJ2 hgridJ3
  dsimp only at hgrid0 hgrid1 hgrid2 hgrid3 hgridJ2 hgridJ3 ⊢
  intro U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let P:=(G.canonicalMinimumSource M forms).product
  let Z:=sourceMonomialScale x W initial
  let Mclock:=4*Cf+2*Temp
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  let f : Fin 4→ℝ:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T P 0 .initial j l t
  let g : Fin 4→ℝ:=fun j=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) (cavityEmbed 0) j l 0
  let J:=fun j=>nativeTransientLowErrorPartJet n q i star U b h K T
    (fun σ=>P σ*sitePair T a z (T.cavityAssignment σ).2) 0 .initial j l t
  have hW : 0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hZ : 0≤Z:=by
    dsimp [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hcap (a : ℝ) (ha : a≤Cp) (k : ℕ) :
      absJetVariation rBound (k+1)*(a*M.xs*d*Z*W^(k-1))≤
        (absJetVariation rBound (k+1)*Cp)*W^(k-1)*Z*M.xs*d := by
    have H:=mul_le_mul_of_nonneg_left ha
      (mul_nonneg (absJetVariation_nonneg rBound (k+1))
        (mul_nonneg (mul_nonneg (mul_nonneg M.hxs.le hd) hZ) (pow_nonneg hW.le (k-1))))
    convert H using 1 <;> ring
  have Hf0:=hgrid0 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf0' : |f 0|≤A 0*W^(0-1)*Z*M.xs*d:=by
    apply Hf0.trans
    exact Hcap Cp0 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 0
  have Hf1:=hgrid1 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf1' : |f 1|≤A 1*W^(1-1)*Z*M.xs*d:=by
    apply Hf1.trans
    exact Hcap Cp1 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 1
  have Hf2:=hgrid2 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf2' : |f 2|≤A 2*W^(2-1)*Z*M.xs*d:=by
    apply Hf2.trans
    exact Hcap Cp2 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 2
  have Hf3:=hgrid3 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
  have Hf3' : |f 3|≤A 3*W^(3-1)*Z*M.xs*d:=by
    apply Hf3.trans
    exact Hcap Cp3 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 3
  have hf j : |f j|≤A j*W^((j:ℕ)-1)*Z*M.xs*d:=by
    fin_cases j
    · exact Hf0'
    · exact Hf1'
    · exact Hf2'
    · exact Hf3'
  have hg j : |g j|≤B j*W^(j:ℕ):=by
    have H:=hng M hsource us jGrid hus U T W l (hxsx.trans hxW) houter hl hT a z (j:ℕ)
    convert H using 1
    dsimp [g,B]
    rw [mul_pow]
    ring
  have HJ2:=hgridJ2 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget
  have HJ2' : |J 2|≤A 2*W^(2-1)*Z*M.xs*d:=by
    apply HJ2.trans
    exact Hcap CJ2 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 2
  have HJ3:=hgridJ3 U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass a z haz htarget
  have HJ3' : |J 3|≤A 3*W^(3-1)*Z*M.xs*d:=by
    apply HJ3.trans
    exact Hcap CJ3 (by dsimp [Cp];linarith only [hCp0,hCp1,hCp2,hCp3,hCJ2,hCJ3]) 3
  have H:=native_centered_initial_LOW_modulus_product_bound hW hW1 hZ M.hxs.le hd hl
    A B f g (J 2) (J 3) hA hB (by simpa only [Nat.reduceSub,pow_one] using HJ2')
    (by simpa only [Nat.reduceSub] using HJ3') hf hg
  have Hleft : nativeTransientCenteredLowErrorPart n q i star U b h K T
      (G.canonicalMinimumSource M forms).restProduct (sitePair T a z) 0 .initial l t=
      l*(J 3-productJet3 g f 3)+3*(J 2-productJet3 g f 2) := by
    dsimp only [nativeTransientCenteredLowErrorPart,J,f,g]
    simp_rw [←(G.canonicalMinimumSource M forms).product_eq_restProduct]
    simp only [map_zero,P]
  rw [Hleft]
  apply H.trans
  have HC : c3+3*c2≤C:=by dsimp [C];linarith
  have Hcap:=mul_le_mul_of_nonneg_right HC (show 0≤W*Z*M.xs*d from mul_nonneg (mul_nonneg (mul_nonneg hW.le hZ) M.hxs.le) hd)
  convert Hcap using 1 <;> ring

end OAI.SKFluctuations.Cavity
