module

public import ComparisonActualHighWallInitialSavedLevelCoefficients
public import ComparisonActualHighWallInitialFullB0EndpointEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 48000000

def actualHighWallInitialSavedRootBundle (depth : ℕ) (f : ℝ) : ℝ :=
  f^((8:ℝ)⁻¹)+f^((4:ℝ)⁻¹)+f^(((2*(depth+2):ℕ):ℝ)⁻¹)+f

theorem exists_actual_high_wall_initial_saved_uniform_coefficient_modulus
    (depth : ℕ) (P : (j : Fin depth) → ActualHighWallInitialForestSavedLevelConstants j.val)
    (Bclock cK : ℝ) (hBc : 0 ≤ Bclock) (hcK : 0 < cK) :
    ∃CA CB CF CZ : ℝ,0 < CA ∧ 0 < CB ∧ 0 < CF ∧ 0 < CZ ∧
      ∀{n : ℕ} {m delta cl cu Az C0 Ct D : ℝ}
        (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (as : List PositiveMass) (i star : ℕ) (eta Ccut e : ℝ),0 ≤ e →
        (n:ℝ)^(-eta)+((n+1:ℕ):ℝ)^(-m)+
          ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))+M.data.d^3 ≤ e →
        (1+actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0))*
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as star+1/(n+1:ℕ)) ≤ e*M.data.d →
        (∫u in 0..Ccut*M.data.d,Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2)) ≤ e*M.data.d →
        ∀j : Fin depth,
          (P j).A eta cK M as i ≤ CA*(actualHighWallInitialSavedRootBundle depth
            ((nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))/M.data.d)+e) ∧
          (P j).B Ccut cK M as i star ≤ CB*M.data.d*(actualHighWallInitialSavedRootBundle depth
            ((nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))/M.data.d)+e) ∧
          (P j).F M ≤ CF*e ∧ (P j).Cfr ≤ CZ := by
  classical
  let K:=originalInitialPairComparisonConstant (2*max Bclock 0) (max Bclock 0)
  have hK : 0 ≤ K:=(original_initial_pair_comparison_constant_pos _ _).le
  have HE : ∀j : Fin depth,∃Cenv : ℝ,0 < Cenv ∧ ∀Di d N eta : ℝ,
      0 ≤ Di → 0 < d → 0 ≤ N →
      actualHighWallInitialFullB0Envelope (1+j.val) (P j).C (P j).CiU (P j).CiB
        (P j).CiM (P j).Cf (P j).Cr (K*Di) d N eta ≤
        Cenv*((Di/d)^((8:ℝ)⁻¹)+(Di/d)^((4:ℝ)⁻¹)+
          (Di/d)^(((2*(depth+2):ℕ):ℝ)⁻¹)+N^(-eta)+d^3) := by
    intro j
    exact exists_actual_high_wall_initial_full_B0_endpoint_envelope depth j K hK
      (P j).C (P j).CiU (P j).CiB (P j).CiM
      (fun a=>((P j).hC a).1.le) (fun a=>((P j).hC a).2.1)
      (fun a=>((P j).hC a).2.2.1) (fun a=>((P j).hC a).2.2.2)
      (P j).Cf (P j).Cr (P j).hCf.le (P j).hCr
  choose Cenv hCenv Henv using HE
  let V:=fun j : Fin depth=>nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 j.val
  let VP:=fun j : Fin depth=>nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
    (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 j.val
  have hCW : 0 ≤ Bclock/(Real.exp (-4*Bclock)*cK):=by positivity
  have hV j : 0 ≤ V j:=nativeActualWeightedFrontierCost_nonneg _ hCW _ _ _
  have hVP j : 0 ≤ VP j:=nativeActualWeightedProfileFrontierCost_nonneg _ hCW _ _ _
  let a:=fun j : Fin depth=>2*V j*((P j).Ca+(P j).Cg+(P j).Cd+2*Cenv j)+
    2*VP j*(2*((P j).Ca+2*(P j).Cl+(P j).Cj+(P j).C4+(P j).CY)+(P j).Ch)
  let b:=fun j : Fin depth=>2*V j*(3*(P j).CY+(P j).Cgl+(P j).Cjl)
  have ha j : 0 ≤ a j:=by
    have hCa:=(P j).hCa
    have hCg:=(P j).hCg
    have hCd:=(P j).hCd
    have hCl:=(P j).hCl
    have hCj:=(P j).hCj
    have hC4:=(P j).hC4
    have hCY:=(P j).hCY
    have hCh:=(P j).hCh
    dsimp only [a];positivity [hV j,hVP j,hCenv j]
  have hb j : 0 ≤ b j:=by
    have hCY:=(P j).hCY
    have hCgl:=(P j).hCgl
    have hCjl:=(P j).hCjl
    dsimp only [b];positivity [hV j]
  let CA:=(∑j : Fin depth,a j)+1
  let CB:=(∑j : Fin depth,b j)+1
  let CF:=(∑j : Fin depth,(P j).Cfirst)+1
  let CZ:=(∑j : Fin depth,(P j).Cfr)+1
  have hCA : 0 < CA:=by
    have HS : 0 ≤ ∑j : Fin depth,a j:=Finset.sum_nonneg (fun j _=>ha j)
    dsimp only [CA];linarith
  have hCB : 0 < CB:=by
    have HS : 0 ≤ ∑j : Fin depth,b j:=Finset.sum_nonneg (fun j _=>hb j)
    dsimp only [CB];linarith
  have hCF : 0 < CF:=by
    dsimp only [CF]
    have HS : 0 ≤ ∑j : Fin depth,(P j).Cfirst:=Finset.sum_nonneg (fun j _=>(P j).hCfirst.le)
    linarith
  have hCZ : 0 < CZ:=by
    dsimp only [CZ]
    have HS : 0 ≤ ∑j : Fin depth,(P j).Cfr:=Finset.sum_nonneg (fun j _=>(P j).hCfr.le)
    linarith
  refine ⟨CA,CB,CF,CZ,hCA,hCB,hCF,hCZ,?_⟩
  intro n m delta cl cu Az C0 Ct D M as i star eta Ccut e he Hnoise Hstar Hthermal j
  let Di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let f:=Di/M.data.d
  let R:=actualHighWallInitialSavedRootBundle depth f
  let X:=R+e
  let rho:=((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  have hDi : 0 ≤ Di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hf : 0 ≤ f:=div_nonneg hDi M.data.hd.le
  have hN : 0 ≤ (n:ℝ)^(-eta):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1 : 0 ≤ ((n+1:ℕ):ℝ)^(-m):=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hrho : 0 ≤ rho:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hd3 : 0 ≤ M.data.d^3:=pow_nonneg M.data.hd.le _
  have Hnoise' : (n:ℝ)^(-eta)+((n+1:ℕ):ℝ)^(-m)+rho+M.data.d^3 ≤ e:=Hnoise
  have h8 : 0 ≤ f^((8:ℝ)⁻¹):=Real.rpow_nonneg hf _
  have h4 : 0 ≤ f^((4:ℝ)⁻¹):=Real.rpow_nonneg hf _
  have hp : 0 ≤ f^(((2*(depth+2):ℕ):ℝ)⁻¹):=Real.rpow_nonneg hf _
  have hR : 0 ≤ R:=by dsimp only [R,actualHighWallInitialSavedRootBundle];positivity
  have hX : 0 ≤ X:=add_nonneg hR he
  have heX : e ≤ X:=by dsimp only [X];linarith
  have hfX : f ≤ X:=by dsimp only [X,R,actualHighWallInitialSavedRootBundle];linarith
  have hnX : (n:ℝ)^(-eta) ≤ X:=by dsimp only [rho] at hrho;linarith
  have hn1X : ((n+1:ℕ):ℝ)^(-m) ≤ X:=by dsimp only [rho] at hrho;linarith
  have hrhoX : rho ≤ X:=by dsimp only [rho];linarith
  have hrhoE : rho ≤ e:=by dsimp only [rho];linarith
  have Hq : actualHighWallInitialFullB0Envelope (1+j.val) (P j).C (P j).CiU (P j).CiB
      (P j).CiM (P j).Cf (P j).Cr (originalHighWallInitialPairErrorScale M as i)
      M.data.d (n:ℝ) eta ≤ Cenv j*X := by
    have H:=Henv j Di M.data.d (n:ℝ) eta hDi M.data.hd (Nat.cast_nonneg _)
    change actualHighWallInitialFullB0Envelope (1+j.val) (P j).C (P j).CiU (P j).CiB
      (P j).CiM (P j).Cf (P j).Cr (originalHighWallInitialPairErrorScale M as i)
      M.data.d (n:ℝ) eta ≤ _ at H
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ (hCenv j).le
    dsimp only [X,R,actualHighWallInitialSavedRootBundle,f,rho] at *
    linarith
  have HAlocal : (P j).A eta cK M as i ≤ a j*X := by
    have H1:=mul_le_mul_of_nonneg_left hnX (P j).hCa.le
    have H2:=mul_le_mul_of_nonneg_left hnX (P j).hCg.le
    have H3:=mul_le_mul_of_nonneg_left hn1X (P j).hCd.le
    have HL:=mul_le_mul_of_nonneg_left (show
        (P j).Ca*(n:ℝ)^(-eta)+(P j).Cg*(n:ℝ)^(-eta)+(P j).Cd*((n+1:ℕ):ℝ)^(-m)+
          2*actualHighWallInitialFullB0Envelope (1+j.val) (P j).C (P j).CiU (P j).CiB
            (P j).CiM (P j).Cf (P j).Cr (originalHighWallInitialPairErrorScale M as i)
            M.data.d (n:ℝ) eta ≤ ((P j).Ca+(P j).Cg+(P j).Cd+2*Cenv j)*X by
          nlinarith only [H1,H2,H3,Hq]) (show 0 ≤ 2*V j by positivity [hV j])
    have hCP : 0 ≤ 2*((P j).Ca+2*(P j).Cl+(P j).Cj+(P j).C4+(P j).CY)+(P j).Ch:=by
      have hCa:=(P j).hCa
      have hCl:=(P j).hCl
      have hCj:=(P j).hCj
      have hC4:=(P j).hC4
      have hCY:=(P j).hCY
      have hCh:=(P j).hCh
      positivity
    have HH:=mul_le_mul_of_nonneg_left hrhoX (show
        0 ≤ 2*VP j*(2*((P j).Ca+2*(P j).Cl+(P j).Cj+(P j).C4+(P j).CY)+(P j).Ch) by
          positivity [hVP j])
    have H:=add_le_add HL HH
    dsimp only [ActualHighWallInitialForestSavedLevelConstants.A,a,V,VP,rho] at *
    nlinarith only [H]
  have HDi : Di ≤ M.data.d*X:=by
    have H:=mul_le_mul_of_nonneg_left hfX M.data.hd.le
    have HE : M.data.d*f=Di:=by dsimp only [f];field_simp [M.data.hd.ne']
    rwa [HE] at H
  have HstarX:=Hstar.trans (mul_le_mul_of_nonneg_right heX M.data.hd.le)
  have HthermalX:=Hthermal.trans (mul_le_mul_of_nonneg_right heX M.data.hd.le)
  have HBlocal : (P j).B Ccut cK M as i star ≤ b j*M.data.d*X:=by
    have H1:=mul_le_mul_of_nonneg_left HDi (P j).hCY.le
    have HC : 0 ≤ (P j).CY+(P j).Cgl+(P j).Cjl:=by
      have hCY:=(P j).hCY
      have hCgl:=(P j).hCgl
      have hCjl:=(P j).hCjl
      positivity
    have H2:=mul_le_mul_of_nonneg_left HstarX HC
    have H3:=mul_le_mul_of_nonneg_left HthermalX (P j).hCY.le
    have H:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add H1 H2) H3)
      (show 0 ≤ 2*V j by positivity [hV j])
    dsimp only [ActualHighWallInitialForestSavedLevelConstants.B,b,V] at *
    nlinarith only [H]
  have haCA : a j ≤ CA:=by
    have H:=Finset.single_le_sum (fun k _=>ha k) (Finset.mem_univ j)
    dsimp only [CA];linarith
  have hbCB : b j ≤ CB:=by
    have H:=Finset.single_le_sum (fun k _=>hb k) (Finset.mem_univ j)
    dsimp only [CB];linarith
  have hfCF : (P j).Cfirst ≤ CF:=by
    have H:=Finset.single_le_sum (fun k _=>(P k).hCfirst.le) (Finset.mem_univ j)
    dsimp only [CF];linarith
  have hzCZ : (P j).Cfr ≤ CZ:=by
    have H:=Finset.single_le_sum (fun k _=>(P k).hCfr.le) (Finset.mem_univ j)
    dsimp only [CZ];linarith
  refine ⟨HAlocal.trans (mul_le_mul_of_nonneg_right haCA hX),?_,?_,hzCZ⟩
  · have H:=mul_le_mul_of_nonneg_right hbCB (mul_nonneg M.data.hd.le hX)
    have H' : b j*M.data.d*X ≤ CB*M.data.d*X:=by nlinarith only [H]
    exact HBlocal.trans H'
  · dsimp only [ActualHighWallInitialForestSavedLevelConstants.F]
    exact (mul_le_mul_of_nonneg_left hrhoE (P j).hCfirst.le).trans
      (mul_le_mul_of_nonneg_right hfCF he)

end OAI.SKFluctuations.Cavity
