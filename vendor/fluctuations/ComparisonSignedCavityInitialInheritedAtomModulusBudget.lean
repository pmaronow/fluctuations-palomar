module

public import ComparisonSignedCavityInitialAtomScaleDichotomy
public import ComparisonSignedCavityInitialInheritedAtomDichotomy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 28000000

private theorem initial_coefficient_power_le {R : ℝ} (hR : 0≤R) {k a : ℕ} (hka : k≤a) :
    R^k≤(max 1 R)^a := by
  exact (pow_le_pow_left₀ hR (le_max_right _ _) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) hka)

theorem eventually_actual_minimum_inherited_initial_atom_modulus_budget
    (aDegree aRows rBound : ℕ) (Bclock Temp Cf Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
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
        let Mclock:=4*Cf+2*Temp
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<V →
        ∀(site : Fin aRows→Bool) (v : Fin aRows→ℝ) (s w : Fin aRows→T.Slot),
          (∀i,v i∈Icc (0:ℝ) 1) → (∀i,s i≠w i) →
          (∀e,site e=true → V≤T.splitIndex (s e) (w e)) →
          (∀e,site e=false → T.splitIndex (s e) (w e)<U) →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalMinimumSource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            C*M.xs*d*p0*W^((nativeInitialOrdinaryRowSet site).card-1) := by
  obtain ⟨Cp,Cr,CpS,CrS,Cq,hCp,hCr,hCpS,hCrS,hCq,HD⟩:=
    eventually_actual_minimum_inherited_initial_atom_dichotomy (D:=D)
      aDegree aRows rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let A:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree
  let AS:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*CpS^aDegree
  let ep:=Real.exp (ClockTree.jetVariation 2 1*Mclock)
  let AV:=4*(rBound:ℝ)*(rBound+1)
  let ET:=Real.exp (2*(rBound:ℝ)*(rBound+1)*Mclock)
  let R:=Cr*(1+Couter)
  let RS:=CrS*(1+Couter)
  let Sraw:=Cr*(1+Ccut)
  let C1:=A*Sraw*(max 1 R)^aRows
  let C2:=AV*ET*AS*ep^(aRows+2)*Cq*(1+Ccut)*(max 1 RS)^aRows
  let C:=C1+C2+1
  have hR : 0<R:=mul_pos hCr (by linarith)
  have hRS : 0<RS:=mul_pos hCrS (by linarith)
  have hSraw : 0<Sraw:=mul_pos hCr (by linarith)
  have hA : 0<A:=by dsimp [A];positivity
  have hAS : 0<AS:=by dsimp [AS];positivity
  have hep : 0<ep:=Real.exp_pos _
  have hAV : 0≤AV:=by dsimp [AV];positivity
  have hET : 0<ET:=Real.exp_pos _
  have hC1 : 0≤C1:=by dsimp [C1];positivity
  have hC2 : 0≤C2:=by dsimp [C2];positivity
  have hC : 0<C:=by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HD] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hW1 houter hmass
    u z huz site v s w hv hne hsiteupper hrowlow
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let value:=T.disorderExpect (fullWeight n) (fullFeature n) 0 law
    (nativeOldInitialRowProduct n T (G.canonicalMinimumSource M forms).restProduct
      (nativeSmallCutOldErrorRestKernel n U b h K) u z
      (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e)) s w) 0
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
  let r:=fun e=>nativeSmallCutOrdinaryScale M.xs Cr as (site e) (T.splitIndex (s e) (w e))
  let rS:=fun e=>nativeSmallCutOrdinaryScale M.xs CrS as (site e) (T.splitIndex (s e) (w e))
  let k:=(nativeInitialOrdinaryRowSet site).card
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hx : 0<M.xs:=M.hxs
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hr e : 0≤r e:=(native_small_cut_ordinary_scale_pos M.hxs hCr ho (site e) _).le
  have hrS e : 0≤rS e:=(native_small_cut_ordinary_scale_pos M.hxs hCrS ho (site e) _).le
  have hsites e (he : site e=true) : r e=1:=by simp only [r,nativeSmallCutOrdinaryScale,he,ite_true]
  have hsitesS e (he : site e=true) : rS e=1:=by simp only [rS,nativeSmallCutOrdinaryScale,he,ite_true]
  have hrows e (he : site e=false) : r e≤R*W:=by
    simp only [r,nativeSmallCutOrdinaryScale,he,Bool.false_eq_true,ite_false]
    have Hmass:partitionPoint 0 as (T.splitIndex (s e) (w e))≤Couter*W:=
      (partitionPoint_mono as ho (hrowlow e he).le).trans houter
    have Hscale : M.xs+partitionPoint 0 as (T.splitIndex (s e) (w e))≤(1+Couter)*W:=by nlinarith only [hxsx,hxW,Hmass]
    exact (mul_le_mul_of_nonneg_left Hscale hCr.le).trans_eq (by dsimp [R];ring)
  have hrowsS e (he : site e=false) : rS e≤RS*W:=by
    simp only [rS,nativeSmallCutOrdinaryScale,he,Bool.false_eq_true,ite_false]
    have Hmass:partitionPoint 0 as (T.splitIndex (s e) (w e))≤Couter*W:=
      (partitionPoint_mono as ho (hrowlow e he).le).trans houter
    have Hscale : M.xs+partitionPoint 0 as (T.splitIndex (s e) (w e))≤(1+Couter)*W:=by nlinarith only [hxsx,hxW,Hmass]
    exact (mul_le_mul_of_nonneg_left Hscale hCrS.le).trans_eq (by dsimp [RS];ring)
  have hka : k≤aRows:=by
    have H:=Finset.card_le_card (Finset.filter_subset (fun e=>site e=false) (Finset.univ : Finset (Fin aRows)))
    simpa only [k,nativeInitialOrdinaryRowSet,Finset.card_univ,Fintype.card_fin] using H
  have HH:=hgrid U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hmass
    u z huz site v s w hv hne
  by_cases Hupper : ∀e,V≤T.splitIndex (s e) (w e)
  · have Hp:=native_initial_radius_product_le site rS (mul_nonneg hRS.le hW.le) hrS hsitesS hrowsS
    have Hpow:=initial_coefficient_power_le hRS.le hka
    have HWpow:=pow_le_pow_of_le_one hW.le hW1 (show k-1≤k by omega)
    have Hprod : (∏e,rS e)≤(max 1 RS)^aRows*W^(k-1):=by
      apply Hp.trans
      rw [mul_pow]
      exact mul_le_mul Hpow HWpow (pow_nonneg hW.le _) (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
    have hleaf : (T.leaves:ℝ)≤rBound:=by exact_mod_cast hT
    have HAv : ClockTree.absJetVariation T.leaves 1≤AV:=by
      simp only [ClockTree.absJetVariation]
      dsimp [AV]
      nlinarith only [hleaf,(show 0≤(T.leaves:ℝ) from Nat.cast_nonneg _)]
    have HM : 0≤Mclock:=by
      dsimp [Mclock]
      positivity
    have HEt : Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)≤ET:=by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ HM
      simp only [ClockTree.jetVariation]
      nlinarith only [hleaf,(show 0≤(T.leaves:ℝ) from Nat.cast_nonneg _)]
    have Hcoeff : ClockTree.absJetVariation T.leaves 1*
        Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)≤AV*ET:=
      mul_le_mul HAv HEt (Real.exp_nonneg _) hAV
    have HS:=HH.2 Hupper
    change |value|≤_ at HS ⊢
    have HprodEp : (∏e,ep*rS e)=ep^aRows*(∏e,rS e):=by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    change |value|≤
      ClockTree.absJetVariation T.leaves 1*(Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)*(AS*p0))*(ep*d)*
        (∏e,ep*rS e)*(ep*(Cq*(1+Ccut)*M.xs)) at HS
    rw [HprodEp] at HS
    have Hrest : |value|≤C2*M.xs*d*p0*W^(k-1):=by
      apply HS.trans
      calc
        _=(ClockTree.absJetVariation T.leaves 1*Real.exp (ClockTree.jetVariation T.leaves 1*Mclock))*(∏e,rS e)*
          (AS*p0*ep^(aRows+2)*d*Cq*(1+Ccut)*M.xs):=by rw [pow_add];ring
        _≤(AV*ET)*((max 1 RS)^aRows*W^(k-1))*(AS*p0*ep^(aRows+2)*d*Cq*(1+Ccut)*M.xs):=
          mul_le_mul_of_nonneg_right (mul_le_mul Hcoeff Hprod (Finset.prod_nonneg fun e _=>hrS e)
            (mul_nonneg hAV hET.le)) (by positivity)
        _=C2*M.xs*d*p0*W^(k-1):=by dsimp [C2];ring
    apply Hrest.trans
    have HC2 : C2≤C:=by dsimp [C];linarith only [hC1]
    have Hc:=mul_le_mul_of_nonneg_right HC2
      (show 0≤M.xs*d*p0*W^(k-1) by positivity)
    convert Hc using 1 <;> ring
  · obtain ⟨e,he⟩:=not_forall.mp Hupper
    have hsmallSplit : T.splitIndex (s e) (w e)<V:=not_le.mp he
    have heSite : site e=false:=Bool.eq_false_iff.mpr (fun H=>he (hsiteupper e H))
    have Hsmall : r e≤Sraw*M.xs:=by
      simp only [r,nativeSmallCutOrdinaryScale,heSite,Bool.false_eq_true,ite_false]
      have Hmass:partitionPoint 0 as (T.splitIndex (s e) (w e))≤Ccut*M.xs:=
        (partitionPoint_mono as ho hsmallSplit.le).trans hcut
      have Hscale : M.xs+partitionPoint 0 as (T.splitIndex (s e) (w e))≤(1+Ccut)*M.xs:=by nlinarith only [Hmass]
      exact (mul_le_mul_of_nonneg_left Hscale hCr.le).trans_eq (by dsimp [Sraw];ring)
    have Hp:=native_initial_radius_product_one_small site r (mul_nonneg hR.le hW.le)
      (mul_nonneg hSraw.le M.hxs.le) hr hsites hrows e heSite Hsmall
    have Hpow:=initial_coefficient_power_le hR.le (show k-1≤aRows by omega)
    have Hprod : (∏e,r e)≤Sraw*(max 1 R)^aRows*M.xs*W^(k-1):=by
      apply Hp.trans
      rw [mul_pow]
      have H:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right Hpow (pow_nonneg hW.le (k-1)))
        (mul_nonneg hSraw.le M.hxs.le)
      convert H using 1;ring
    have HR:=HH.1
    change |value|≤A*p0*d*(∏e,r e) at HR
    have Hraw : |value|≤C1*M.xs*d*p0*W^(k-1):=by
      apply HR.trans
      have H:=mul_le_mul_of_nonneg_left Hprod (mul_nonneg (mul_nonneg hA.le hp0) hd)
      convert H using 1;dsimp [C1];ring
    apply Hraw.trans
    have HC1 : C1≤C:=by dsimp [C];linarith only [hC2]
    have Hc:=mul_le_mul_of_nonneg_right HC1
      (show 0≤M.xs*d*p0*W^(k-1) by positivity)
    convert Hc using 1 <;> ring

end OAI.SKFluctuations.Cavity
