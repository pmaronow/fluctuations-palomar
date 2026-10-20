module

public import ComparisonSignedCavityInitialAtomRawBudget
public import ComparisonSignedCavityActualSmallCutAtomicProducer
public import ComparisonSignedCavityTransientLowStarProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 26000000

theorem eventually_actual_minimum_bare_initial_atom_dichotomy
    (aDegree aRows rBound : ℕ) (Bclock Temp Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp Cr CpS CrS Cq : ℝ,0<Cp ∧ 0<Cr ∧ 0<CpS ∧ 0<CrS ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        let ep:=Real.exp (ClockTree.jetVariation 2 1*Mclock)
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<V →
        ∀(site : Fin aRows→Bool) (v : Fin aRows→ℝ) (s w : Fin aRows→T.Slot),
          (∀i,v i∈Icc (0:ℝ) 1) → (∀i,s i≠w i) →
          let p0:=sourceMonomialScale M.xs W initial
          let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*p0
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          let r:=fun i=>nativeSmallCutOrdinaryScale M.xs Cr as (site i) (T.splitIndex (s i) (w i))
          let CS:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*CpS^aDegree*p0
          let rS:=fun i=>nativeSmallCutOrdinaryScale M.xs CrS as (site i) (T.splitIndex (s i) (w i))
          (|T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalMinimumSource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            C*d*(∏i,r i)) ∧
          ((∀i,V≤T.splitIndex (s i) (w i)) →
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalMinimumSource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            ClockTree.absJetVariation T.leaves 1*
              (Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)*CS)*(ep*d)*
              (∏i,ep*rS i)*(ep*(Cq*(1+Ccut)*M.xs))) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_continuum_even_all_degree
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_bare_continuum_low_profile_moment
    (D:=D) (2*(aRows+1)) (by omega) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CpS,CrS,Cq,hCpS,hCrS,hCq,HS⟩:=eventually_actual_minimum_bare_small_cut_old_initial_atom
    (D:=D) aDegree aRows rBound Bclock Temp Cmass Ccut hTemp hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr,CpS,CrS,Cq,hCp,hCr,hCpS,hCrS,hCq,?_⟩
  filter_upwards [HP,HR,HS] with n hnP hnR hnS
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs L us hus hret hmesh,
    hnR M hb hh hxs L us hus hret hmesh,hnS M hb hh hxs L us hus hret hmesh]
    with jGrid hgridP hgridR hgridS
  dsimp only at hgridP hgridR hgridS ⊢
  intro U V T l t hU hV0 hVU hcut hl ht hT G forms initial W hxW hmass
    u z huz site v s w hv hne
  constructor
  · let as:=finiteCutMasses us jGrid
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let law:=cutFullVariance n q U l t b h K
    let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
    let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
      sourceMonomialScale M.xs W initial
    let d:=actualLowErrorComparisonConstant Mclock Temp*
      (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
    let r:=fun e=>nativeSmallCutOrdinaryScale M.xs Cr as (site e) (T.splitIndex (s e) (w e))
    have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have HC : 0≤C:=by
      dsimp only [C]
      rw [←source_factor_scale_product]
      exact mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
        (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le)
    have Hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have Hne : u≠z:=by
      intro H
      rw [H,T.splitIndex_self] at huz
      omega
    have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|(G.canonicalMinimumSource M forms).product σ|^4) 0≤C^4:=
      hgridP U T l t hl ht hT G forms initial W hxW hmass
    have Herror : (ClockTree.pairClock as (T.splitIndex u z)).disorderExpect (fullWeight n) (fullFeature n) 0 law
        (fun σ=>(nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K) (T.splitIndex u z)
          (ClockTree.pairSpin as (T.splitIndex u z) σ).1
          (ClockTree.pairSpin as (T.splitIndex u z) σ).2)^2) 0≤d^2:=by
      rw [native_small_cut_old_error_eq_original_profile]
      change nativeWholeLawErrorSecond n as law (cutLowError n U b h K) (T.splitIndex u z)≤d^2
      rw [nativeWholeLawErrorSecond_eq_radius_sq n ho law]
      apply pow_le_pow_left₀ (nativeWholeLawErrorRadius_nonneg _ _ _ _ _) _ 2
      have H:=actual_minimum_current_low_error_radius_le_original_fixed M hcl hAz Temp hTemp hb hh hxs
        ho U hl ht (T.splitIndex u z) (T.splitIndex_le_clockLength u z)
      rw [ite_eq_left (huz.trans_le hVU)] at H
      exact H
    have HE e : (ClockTree.pairClock as (T.splitIndex (s e) (w e))).disorderExpect
        (fullWeight n) (fullFeature n) 0 law
        (fun σ=>|nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))
          (T.splitIndex (s e) (w e)) (ClockTree.pairSpin as (T.splitIndex (s e) (w e)) σ).1
          (ClockTree.pairSpin as (T.splitIndex (s e) (w e)) σ).2|^(4*(aRows+1))) 0≤(r e)^(4*(aRows+1)):=by
      cases hsite : site e
      · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
        simp only [hsite,Bool.false_eq_true,ite_false]
        rw [native_small_cut_moving_kernel_eq_original_profile]
        simpa only [←Nat.mul_assoc,law,q,b,h,S,K,as] using
          hgridR U l t (v e) hl ht (hv e) (T.splitIndex (s e) (w e)) (T.splitIndex_le_clockLength _ _)
      · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
        simp only [hsite,ite_true,native_small_cut_site_row_abs_one,one_pow]
        exact le_of_eq (ClockTree.disorderExpect_one (fullWeight_pos n) (fullFeature n) _ ho 0 law 0)
    have H:=ClockTree.native_initial_observed_error_product_abs_le (fullWeight_pos n) (fullFeature n) T ho
      0 law 0 (G.canonicalMinimumSource M forms).product HC Hd HPmoment
      (nativeRestRowKernel n (nativeSmallCutOldErrorRestKernel n U b h K)) u z Hne Herror
      (fun e=>nativeRestRowKernel n (nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e))) s w hne
      r (fun e=>native_small_cut_ordinary_scale_pos M.hxs hCr ho (site e) _) HE
    change |T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (nativeOldInitialRowProduct n T (G.canonicalMinimumSource M forms).restProduct
        (nativeSmallCutOldErrorRestKernel n U b h K) u z
        (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (v e)) s w) 0|≤C*d*(∏e,r e)
    unfold nativeOldInitialRowProduct
    simp_rw [(G.canonicalMinimumSource M forms).product_eq_restProduct] at H
    exact H
  · intro hupper
    exact hgridS U V T l t hU hV0 hVU hcut hl ht hT G forms initial W hxW hmass
      u z huz site v s w hv hupper hne

end OAI.SKFluctuations.Cavity
