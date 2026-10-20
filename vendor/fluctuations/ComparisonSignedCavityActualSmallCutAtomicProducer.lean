module

public import ComparisonSignedCavitySmallCutAtomicKernels

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_bare_small_cut_old_initial_atom
    (aDegree aRows rBound : ℕ) (Bclock Temp Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp Cr Cq : ℝ,0<Cp ∧ 0<Cr ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
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
          (∀i,v i∈Icc (0:ℝ) 1) → (∀i,V≤T.splitIndex (s i) (w i)) → (∀i,s i≠w i) →
          let p0:=sourceMonomialScale M.xs W initial
          let C:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*p0
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          let r:=fun i=>nativeSmallCutOrdinaryScale M.xs Cr as (site i) (T.splitIndex (s i) (w i))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalMinimumSource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w) 0|≤
            ClockTree.absJetVariation T.leaves 1*
              (Real.exp (ClockTree.jetVariation T.leaves 1*Mclock)*C)*(ep*d)*
              (∏i,ep*r i)*(ep*(Cq*(1+Ccut)*M.xs)) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_continuum_even_all_degree
    (D:=D) aDegree 2 rBound (by norm_num) Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_bare_continuum_low_profile_moment
    (D:=D) (2*(aRows+1)) (by omega) Bclock Temp hTemp
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_bare_small_cut_low_moment
    (D:=D) (2*(aRows+1)) (by omega) Bclock Temp Ccut hTemp hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr,Cq,hCp,hCr,hCq,?_⟩
  filter_upwards [HP,HR,HQ] with n hnP hnR hnQ
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs L us hus hret hmesh,
    hnR M hb hh hxs L us hus hret hmesh,
    hnQ M hb hh hxs L us hus hret hmesh] with jGrid hgridP hgridR hgridQ
  dsimp only at hgridP hgridR hgridQ ⊢
  intro U V T l t hU hV0 hVU hcut hl ht hT G forms initial W hxW hmass u z huz
    site v s w hv hsw hne
  let as:=finiteCutMasses us jGrid
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
  let r:=fun i=>nativeSmallCutOrdinaryScale M.xs Cr as (site i) (T.splitIndex (s i) (w i))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hV : V≤as.length:=hVU.trans hU
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ)≤M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ)≤M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hCf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg (D:=D) hcl hAz
  have HM : 0≤Mclock:=by dsimp [Mclock];positivity
  have Hb j : b j≤Temp:=(M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho j)).2.1
  have Hh j : h j≤2*NativeOverlapMinimum.bareSourceClockConstant cl Az D := by
    have Hsource:=M.bare_source_clock_bounds hcl hAz Temp hb hh (partitionPoint_mem as ho j)
    have HH:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as j≤2 by linarith [(partitionPoint_mem as ho j).2]) hCf
    exact Hsource.2.2.2.trans (by linarith only [HH])
  have Hclock j : |K j|+|h j|+|b j|≤Mclock := by
    rw [abs_of_nonneg (hK0 j),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _)]
    have HK:=mul_le_mul_of_nonneg_left (HS j).2 (NNReal.coe_nonneg (M.bf (partitionPoint 0 as j)))
    dsimp only [K,Mclock]
    linarith [Hh j,Hb j]
  have HC : 0≤C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le)
  have Hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hnewpos : 0<Cq*(1+Ccut)*M.xs:=mul_pos (mul_pos hCq (by linarith)) M.hxs
  apply native_old_initial_row_product_abs_le_original_moments n q U V hV0 b h K T ho hV
    (G.canonicalMinimumSource M forms).restProduct (nativeSmallCutOldErrorRestKernel n U b h K) u z huz
    (fun i=>nativeSmallCutOrdinaryRestKernel n U b h K (site i) (v i)) s w hsw hne 0
    (by intro i;rfl) (by intro i;rfl)
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
    HM HC Hd Hnewpos (fun j _=>Hclock j) r
    (fun i=>native_small_cut_ordinary_scale_pos M.hxs hCr ho (site i) _ ) hl ht
  · have H:=hgridP U T l t hl ht hT G forms initial W hxW hmass
    simp_rw [(G.canonicalMinimumSource M forms).product_eq_restProduct] at H
    simpa only [Nat.mul_succ,Nat.mul_zero,Nat.add_zero,C,Mclock,law,q,b,h,S,K,as] using H
  · rw [native_small_cut_old_error_eq_original_profile]
    change nativeWholeLawErrorSecond n as law (cutLowError n U b h K) (T.splitIndex u z)≤d^2
    rw [nativeWholeLawErrorSecond_eq_radius_sq n ho law]
    apply pow_le_pow_left₀ (nativeWholeLawErrorRadius_nonneg _ _ _ _ _) _ 2
    have H:=native_actual_low_error_radius_le_original (M:=Mclock) n U M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) ho hl ht hTemp
      (fun j _=>Hb j) (by
        have HH:=Hclock as.length
        rw [abs_of_nonneg (hK0 _),abs_of_nonneg (NNReal.coe_nonneg _),abs_of_nonneg (NNReal.coe_nonneg _)] at HH
        dsimp only [K,b,h,S] at HH
        linarith only [HH]) (T.splitIndex u z) (T.splitIndex_le_clockLength u z)
    rw [ite_eq_left (huz.trans_le hVU)] at H
    exact H
  · intro i
    cases hsite : site i
    · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
      simp only [hsite,Bool.false_eq_true,ite_false]
      rw [native_small_cut_moving_kernel_eq_original_profile]
      simpa only [←Nat.mul_assoc,law,q,b,h,S,K,as] using
        hgridR U l t (v i) hl ht (hv i) (T.splitIndex (s i) (w i)) (T.splitIndex_le_clockLength _ _)
    · dsimp only [nativeSmallCutOrdinaryRestKernel,nativeSmallCutOrdinaryScale,r]
      simp only [hsite,ite_true,native_small_cut_site_row_abs_one,one_pow]
      exact le_of_eq (ClockTree.disorderExpect_one (fullWeight_pos n) (fullFeature n) _ ho 0 law 0)
  · intro j
    by_cases hj : j≤as.length
    · simpa only [←Nat.mul_assoc,q,b,h,S,K,as] using hgridQ U V hVU hcut l t t hl ht ht j hj
    · have hjV : ¬j<V:=by omega
      simp only [ReplicaTree.coordinateProfile,cutLSlope,hjV,ite_false,Pi.zero_apply,zero_mul,
        Finset.sum_const_zero,abs_zero,zero_pow (by omega : 4*(aRows+1)≠0),
        ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg Hnewpos.le _

end OAI.SKFluctuations.Cavity
