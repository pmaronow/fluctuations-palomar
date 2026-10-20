module

public import ComparisonSignedCavitySecondLowInheritedInitialRawAtomBudget
public import ComparisonSignedCavitySecondLowInheritedInitialWordBudget
public import ComparisonSignedCavitySecondLowInheritedUnobservedInitialEntryBudget
public import ComparisonSignedCavitySecondLowInheritedOldCBaselineAtomBudget
public import ComparisonActualHighOnlyInitialLowModulusSourceAlong
public import ComparisonActualHighOnlyOriginalTargetB0

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
theorem eventually_actual_minimum_inherited_second_low_actual_initial_raw_atom_budget_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
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
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(u z : T.Slot),T.splitIndex u z<V →
        ∀(s0 w0 s1 w1 : T.Slot) (vOrd : ℝ),
          T.splitIndex s0 w0<V → s0≠w0 → s1≠w1 → vOrd∈Icc (0:ℝ) 1 →
          let p0:=sourceMonomialScale x W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (nativeOldInitialRowProduct n T (G.canonicalHighOnlySource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![vOrd,0] i))
              ![s0,s1] ![w0,w1]) 0|≤C*M.xs*d*p0 := by
  obtain ⟨Cp,Cr,CpS,CrS,Cq,hCp,hCr,hCpS,hCrS,hCq,HD⟩:=
    eventually_actual_minimum_inherited_initial_atom_dichotomy_high_only (D:=D)
      aDegree 2 rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let A:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree
  let Sraw:=Cr*(1+Ccut)
  let C:=A*Sraw
  have hA : 0<A:=by dsimp [A];positivity
  have hSraw : 0<Sraw:=mul_pos hCr (by linarith)
  refine ⟨C,mul_pos hA hSraw,?_⟩
  filter_upwards [HD] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hmass
    u z huz s0 w0 s1 w1 vOrd hsmall hne0 hne1 hvOrd
  let as:=finiteCutMasses us jGrid
  let p0:=sourceMonomialScale x W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex u z)+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hv : ∀i : Fin 2, (![vOrd,0] i)∈Icc (0:ℝ) 1:=by
    intro i
    fin_cases i
    · change vOrd∈Icc (0:ℝ) 1
      exact hvOrd
    · change (0:ℝ)∈Icc (0:ℝ) 1
      exact ⟨le_rfl,zero_le_one⟩
  have hne : ∀i : Fin 2, (![s0,s1] i)≠(![w0,w1] i):=by
    intro i
    fin_cases i
    · change s0≠w0
      exact hne0
    · change s1≠w1
      exact hne1
  have HH:=hgrid U V T l t hU hV0 hVU hcut hl ht hT G forms initial x W hxsx hxW hmass
    u z huz (![false,true]) (![vOrd,0]) (![s0,s1]) (![w0,w1]) hv hne
  have HR:=HH.1
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    nativeSmallCutOrdinaryScale,Bool.false_eq_true,ite_false,ite_true,mul_one] at HR
  have Hmass:partitionPoint 0 as (T.splitIndex s0 w0)≤Ccut*M.xs:=
    (partitionPoint_mono as ho hsmall.le).trans hcut
  have Hscale : M.xs+partitionPoint 0 as (T.splitIndex s0 w0)≤(1+Ccut)*M.xs:=by
    nlinarith only [Hmass]
  have Hrow : Cr*(M.xs+partitionPoint 0 as (T.splitIndex s0 w0))≤Sraw*M.xs:=
    (mul_le_mul_of_nonneg_left Hscale hCr.le).trans_eq (by dsimp [Sraw];ring)
  apply HR.trans
  change A*p0*d*(Cr*(M.xs+partitionPoint 0 as (T.splitIndex s0 w0)))≤C*M.xs*d*p0
  have H:=mul_le_mul_of_nonneg_left Hrow (mul_nonneg (mul_nonneg hA.le hp0) hd)
  convert H using 1
  dsimp [C]
  ring

theorem eventually_actual_minimum_inherited_second_low_actual_initial_word_budget_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
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
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as),
          U≤as.length → 0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(a z : T.Slot),T.splitIndex a z<U →
        ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
        ∀(r : MarkedPlacement p.tree),r∈p.tree.markedAttach 0 →
        ∀(s : MarkedPlacement r.tree),s∈r.tree.markedAttach 0 →
        ∀(t : MarkedPlacement s.tree),t∈s.tree.markedAttach 0 →
          r.tree.splitIndex (r.embed p.mark) r.mark<V →
          t.tree.splitIndex (t.embed s.mark) t.mark<V →
          let p0:=sourceMonomialScale x W initial
          |nativeSecondLowWordValue n q U b h K (G.canonicalHighOnlySource M forms).restProduct a z p r s t|≤
            C*M.xs*actualLowErrorComparisonConstant Mclock Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+
                nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+
                2/(n+1:ℕ))*p0 := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_second_low_actual_initial_raw_atom_budget_high_only
    (D:=D) aDegree (rBound+4) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V T hU hV0 hVU hcut hT G forms initial x W hxsx hxW hmass a z haz
    p hp r hr s hs t ht Hfirst Hsecond
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let Gfinal:=nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht
  let af:=t.embed (s.embed (r.embed (p.embed a)))
  let zf:=t.embed (s.embed (r.embed (p.embed z)))
  let f:=t.embed (s.embed (r.embed p.mark))
  let c:=t.embed (s.embed r.mark)
  let e:=t.embed s.mark
  let d:=t.mark
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hfinal : t.tree.leaves≤rBound+4:=
    (native_second_low_four_mark_leaves_le p hp r hr s hs t ht).trans (by omega)
  have hfinalmass : ∀i,Gfinal.sourceLowMass i≤Cmass*sourceFactorScale x W initial i:=by
    intro i
    rw [native_second_low_canonical_old_shape_source_mass]
    exact hmass i
  have Hfc : t.tree.splitIndex f c=r.tree.splitIndex (r.embed p.mark) r.mark:=by
    dsimp only [f,c]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
  have Hf : t.tree.splitIndex f c<V:=by rw [Hfc];exact Hfirst
  have He : t.tree.splitIndex e d<V:=Hsecond
  have Ha : t.tree.splitIndex af zf<U:=by
    dsimp only [af,zf]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2,
      (T.markedAttach_embed_preserves 0 p hp).2]
    exact haz
  have Hne (u v : t.tree.Slot) (H : t.tree.splitIndex u v<U) : u≠v:=by
    intro HH
    rw [HH,t.tree.splitIndex_self] at H
    omega
  have Hfn : f≠c:=Hne f c (Hf.trans_le hVU)
  have Hen : e≠d:=Hne e d (He.trans_le hVU)
  have Han : af≠zf:=Hne af zf Ha
  have hzero : (0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
  have hone : (1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
  have Bfirst:=hgrid U V t.tree 0 0 hU hV0 hVU hcut hzero hzero hfinal
    Gfinal forms initial x W hxsx hxW hfinalmass f c Hf e d af zf 1 He Hen Han hone
  have Bsecond:=hgrid U V t.tree 0 0 hU hV0 hVU hcut hzero hzero hfinal
    Gfinal forms initial x W hxsx hxW hfinalmass e d He f c af zf 0 Hf Hfn Han hzero
  have HP : (Gfinal.canonicalHighOnlySource M forms).restProduct=
      nativeSecondLowOldTest (G.canonicalHighOnlySource M forms).restProduct p r s t:=by
    funext τ
    exact native_second_low_canonical_old_shape_rest_product_high_only M G forms p hp r hr s hs t ht τ
  have Hword:=native_second_low_joint_word_eq_original_physical_payload n q U b h K T ho
    (G.canonicalHighOnlySource M forms).restProduct a z p r s hs t ht
  rw [←HP,native_second_low_physical_QQKK_expect_eq_two_initial_products] at Hword
  let val1:=t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
    (nativeOldInitialRowProduct n t.tree (Gfinal.canonicalHighOnlySource M forms).restProduct
      (nativeSmallCutOldErrorRestKernel n U b h K) f c
      (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![1,0] i))
      ![e,af] ![d,zf]) 0
  let val2:=t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
    (nativeOldInitialRowProduct n t.tree (Gfinal.canonicalHighOnlySource M forms).restProduct
      (nativeSmallCutOldErrorRestKernel n U b h K) e d
      (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![0,0] i))
      ![f,af] ![c,zf]) 0
  change nativeSecondLowWordValue n q U b h K (G.canonicalHighOnlySource M forms).restProduct a z p r s t=
    val1+val2 at Hword
  change |val1|≤C*M.xs*(actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex f c)+1/(n+1:ℕ)))*p0 at Bfirst
  change |val2|≤C*M.xs*(actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex e d)+1/(n+1:ℕ)))*p0 at Bsecond
  rw [Hfc] at Bfirst
  rw [Hword]
  apply (abs_add_le val1 val2).trans
  apply (add_le_add Bfirst Bsecond).trans_eq
  dsimp only [e,d,p0,Mclock]
  ring

theorem eventually_actual_minimum_inherited_second_low_unobserved_initial_entry_budget_high_only
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
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
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length),
           0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(a z : T.Slot),T.splitIndex a z<U →
        ∀(i : ℕ),i<V → ∀(j : Fin 8),
          let p0:=sourceMonomialScale x W initial
          let di:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeSecondLowInitialUnobservedClassLedger n q i U b h K T
            hU (G.canonicalHighOnlySource M forms).restProduct a z j/2|≤
            C*partitionPoint 0 as U*M.xs*di*p0 := by
  obtain ⟨Cword,hCword,HW⟩:=eventually_actual_minimum_inherited_second_low_actual_initial_word_budget_high_only
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Prow:ℝ:=4*(rBound+1)*(rBound+2)*(rBound+3)*(rBound+4)
  have hProw:0<Prow:=by dsimp [Prow];positivity
  refine ⟨Prow*Cword,mul_pos hProw hCword,?_⟩
  filter_upwards [HW] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V T hU hV0 hVU hcut hT G forms initial x W hxsx hxW hmass a z haz i hi j
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let di:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  let F:=nativeSecondLowInitialUnobservedWord n q i U b h K hU
    (G.canonicalHighOnlySource M forms).restProduct a z j
  let Bd:=2*Cword*M.xs*di*p0
  have hp0:0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le
  have hdi:0≤di:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hxspos:0<M.xs:=M.hxs
  have hBd:0≤Bd:=by dsimp [Bd];positivity
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HF:∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t|≤Bd:=by
    intro p hp r hr s hs t ht
    dsimp only [F,nativeSecondLowInitialUnobservedWord,nativeSecondLowUnobservedWord]
    split_ifs with Hindices _Hsource
    · have H:=hgrid U V T hU hV0 hVU hcut hT G forms initial x W hxsx hxW hmass a z haz
        p hp r hr s hs t ht (Hindices.1 ▸ hi) (Hindices.2 ▸ hi)
      rw [Hindices.1,Hindices.2] at H
      convert H using 1
      dsimp [Bd,di,p0]
      ring
    · simpa only [abs_zero] using hBd
    · simpa only [abs_zero] using hBd
  have Hentry:=native_second_low_entry_four_average_abs_le T U hU ho hT
    (nativeSecondLowFirstMiddleIsFirst j) F hBd HF
  rw [←native_second_low_initial_unobserved_class_eq_entry n q i U b h K T hU
    (G.canonicalHighOnlySource M forms).restProduct a z j] at Hentry
  have Hmass:0≤partitionPoint 0 as U:=(partitionPoint_mem as ho U).1
  have Hpoly:(4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))≤Prow:=by
    dsimp [Prow]
    gcongr <;> linarith
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _≤((4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*partitionPoint 0 as U*Bd)/2:=
      div_le_div_of_nonneg_right Hentry (by norm_num)
    _=(4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*Cword*
        partitionPoint 0 as U*M.xs*di*p0:=by dsimp [Bd];ring
    _≤Prow*Cword*partitionPoint 0 as U*M.xs*di*p0:=by
      gcongr
    _= _:=rfl

theorem eventually_actual_minimum_inherited_second_low_old_c_error_atom_budget_high_only
    (degree rBound : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualHighOnlySmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(f c z : T.Slot),T.splitIndex f c<U → T.splitIndex c z<U → f≠z → ∀firstError : Bool,
          let errorCut:=if firstError then T.splitIndex f c else T.splitIndex c z
          let otherCut:=if firstError then T.splitIndex c z else T.splitIndex f c
          let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as errorCut+1/(n+1:ℕ))
          |T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
            (nativeSecondLowOldCBaselineErrorAtom n U b h K T
              (G.canonicalHighOnlySource M forms).restProduct f c z firstError) 0|≤
            C*d*(M.xs+partitionPoint 0 as otherCut)*sourceMonomialScale x W initial := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_actual_raw_atom_budget_high_only
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs HS hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs HS hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial x W hxsx hxW hmass f c z Hfc Hcz Hfz firstError
  have Hfn:f≠c:=native_second_low_low_slots_ne T U hU f c Hfc
  have Hcn:c≠z:=native_second_low_low_slots_ne T U hU c z Hcz
  have hzero:(0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
  have hone:(1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
  cases firstError
  · exact hgrid U T 0 0 hU hzero hzero hT G forms initial x W hxsx hxW hmass c z Hcz
      f c f z 0 Hfc Hfn Hfz hzero
  · exact hgrid U T 0 0 hU hzero hzero hT G forms initial x W hxsx hxW hmass f c Hfc
      c z f z 1 Hcz Hcn Hfz hone

end OAI.SKFluctuations.Cavity
