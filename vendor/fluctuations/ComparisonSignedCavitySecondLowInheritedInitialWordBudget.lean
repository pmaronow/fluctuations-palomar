module

public import ComparisonSignedCavitySecondLowInheritedInitialRawAtomBudget
public import ComparisonSignedCavitySecondLowOriginalCanonicalTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000

theorem eventually_actual_minimum_inherited_second_low_actual_initial_word_budget
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
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
          |nativeSecondLowWordValue n q U b h K (G.canonicalMinimumSource M forms).restProduct a z p r s t|≤
            C*M.xs*actualLowErrorComparisonConstant Mclock Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+
                nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+
                2/(n+1:ℕ))*p0 := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_second_low_actual_initial_raw_atom_budget
    (D:=D) aDegree (rBound+4) Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
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
  have HP : (Gfinal.canonicalMinimumSource M forms).restProduct=
      nativeSecondLowOldTest (G.canonicalMinimumSource M forms).restProduct p r s t:=by
    funext τ
    exact native_second_low_canonical_old_shape_rest_product M G forms p hp r hr s hs t ht τ
  have Hword:=native_second_low_joint_word_eq_original_physical_payload n q U b h K T ho
    (G.canonicalMinimumSource M forms).restProduct a z p r s hs t ht
  rw [←HP,native_second_low_physical_QQKK_expect_eq_two_initial_products] at Hword
  let val1:=t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
    (nativeOldInitialRowProduct n t.tree (Gfinal.canonicalMinimumSource M forms).restProduct
      (nativeSmallCutOldErrorRestKernel n U b h K) f c
      (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![1,0] i))
      ![e,af] ![d,zf]) 0
  let val2:=t.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 0 0 b h K)
    (nativeOldInitialRowProduct n t.tree (Gfinal.canonicalMinimumSource M forms).restProduct
      (nativeSmallCutOldErrorRestKernel n U b h K) e d
      (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![0,0] i))
      ![f,af] ![c,zf]) 0
  change nativeSecondLowWordValue n q U b h K (G.canonicalMinimumSource M forms).restProduct a z p r s t=
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

end OAI.SKFluctuations.Cavity
