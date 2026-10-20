module

public import ComparisonSignedCavityInitialInheritedAtomDichotomy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_minimum_inherited_second_low_actual_initial_raw_atom_budget
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
            (nativeOldInitialRowProduct n T (G.canonicalMinimumSource M forms).restProduct
              (nativeSmallCutOldErrorRestKernel n U b h K) u z
              (fun i : Fin 2=>nativeSmallCutOrdinaryRestKernel n U b h K (![false,true] i) (![vOrd,0] i))
              ![s0,s1] ![w0,w1]) 0|≤C*M.xs*d*p0 := by
  obtain ⟨Cp,Cr,CpS,CrS,Cq,hCp,hCr,hCpS,hCrS,hCq,HD⟩:=
    eventually_actual_minimum_inherited_initial_atom_dichotomy (D:=D)
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
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
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

end OAI.SKFluctuations.Cavity
