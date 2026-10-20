module

public import ComparisonSignedCavityInitialInsertionWordJetLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000

 theorem eventually_actual_minimum_bare_initial_word_modulus_budget
    (aDegree k rBound : ℕ) (Bclock Temp Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U V i : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,a≠z → V≤T.splitIndex a z →
        ∀g : NativeInitialInsertionWord T (k+1),
          let p0:=sourceMonomialScale M.xs W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |g.coefficient*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (g.test (nativeInitialTerminalLowDirections n U i k b h K t)
              (fun σ=>(G.canonicalMinimumSource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2)) 0|≤
            |g.coefficient| *(C*M.xs*d*p0*W^(k-1)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_bare_initial_atom_modulus_budget
    (D:=D) aDegree (k+1) (rBound+2*(k+1)) Bclock Temp Cmass Ccut Couter hTemp hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V i T l t hU hV0 hVU hiV hcut hl ht hT G forms initial W hxW hW1 houter hmass a z haz htarget g
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let P:=fun σ=>(G.canonicalMinimumSource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2
  let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let p0:=sourceMonomialScale M.xs W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  let B:=C*M.xs*d*p0*W^(k-1)
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hB : 0≤B:=by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le M.hxs.le) hd) hp0) (pow_nonneg hW.le _)
  change |g.coefficient*g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 law
    (g.test (nativeInitialTerminalLowDirections n U i k b h K t) P) 0|≤|g.coefficient| *B
  by_cases hcoef : g.coefficient=0
  · simp only [hcoef,zero_mul,abs_zero]
    exact le_rfl
  by_cases Hsplit : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2=i
  · by_cases Hlow : ∀e : Fin k,g.tree.splitIndex (g.pairSlots e.castSucc).1 (g.pairSlots e.castSucc).2 < U
    · have Hleaf : g.tree.leaves≤rBound+2*(k+1):=(g.leaves_le).trans (Nat.add_le_add_right hT _)
      let Gn:=g.canonicalShape G
      let site : Fin (k+1)→Bool:=Fin.cases true (fun _=>false)
      let vn : Fin (k+1)→ℝ:=Fin.cases 0 (fun _=>t)
      let sn : Fin (k+1)→ g.tree.Slot:=Fin.cases (g.embed a) (fun e=> (g.pairSlots e.castSucc).1)
      let tn : Fin (k+1)→ g.tree.Slot:=Fin.cases (g.embed z) (fun e=> (g.pairSlots e.castSucc).2)
      have Hmass e : Gn.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e:=by
        rw [NativeInitialInsertionWord.canonicalShape_sourceLowMass]
        exact hmass e
      have HV : ∀e,vn e∈Icc (0:ℝ) 1:=fun e=>Fin.cases (by dsimp [vn];simp) (fun _=>ht) e
      have Hne : ∀e,sn e≠tn e:=fun e=>Fin.cases
        (fun H=>haz (g.embed_preserves.1 H))
        (fun e=>g.pair_distinct_of_coefficient_ne_zero hcoef e.castSucc) e
      have Hsiteupper : ∀e,site e=true→V≤g.tree.splitIndex (sn e) (tn e):=by
        intro e
        refine Fin.cases ?_ (fun e=>?_) e
        · intro _
          dsimp only [sn,tn,Fin.cases_zero]
          rw [g.embed_preserves.2]
          exact htarget
        · intro H
          dsimp only [site,Fin.cases_succ] at H
          contradiction
      have Hrowlow : ∀e,site e=false→ g.tree.splitIndex (sn e) (tn e) < U:=by
        intro e
        refine Fin.cases ?_ (fun e=>?_) e
        · intro H
          dsimp only [site,Fin.cases_zero] at H
          contradiction
        · intro _
          exact Hlow e
      have Hnorm:=hgrid U V g.tree l t hU hV0 hVU hcut hl ht Hleaf Gn forms initial W hxW hW1 houter Hmass
        (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2 (Hsplit.trans_lt hiV)
        site vn sn tn HV Hne Hsiteupper Hrowlow
      rw [Hsplit] at Hnorm
      have Hcount : (nativeInitialOrdinaryRowSet site).card=k:=native_initial_terminal_site_count k
      rw [Hcount] at Hnorm
      have Htest : g.test (nativeInitialTerminalLowDirections n U i k b h K t) P=
          nativeOldInitialRowProduct n g.tree (Gn.canonicalMinimumSource M forms).restProduct
            (nativeSmallCutOldErrorRestKernel n U b h K)
            (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2
            (fun e=>nativeSmallCutOrdinaryRestKernel n U b h K (site e) (vn e)) sn tn:=by
        funext σ
        exact native_initial_terminal_word_test_eq_physical_atom n U i k b h K t T g G M forms a z Hsplit σ
      rw [Htest,abs_mul]
      exact mul_le_mul_of_nonneg_left Hnorm (abs_nonneg _)
    · obtain ⟨e,he⟩:=not_forall.mp Hlow
      rw [native_initial_terminal_word_zero_high n U i k b h K t T g P e (not_lt.mp he)]
      simp only [disorderExpect,mul_zero,Finset.sum_const_zero,abs_zero]
      exact mul_nonneg (abs_nonneg _) hB
  · rw [native_initial_terminal_word_zero_error n U i k b h K t T g P Hsplit]
    simp only [disorderExpect,mul_zero,Finset.sum_const_zero,abs_zero]
    exact mul_nonneg (abs_nonneg _) hB

end OAI.SKFluctuations.Cavity
