module

public import ComparisonSignedCavityInitialActualWordModulusBudget
public import ComparisonSignedCavityInitialActualPlainWordModulusBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000

theorem native_initial_word_sum_abs_le
    {S : Type} {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (k rBound : ℕ) (hT : T.leaves≤rBound)
    (F : NativeInitialInsertionWord T k→ℝ) {B : ℝ} (hB : 0≤B)
    (hF : ∀g,|g.coefficient*F g|≤|g.coefficient| *B) :
    |((nativeInitialInsertionWords T k).map (fun g=>g.coefficient*F g)).sum|≤
      absJetVariation rBound k*B := by
  have Habs : ∀L : List (NativeInitialInsertionWord T k),
      |(L.map (fun g=>g.coefficient*F g)).sum|≤
        (L.map (fun g=>|g.coefficient*F g|)).sum := by
    intro L
    induction L with
    | nil=>simp
    | cons g L ih=>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)
  apply (Habs _).trans
  apply (List.sum_le_sum (fun g _=>hF g)).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right (native_initial_insertion_word_variation T ho k rBound hT) hB

 theorem eventually_actual_minimum_bare_initial_jet_modulus_budget
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
        ∀(U V i star : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,a≠z → V≤T.splitIndex a z →
          let p0:=sourceMonomialScale M.xs W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (fun σ=>(G.canonicalMinimumSource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2) 0 .initial k l t|≤
            absJetVariation rBound (k+1)*(C*M.xs*d*p0*W^(k-1)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_bare_initial_word_modulus_budget
    (D:=D) aDegree k rBound Bclock Temp Cmass Ccut Couter hTemp hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial W hxW hW1 houter hmass a z haz htarget
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let P:=(fun σ=>(G.canonicalMinimumSource M forms).product σ*sitePair T a z (T.cavityAssignment σ).2)
  let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let p0:=sourceMonomialScale M.xs W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
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
  have hW : 0<W:=M.hxs.trans_le hxW
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hB : 0≤C*M.xs*d*p0*W^(k-1):=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le M.hxs.le) hd) hp0) (pow_nonneg hW.le _)
  rw [native_initial_LOW_jet_eq_terminal_word_sum n q i star U k b h K T ho
    (fun j z=>by cases z <;> exact NNReal.coe_nonneg _)
    (fun z=>by cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm P 0 hl ht]
  apply native_initial_word_sum_abs_le T ho (k+1) rBound hT _ hB
  intro g
  exact hgrid U V i T l t hU hV0 hVU hiV hcut hl ht hT G forms initial W hxW hW1 houter hmass a z haz htarget g

 theorem eventually_actual_minimum_bare_initial_plain_jet_modulus_budget
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
        ∀(U V i star : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          U≤as.length → 0 < V → V≤U → i < V → partitionPoint 0 as V≤Ccut*M.xs →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs≤W → W≤1 → partitionPoint 0 as U≤Couter*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
          let p0:=sourceMonomialScale M.xs W initial
          let d:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeTransientLowErrorPartJet n q i star U b h K T
            (G.canonicalMinimumSource M forms).product 0 .initial k l t|≤
            absJetVariation rBound (k+1)*(C*M.xs*d*p0*W^(k-1)) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_bare_initial_plain_word_modulus_budget
    (D:=D) aDegree k rBound Bclock Temp Cmass Ccut Couter hTemp hCmass hCcut hCouter
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V i star T l t hU hV0 hVU hiV hcut hl ht hT G forms initial W hxW hW1 houter hmass
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let P:=(G.canonicalMinimumSource M forms).product
  let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
  let p0:=sourceMonomialScale M.xs W initial
  let d:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
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
  have hW : 0<W:=M.hxs.trans_le hxW
  have hp0 : 0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs hW initial e).le
  have hd : 0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hB : 0≤C*M.xs*d*p0*W^(k-1):=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le M.hxs.le) hd) hp0) (pow_nonneg hW.le _)
  rw [native_initial_LOW_jet_eq_terminal_word_sum n q i star U k b h K T ho
    (fun j z=>by cases z <;> exact NNReal.coe_nonneg _)
    (fun z=>by cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm P 0 hl ht]
  apply native_initial_word_sum_abs_le T ho (k+1) rBound hT _ hB
  intro g
  exact hgrid U V i T l t hU hV0 hVU hiV hcut hl ht hT G forms initial W hxW hW1 houter hmass g

end OAI.SKFluctuations.Cavity
