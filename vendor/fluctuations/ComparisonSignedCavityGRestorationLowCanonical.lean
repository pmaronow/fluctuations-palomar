module

public import ComparisonSignedCavityGRestorationRawLow
public import ComparisonSignedCavityGRestorationLowMoments
public import ComparisonSignedCavityCanonicalContinuumMoments
public import ComparisonSignedCavityMixedErrorCanonicalLedger

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_bare_canonical_G_low_restoration
    (aDegree rBound : ℕ) (ha : 0 < aDegree)
    (Bclock Temp Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l : ℝ),
          U ≤ as.length → l∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a c e f : T.Slot,e≠f →
          let law:=cutFullVariance n q U l 1 b h K
          let high:=cutTSlope n U 0 b h K
          |cutLowJet n q U b h K T (fun σ=>(G.canonicalMinimumSource M forms).product σ*
            nativeOriginalHighGAtom T U K b S a c e f σ) 0 1 l 1| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                  sourceMonomialScale M.xs W initial)*
                nativeWholeLawErrorRadius n as law high (T.splitIndex e f)*(Cq*W)) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_bare_canonical_continuum_square_even_moment
    (D:=D) aDegree 2 rBound ha (by norm_num) Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_bare_original_low_profile_fourth
    (D:=D) Bclock Temp Ccut hTemp hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs L us hus hret hmesh,
    hnQ M hb hh hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l hU hl hT G forms initial W hxW hcut hmass a c e f hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l 1 b h K
  let high:=cutTSlope n U 0 b h K
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*
    (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp))*Cp^aDegree*
      sourceMonomialScale M.xs W initial
  let P:=(G.canonicalMinimumSource M forms).product
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0 ≤ C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial i).le)
  have Hraw:=hgrid U T l 1 hl (by norm_num) hT G forms initial W hxW hmass
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^4) 0 ≤ C^4:=Hraw
  have HQmoment:=hgridQ U l 1 1 W hU hl (by norm_num) (by norm_num) hxW hcut
  have H:=native_original_G_raw_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law P a c e f hef (cutLSlope n U 1 b h K) HC
    (mul_pos hCq (M.hxs.trans_le hxW)) HPmoment HQmoment
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
  simpa only [List.replicate_one] using H

end OAI.SKFluctuations.Cavity
