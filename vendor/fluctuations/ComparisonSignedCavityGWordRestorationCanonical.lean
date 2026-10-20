module

public import ComparisonSignedCavityGRestorationWords
public import ComparisonSignedCavityGRestorationHighCanonical
public import ComparisonSignedCavityGRestorationLowCanonical

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_bare_canonical_G_word_high_restoration
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
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
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          U ≤ as.length → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),g.z.embed g.r.mark≠g.z.mark →
          let law:=cutFullVariance n q U 0 t b h K
          let high:=cutTSlope n U 0 b h K
          |cutMixedJet n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalMinimumSource M forms).product a) 0 0 0 t| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
              (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
              (g.z.embed g.r.mark) g.z.mark| *
              (ClockTree.pairForkVariation (rBound+3)*
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cp^aDegree*
                  sourceMonomialScale M.xs W initial)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law high (g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark))^(2/p)*
                nativeWholeLawProfileCost n law high g.tree (2/p)) := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_bare_canonical_G_high_restoration
    (D:=D) aDegree dOrder (rBound+3) ha hd p hp hOrder Bclock Temp Cmass hTemp hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T t hU ht hT G forms initial W hxW hmass g a hef
  have hTg : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
  have hmassg (e : Fin aDegree) : (g.canonicalOldShape G).sourceLowMass e ≤
      Cmass*sourceFactorScale M.xs W initial e:=by
    rw [g.canonicalOldShape_sourceLowMass G e]
    exact hmass e
  have HB:=hgrid U g.tree t hU ht hTg (g.canonicalOldShape G) forms initial W hxW hmassg
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark hef
  rw [←g.originalRestorationTest_canonical G M forms] at HB
  exact HB

theorem eventually_actual_minimum_bare_canonical_G_word_low_restoration
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
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),g.z.embed g.r.mark≠g.z.mark →
          let law:=cutFullVariance n q U l 1 b h K
          let high:=cutTSlope n U 0 b h K
          |cutLowJet n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalMinimumSource M forms).product a) 0 1 l 1| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
              (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
              (g.z.embed g.r.mark) g.z.mark| *
              (ClockTree.absJetVariation (rBound+3) 1*
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cp^aDegree*
                  sourceMonomialScale M.xs W initial)*
                nativeWholeLawErrorRadius n as law high (g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark)*(Cq*W)) := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_minimum_bare_canonical_G_low_restoration
    (D:=D) aDegree (rBound+3) ha Bclock Temp Cmass Ccut hTemp hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l hU hl hT G forms initial W hxW hcut hmass g a hef
  have hTg : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
  have hmassg (e : Fin aDegree) : (g.canonicalOldShape G).sourceLowMass e ≤
      Cmass*sourceFactorScale M.xs W initial e:=by
    rw [g.canonicalOldShape_sourceLowMass G e]
    exact hmass e
  have HB:=hgrid U g.tree l hU hl hTg (g.canonicalOldShape G) forms initial W hxW hcut hmassg
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark hef
  rw [←g.originalRestorationTest_canonical G M forms] at HB
  exact HB

end OAI.SKFluctuations.Cavity
