module

public import ComparisonSignedCavityGRestorationWords
public import ComparisonActualHighWallGRestorationHighCanonical
public import ComparisonActualHighWallGRestorationLowCanonical

public import ComparisonSignedCavityGWordRestorationCanonical
public import ComparisonActualGeneralMarkedSourceTransport

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_G_word_high_restoration
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          U ≤ as.length → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),g.z.embed g.r.mark≠g.z.mark →
          let law:=cutFullVariance n q U 0 t b h K
          let high:=cutTSlope n U 0 b h K
          |cutMixedJet n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalHighWallSource M forms).product a) 0 0 0 t| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
              (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
              (g.z.embed g.r.mark) g.z.mark| *
              (ClockTree.pairForkVariation (rBound+3)*
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cp^aDegree*
                  M.data.d^aDegree)*(2*M.data.T)^((p-2)/p)*(2*M.data.T)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law high (g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark))^(2/p)*
                nativeWholeLawProfileCost n law high g.tree (2/p)) := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_high_wall_canonical_G_high_restoration
    (D:=D) aDegree dOrder (rBound+3) hd p hp hOrder Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T t hU ht hT G forms hmass g a hef
  have hTg : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
  have hmassg (e : Fin aDegree) : (g.canonicalOldShape G).sourceLowMass e ≤
      Cmass*M.data.d:=by
    rw [g.canonicalOldShape_sourceLowMass G e]
    exact hmass e
  have HB:=hgrid U g.tree t hU ht hTg (g.canonicalOldShape G) forms hmassg
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark hef
  rw [←g.originalRestorationTest_physical G M.bf M.hf forms] at HB
  exact HB

theorem eventually_actual_high_wall_canonical_G_word_low_restoration
    (aDegree rBound : ℕ)
    (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l : ℝ),
          U ≤ as.length → l∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm),
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),g.z.embed g.r.mark≠g.z.mark →
          let law:=cutFullVariance n q U l 1 b h K
          let high:=cutTSlope n U 0 b h K
          |cutLowJet n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalHighWallSource M forms).product a) 0 1 l 1| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
              (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
              (g.z.embed g.r.mark) g.z.mark| *
              (ClockTree.absJetVariation (rBound+3) 1*
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cp^aDegree*
                  M.data.d^aDegree)*
                nativeWholeLawErrorRadius n as law high (g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark)*(Cq*M.data.d)) := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_high_wall_canonical_G_low_restoration
    (D:=D) aDegree (rBound+3) Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l hU hl hT G forms hcut hmass g a hef
  have hTg : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
  have hmassg (e : Fin aDegree) : (g.canonicalOldShape G).sourceLowMass e ≤
      Cmass*M.data.d:=by
    rw [g.canonicalOldShape_sourceLowMass G e]
    exact hmass e
  have HB:=hgrid U g.tree l hU hl hTg (g.canonicalOldShape G) forms hcut hmassg
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark hef
  rw [←g.originalRestorationTest_physical G M.bf M.hf forms] at HB
  exact HB

end OAI.SKFluctuations.Cavity
