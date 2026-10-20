module

public import ComparisonActualHighWallSecondLowFreshCenteredInitialAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 60000000

theorem eventually_actual_high_wall_second_low_fresh_centered_initial_nonempty_modulus_price_along
    (degree rBound : ℕ) (hdegree : 0 < degree) (Bclock Cmass Ccut Rmacro F Cx : ℝ)
    {eta : ℝ} (hCx : 0 < Cx) (heta : 0 < eta)
    (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C CiU CiB CiM : ℝ,0 < C ∧ 0 < CiU ∧ 0 < CiB ∧ 0 < CiM ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass) (_hus : ∀u∈us,u.val ≤ 1),
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let W:=M.data.d
        ∀(pre mid tail : List PositiveMass) (_hparts : as=pre++(mid++tail))
          (T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape (dim n) (degree) T)
          (forms : Fin (degree)→NativeSourceFactorForm) (initial : Finset (Fin (degree)))
          (s : T.Slot) (U : ℕ) (_hU : U ≤ (pre++(mid++tail)).length)
          (x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),
          0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T → T.leaves ≤ rBound →
          partitionPoint 0 as U ≤ Ccut*M.data.d →
          M.xs ≤ x → x ≤ W → W ≤ Rmacro/2 →
          (∀e,T.splitIndex (G.i e) (G.j e) < U) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          ∀(e0 : Fin (degree)) (initialCut : ℕ),forms e0=.centered →
            T.splitIndex (G.i e0) (G.j e0)=initialCut →
          partitionPoint 0 as pre.length ≤ Cmass*W →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          4*W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U) →
          M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          (∀e,M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)) →
          M.data.wallRadius M.alpha (partitionPoint 0 as pre.length) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) →
          Cx*M.xs ≤ sourceMass → NativeDyadicRetainedReadout sourceMass hsourceMass (pre++(mid++tail)) U →
        |nativeSecondLowFreshFullB0Source (dim n) q U b h K T s
          (pre.length+mid.length) (nativeOriginalCenteredRestTest (dim n) q U b h K T
            (G.canonicalHighWallSource M forms).restProduct)| ≤
          C*M.data.d^3*sourceMonomialScale x W initial*(
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as initialCut) (CiU*M.data.d) 8+
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as initialCut) (CiB*M.data.d) 8+
            originalInitialLowMomentModulus
              (originalHighWallInitialPairErrorScale M as initialCut) (CiM*M.data.d) 4+
            (dim n:ℝ)^(-eta)) := by
  cases degree with
  | zero => omega
  | succ a =>
    simpa only [Nat.succ_eq_add_one] using
      (eventually_actual_high_wall_second_low_fresh_centered_initial_modulus_price_along
        (D:=D) a rBound Bclock Cmass Ccut Rmacro F Cx hCx heta hCm hCcut
        hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim)

end OAI.SKFluctuations.Cavity
