module

public import ComparisonSignedCavityActualConstantForwardMean

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000

def nativeActualJointRestoredForwardTaylorError (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) : ℝ :=
  nativeActualHigherAllocatedRemainder n q U b h K T P a z-
    nativeCenteredLowGammaHighSecondRemainder n q U b h K S T P a z-
    nativeCenteredLowGammaLowRestoration n q U b h K S T P a z-
    nativeOriginalGKernelLowRestoration n q U b h K S T P a z
      (restCenteredLowKernel n U b S)

theorem native_original_forward_longitudinal_joint_restoration (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (hU : U≤as.length)
    (hq0 : ∀j i,0≤q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0≤b j) (hh : ∀j,0≤h j) (hK : ∀j,0≤K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    chi*K (T.splitIndex a z)*
      (nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
        (fun σ=>P (T.cavityAssignment σ).1) a+
       nativeOriginalLongitudinalPairing n 0 (cutFullVariance n q U 1 1 b h K) 0 U K b S T
        (fun σ=>P (T.cavityAssignment σ).1) z)+
      nativeActualOriginalForwardTaylorError n q U b h K S T P a z=
    chi*K (T.splitIndex a z)*
      (nativeRetainedLongitudinalPairing n q U b h K T P a+
       nativeRetainedLongitudinalPairing n q U b h K T P z)+
      nativeActualJointRestoredForwardTaylorError n q U b h K S T P a z := by
  dsimp only
  have HA:=native_original_longitudinal_eq_retained_add_restoration n q U b h K S hKS T ho P a hU
    hq0 hq hb hh hK hbm hhm hKm
  have HZ:=native_original_longitudinal_eq_retained_add_restoration n q U b h K S hKS T ho P z hU
    hq0 hq hb hh hK hbm hhm hKm
  unfold nativeActualOriginalForwardTaylorError nativeActualJointRestoredForwardTaylorError
  rw [HA,HZ]
  ring

theorem actual_original_constant_gap_eq_jointly_restored_star_responses
    (n : ℕ) (as : List PositiveMass) (star U : ℕ)
    (hs : star < U) (hU : U≤as.length) (ho : MassOrdered 0 as) (b h K S : ℕ→ℝ)
    (hKS : ∀j,K j=h j+b j*S j)
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s : T.Slot:=singleSlot as
    let g:=nativeFreshAtSlot T 0 s star
    let qfull:=cutFullVariance n q U 1 1 b h K
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-S star
    finitePhysicalMean (n+1) as b h star-nativeOriginalScalarPairMean as K star=
      chi*K star*
        (nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) (g.embed s)+
         nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) g.mark)+
      chi^2*b star*(finitePhysicalMean (n+1) as b h star-
        finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)+
      b star*(chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b S g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
        nativeOriginalFreshPartnerLResponse n 0 qfull 0 U K b S T s star
          (fun _ c d=>A c d))+
      nativeActualJointRestoredForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  let T:=ClockTree.single (S:=Spin n×Bool) as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let s : T.Slot:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  have hq0 : ∀j i,0≤q j i:=by
    intro j i
    cases i <;> simp only [q,Sum.elim_inl,Sum.elim_inr] <;> first | exact hb j | exact hh j
  have hq : ∀i,Monotone (fun j=>q j i):=by
    intro i
    cases i <;> first | exact hbm | exact hhm
  have HE:=actual_original_constant_gap_eq_single_star_responses n as star U hs hU ho b h K S
    hKS hb hh hK hbm hhm hKm
  dsimp only at HE
  have HJ:=native_original_forward_longitudinal_joint_restoration n q U b h K S hKS g.tree ho
    (fun _=>1) (g.embed s) g.mark hU hq0 hq hb hh hK hbm hhm hKm
  dsimp only at HJ
  have hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      Nat.min_eq_left (hs.le.trans hU)]
  rw [hsplit] at HJ
  linear_combination HE+HJ

end OAI.SKFluctuations.Cavity
