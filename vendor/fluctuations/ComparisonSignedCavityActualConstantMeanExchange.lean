module

public import ComparisonSignedCavityActualExteriorGammaLongitudinal
public import ComparisonSignedCavitySingleFreshLongitudinal
public import ComparisonSignedCavityActualConstantForwardMean

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_single_fresh_partner_longitudinal_eq_old
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i : ℕ)
    (hi : i < U) (hU : U ≤ as.length)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (hA : ∀u v,A u v=A v u)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) :
    let T:=single (S:=Spin n×Bool) as
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    nativeOriginalFreshPartnerLResponse n v q x U K b C T s i (fun _ c d=>A c d)=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeOriginalLongitudinalPairing n v q x U K b C g.tree
          (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s) := by
  dsimp only
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s i
  rw [native_original_fresh_partner_longitudinal_constant_row_collapse n v q x U K b C
    T ho s i hi hU (native_single_target_star_singleton as s i) hq hq0 hK hKm A]
  have H:=native_original_single_fresh_longitudinal_symmetric n v q x U K b C as ho i
    (hi.le.trans hU) A hA hq hq0 hK hKm (by omega) hU
  dsimp only at H
  simp_rw [MarkedPlacement.restrict_at,MarkedPlacement.spin_at]
  rw [H]

theorem actual_original_constant_gap_eq_twice_old_longitudinal
    (n : ℕ) (as : List PositiveMass) (i U : ℕ)
    (hi : i < U) (hU : U≤as.length) (ho : MassOrdered 0 as) (b h K C : ℕ→ℝ)
    (hKC : ∀j,K j=h j+b j*C j)
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    let T:=ClockTree.single (S:=Spin n×Bool) as
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let s:=singleSlot (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 s i
    let qfull:=cutFullVariance n q U 1 1 b h K
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let A:=fun σ τ : Spin n×Bool=>deletedOverlap n (joinSpin σ) (joinSpin τ)-C i
    finitePhysicalMean (n+1) as b h i-nativeOriginalScalarPairMean as K i=
      chi*K i*
        (nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) (g.embed s)+
         nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree (fun _=>1) g.mark)+
      chi^2*b i*(finitePhysicalMean (n+1) as b h i-
        finitePhysicalMean (n+1) as b h i/(n+1:ℕ)-C i)+
      2*b i*chi*nativeOriginalLongitudinalPairing n 0 qfull 0 U K b C g.tree
        (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
      nativeActualOriginalForwardTaylorError n q U b h K C g.tree (fun _=>1) (g.embed s) g.mark := by
  dsimp only
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have hq : ∀j,Monotone (fun u=>q u j):=by
    intro j
    cases j with
    | inl j=>exact hbm
    | inr j=>exact hhm
  have hq0 : ∀u j,0 ≤ q u j:=by
    intro u j
    cases j with
    | inl j=>exact hb u
    | inr j=>exact hh u
  have H:=actual_original_constant_gap_eq_single_star_responses n as i U hi hU ho b h K C
    hKC hb hh hK hbm hhm hKm
  dsimp only at H
  rw [native_original_single_fresh_partner_longitudinal_eq_old n 0
    (cutFullVariance n q U 1 1 b h K) 0 U K b C as ho i hi hU
    (fun u v=>deletedOverlap n (joinSpin u) (joinSpin v)-C i)
    (by intro u v;simp only [deletedOverlap,mul_comm])
    (cutFullVariance_monotone n q U (by norm_num) (by norm_num) hq hb hh hK hbm hhm hKm)
    (cutFullVariance_nonneg n q U (by norm_num) (by norm_num) hq0 hb hh hK 0)
    hK hKm] at H
  rw [H]
  ring

end OAI.SKFluctuations.Cavity
