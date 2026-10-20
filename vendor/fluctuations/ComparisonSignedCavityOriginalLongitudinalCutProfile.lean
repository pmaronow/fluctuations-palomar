module

public import ComparisonSignedCavityOriginalGPairCutProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Classical
open scoped NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_longitudinal_cut_difference_abs_le_profile
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (r : ℕ) (hT : T.leaves≤r)
    (U V : ℕ) (hU0 : 0<U) (hUV : U≤V) (hV : V≤as.length)
    (b h K C : ℕ→ℝ) (hKC : ∀j,K j=h j+b j*C j)
    (hKm : Monotone K) (hK0 : ∀j,0≤K j)
    (q : ℕ→FullCoordinate n→ℝ) (P : T.Assignment→ℝ) (a : T.Slot)
    (A : ℝ) (hA : 0≤A)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0 q (fun σ=>(P σ)^2) 0≤A^2) :
    let coef:=(3/2:ℝ)*(errorJetVariation (r+3) 0 0*((r+3:ℕ)+1))*K (V-1)
    let f:=fun j=>if j<U then 0 else
      if j<V then nativeWholeLawErrorRadius n as q (cutTSlope n U 0 b h K) j
      else coef*nativeWholeLawErrorRadius n as q (cutTSlope n V 0 b h K) j
    abs (nativeOriginalLongitudinalPairing n 0 q 0 U K b C T P a-
      nativeOriginalLongitudinalPairing n 0 q 0 V K b C T P a) ≤
      A*forkVariation r 3*(T.forkCost f+edgeBudget 0 as f) := by
  dsimp only
  let coef:=(3/2:ℝ)*(errorJetVariation (r+3) 0 0*((r+3:ℕ)+1))*K (V-1)
  let f:=fun j=>if j<U then 0 else
    if j<V then nativeWholeLawErrorRadius n as q (cutTSlope n U 0 b h K) j
    else coef*nativeWholeLawErrorRadius n as q (cutTSlope n V 0 b h K) j
  have hc : 0≤coef:=mul_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg (errorJetVariation_nonneg (r+3) 0 0) (by positivity))) (hK0 _)
  have hf j : 0≤f j:=by
    dsimp only [f]
    split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
    · exact mul_nonneg hc (Real.sqrt_nonneg _)
  let F:=fun (cut : ℕ) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
      (z : MarkedPlacement r.tree)=>
    z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*nativeOriginalHighGAtom z.tree cut K b C
        (z.embed (r.embed (p.embed a))) (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ) 0
  let G:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (z : MarkedPlacement r.tree)=>
    z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ=>P (p.restrict (r.restrict (z.restrict σ)))*
        (nativeOriginalHighGAtom z.tree U K b C
          (z.embed (r.embed (p.embed a))) (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ-
         nativeOriginalHighGAtom z.tree V K b C
          (z.embed (r.embed (p.embed a))) (z.embed (r.embed p.mark)) (z.embed r.mark) z.mark σ)) 0
  have HE (cut : ℕ) : nativeOriginalLongitudinalPairing n 0 q 0 cut K b C T P a=
      ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*F cut g.p g.r g.z)).sum:=by
    rw [nativeOriginalGMarkedWords_weighted_kernel_sum]
    rfl
  have HG (g : NativeOriginalGMarkedWord T) : G g.p g.r g.z=F U g.p g.r g.z-F V g.p g.r g.z:=by
    dsimp only [G,F]
    simp only [mul_sub,ClockTree.disorderExpect,Finset.sum_sub_distrib]
  have Hdiff : nativeOriginalLongitudinalPairing n 0 q 0 U K b C T P a-
      nativeOriginalLongitudinalPairing n 0 q 0 V K b C T P a=
      ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*G g.p g.r g.z)).sum:=by
    rw [HE U,HE V]
    simp only [HG,mul_sub,sum_map_sub_explicit]
  have HB (g : NativeOriginalGMarkedWord T) : abs (G g.p g.r g.z)≤A*g.tree.forkCost f:=by
    have HP : g.z.tree.disorderExpect (fullWeight n) (fullFeature n) 0 q
        (fun σ=>(P (g.p.restrict (g.r.restrict (g.z.restrict σ))))^2) 0≤A^2:=by
      rw [g.r.tree.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
        g.z g.hz 0 q (fun σ=>(P (g.p.restrict (g.r.restrict σ)))^2) 0,
        g.p.tree.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
          g.r g.hr 0 q (fun σ=>(P (g.p.restrict σ))^2) 0,
        T.markedAttach_disorderPreserves_actual (fullWeight_pos n) (fullFeature n) ho
          g.p g.hp 0 q (fun σ=>(P σ)^2) 0]
      exact hP
    have Hleaves : g.z.tree.leaves≤r+3:=by
      have H1:=T.markedAttach_leaves 0 g.p g.hp
      have H2:=g.p.tree.markedAttach_leaves 0 g.r g.hr
      have H3:=g.r.tree.markedAttach_leaves 0 g.z g.hz
      omega
    by_cases hdiag : g.z.embed g.r.mark=g.z.mark
    · have Hzero : G g.p g.r g.z=0:=by
        dsimp only [G]
        simp only [hdiag,native_original_G_atom_zero_of_diagonal_error_pair,sub_self,mul_zero,
          ClockTree.disorderExpect,Finset.sum_const_zero]
      rw [Hzero,abs_zero]
      exact mul_nonneg hA (g.tree.forkCost_nonneg hf)
    · have H:=native_original_G_pair_cut_difference_abs_le_profile g.z.tree ho (r+3) Hleaves
        U V hU0 hUV hV b h K C hKC hKm hK0 q
        (fun σ=>P (g.p.restrict (g.r.restrict (g.z.restrict σ))))
        (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
        (g.z.embed g.r.mark) g.z.mark A hA HP
      change abs (G g.p g.r g.z)≤A*f (g.z.tree.splitIndex (g.z.embed g.r.mark) g.z.mark) at H
      exact H.trans (mul_le_mul_of_nonneg_left
        (g.z.tree.split_le_forkCost hf (g.z.embed g.r.mark) g.z.mark hdiag) hA)
  have Habs (l : List ℝ) : abs l.sum≤(l.map abs).sum:=by
    induction l with
    | nil=>simp
    | cons u l ih=>
      simp only [List.sum_cons,List.map_cons]
      linarith [abs_add_le u l.sum]
  rw [Hdiff]
  calc
    _ ≤ ((nativeOriginalGMarkedWords T).map (fun g=>abs (g.coefficient*G g.p g.r g.z))).sum:=
      by simpa only [List.map_map,Function.comp_def] using
        Habs ((nativeOriginalGMarkedWords T).map (fun g=>g.coefficient*G g.p g.r g.z))
    _ ≤ ((nativeOriginalGMarkedWords T).map (fun g=>A*(abs g.coefficient*g.tree.forkCost f))).sum:=by
      apply List.sum_le_sum
      intro g hg
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (HB g) (abs_nonneg g.coefficient)).trans_eq (by ring)
    _ = A*((nativeOriginalGMarkedWords T).map (fun g=>abs g.coefficient*g.tree.forkCost f)).sum:=
      List.sum_map_mul_left _ _ _
    _ ≤ A*(forkVariation r 3*(T.forkCost f+edgeBudget 0 as f)):=
      mul_le_mul_of_nonneg_left (nativeOriginalGMarkedWords_forkProfile_le T ho f hf r hT) hA
    _ = _:=by ring

end OAI.SKFluctuations.Cavity
