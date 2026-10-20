module

public import SKBarriers2.Corner.PathEnergyInner7

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic

namespace SKBarriers2.Corner

open StepCalculus
local notation "E" => (Fin 3 → ℝ)

private theorem inner8_window_direction_bound (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (α : ℝ → ℝ) (s h : ℝ), 0 ≤ h → ∀ N : ℕ,
      ∀ p ∈ windowKCurves β α s h N, ∀ k : ℝ, |k| ≤ 1/2 →
      ‖(p k).2‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
        ‖deriv (fun t => (p t).2) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) ∧
        ‖deriv (deriv (fun t => (p t).2)) k‖ ≤ L*Real.sqrt (h/(N : ℝ)) := by
  obtain ⟨A,hA,hbound⟩ := window_direction_budget
  refine ⟨A*|β|,by positivity,?_⟩
  intro α s h hh N p hp k hk
  obtain ⟨σ,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,_,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact (hbound β h hh N i k hk).2

theorem scalarData_orderedInner_valueRemainder_jets_bound {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0 < l) (hu : u < D.q) :
    ∃ C h0 kap : ℝ, 0 ≤ C ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ N : ℕ, 1 ≤ N →
      ∀ lam ∈ Icc (0 : ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k| ≤ kap →
      ∀ x : E, ∀ c : ℕ, c ≤ 2 →
      let α := cdf (D.μ : Measure ℝ)
      |iteratedDeriv c (fun t => orderedInnerValueRemainder β α (α (r-h))
        (r-h) h N lam j t x) k| ≤ C*h^2 := by
  by_cases hlu : l ≤ u
  · obtain ⟨A,a0,hV,hA,ha0,hhV,hvar⟩ :=
      scalarData_interpolated_window_variation_inputs D hl hlu hu
    obtain ⟨C₁,hJ,hC₁,hhJ,hvariations⟩ :=
      scalarData_interpolated_window_variations_c6_c4 D hl hlu hu
    obtain ⟨B,aE,S,hE,kapE,hB,_,_,hhE,hkapE,hentropy⟩ :=
      scalarData_uniformWindowEntropyInputs D hl hu
    obtain ⟨L,hL,hdir⟩ := inner8_window_direction_bound β
    let K := spatialStepDifferenceCoefficient 2 B
    have hK : 0 ≤ K := spatialStepDifferenceCoefficient_nonneg 2 hB
    let R := K*A+C₁
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    let V := innerLocalTaylorCoefficient B R a0
    have hV0 : 0 ≤ V := innerLocalTaylorCoefficient_nonneg hB hR ha0
    let C := (21*B+6)*R*L^2+V*L^4
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have hden : 0 < A*(2*B+1)+1 := by positivity
    refine ⟨12*C,min hV (min hJ (min hE (min (1/(A*(2*B+1)+1))
      (min (1/(R+1)) 1)))),min kapE (1/2),by positivity,
      lt_min hhV (lt_min hhJ (lt_min hhE (lt_min (by positivity)
        (lt_min (by positivity) (by norm_num))))),lt_min hkapE (by norm_num),?_⟩
    intro r hr h hh hh0 N hN lam hlam j k hk x c hc
    dsimp only
    have hhV' := hh0.trans (min_le_left _ _)
    have hhJ' := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hhE' := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have hhsmall := hh0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hhR := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    have hh1 : h ≤ 1 := hh0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
    have hRh : R*h ≤ 1 := by
      have H := (le_div_iff₀ (by positivity : 0 < R+1)).mp hhR
      nlinarith only [H,hh.le]
    have hkhalf := hk.trans (min_le_right _ _)
    let α := cdf (D.μ : Measure ℝ)
    let ps := windowKCurves β (interpolatedProfile α (α (r-h)) lam) (r-h) h N
    let qs := ps.drop (j.val+1)
    let Ls := massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h k N) lam
    let f := massVariationTerminal β α (r-h) h
    have hpath : ps.map (fun p => p k) = Ls := by
      dsimp only [ps,Ls]
      rw [windowKCurves_apply β _ (r-h) h k N hh.le,massPath_window_eq]
    obtain ⟨he,hinputs⟩ := hvar r hr h hh hhV' N hN lam hlam k hkhalf
    have henergy : chainEnergy Ls ≤ A*h := by
      rw [← hpath]
      exact (chainEnergy_le_windowVariationEnergy ps k).trans he
    have hshort : (2*B+1)*chainEnergy Ls ≤ 1 := by
      have H := (le_div_iff₀ hden).mp hhsmall
      have H' := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 2*B+1 by positivity)
      nlinarith only [H,H',hh.le]
    have hm : ∀ p ∈ Ls, p.1 ∈ Icc (0:ℝ) 1 := by
      rw [← hpath]
      intro p hp
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
      exact ⟨ha0.le.trans (hinputs q hq).2.1.1,(hinputs q hq).2.1.2⟩
    have hv : ∀ p ∈ Ls, ‖p.2‖ ≤ 1 ∧ p.1*(B*‖p.2‖^2) ≤ 1/2 := by
      intro p hp
      have hs : ‖p.2‖^2 ≤ chainEnergy Ls := by
        exact List.single_le_sum (fun a ha => by
          obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
          exact sq_nonneg _) _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
      have hE := chainEnergy_nonneg Ls
      have hsmall : B*‖p.2‖^2 ≤ 1/2 := by
        have H := mul_le_mul_of_nonneg_left hs hB
        nlinarith only [H,hshort,hE]
      refine ⟨by nlinarith [norm_nonneg p.2],?_⟩
      exact (mul_le_of_le_one_left (by positivity) (hm p hp).2).trans hsmall
    obtain ⟨_,hEN⟩ := hentropy r hr h hh hhE' k (hk.trans (min_le_left _ _)) N hN
    have hinner := (hEN lam hlam).1
    have hlen : 0 < Ls.length := by
      dsimp only [Ls]
      rw [massPath,List.length_map,windowMassPath_length]
      omega
    have hsp : SpatialChainJets 5 B (Ls.drop (j.val+1)) f := by
      apply strictSuffix_spatialChainJets hlen
      intro n hn
      exact (hinner n (by simpa only [Ls,massPath,List.length_map] using hn)).of_le (by norm_num)
    have hf : QPotential 4 B f := by
      simpa only [List.drop_length,vectorIncrementChain] using (hsp ((Ls.drop (j.val+1)).length)).of_le
        (by norm_num : 4 ≤ 5)
    have hqse : qs.map (fun p => p k) = Ls.drop (j.val+1) := by
      dsimp only [qs]
      rw [List.map_drop,hpath]
    have hmem : ∀ p ∈ qs, p ∈ ps := fun p hp => List.mem_of_mem_drop hp
    have hreg : ∀ p ∈ qs, ContDiffAt ℝ 2 p k := fun p hp => (hinputs p (hmem p hp)).1
    have hpos : ∀ p ∈ qs, 0 < (p k).1 := fun p hp =>
      ha0.trans_le (hinputs p (hmem p hp)).2.1.1
    let d := L*Real.sqrt (h/(N:ℝ))
    have hd : 0 ≤ d := by dsimp only [d]; positivity
    have hd2 : d^2 = L^2*h/(N:ℝ) := by
      dsimp only [d]
      rw [mul_pow,Real.sq_sqrt (div_nonneg hh.le (Nat.cast_nonneg N))]
      ring
    have hd4 : d^4 = L^4*h^2/(N:ℝ)^2 := by
      calc
        d^4 = (d^2)^2 := by ring
        _ = _ := by rw [hd2]; ring
    let J := (21*B+6)*R*h*d^2+V*d^4
    have hJ0 : 0 ≤ J := by dsimp only [J]; positivity
    have hlocal : ∀ front p tail, qs = front++p::tail → ∀ y : E,
        ∀ a : ℕ, a ≤ 2 → |iteratedDeriv a (chainHeadRemainder f p tail y) k| ≤ J := by
      intro front p tail hsplit y a ha
      have hsplitFull : ps = (ps.take (j.val+1)++front)++p::tail := by
        calc
          ps = ps.take (j.val+1)++qs := (List.take_append_drop _ _).symm
          _ = _ := by rw [hsplit,List.append_assoc]
      have hp : p ∈ ps := by rw [hsplitFull]; simp
      have hsub : ∀ q ∈ p::tail, q ∈ ps := by
        intro q hq
        rw [hsplitFull]
        exact List.mem_append_right _ hq
      have hdrop : qs.drop (front.length+1) = tail := by
        calc
          _ = (qs.drop front.length).drop 1 := (List.drop_drop (i := 1) (j := front.length) (l := qs)).symm
          _ = tail := by rw [hsplit,List.drop_left]; rfl
      have htailEq : (Ls.drop (j.val+1)).drop (front.length+1) = tail.map (fun q => q k) := by
        rw [← hqse,← List.map_drop,hdrop]
      have htailsp : SpatialChainJets 5 B (tail.map (fun q => q k)) f := by
        rw [← htailEq]
        exact hsp.drop _
      have htailmem : ∀ q ∈ tail.map (fun q => q k), q ∈ Ls := by
        intro q hq
        rw [← hpath]
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
        exact List.mem_map.mpr ⟨z,hsub z (by simp [hz]),rfl⟩
      have htailE : chainEnergy (tail.map (fun q => q k)) ≤ chainEnergy Ls := by
        have hsplitEval : Ls = ((ps.take (j.val+1)++front).map (fun q => q k))++
            (p k)::tail.map (fun q => q k) := by
          have H := congrArg (fun rs => rs.map (fun q => q k)) hsplitFull
          exact hpath.symm.trans (by simpa only [List.map_append,List.map_cons] using H)
        rw [hsplitEval,chainEnergy_append,chainEnergy_cons]
        nlinarith only [chainEnergy_nonneg ((ps.take (j.val+1)++front).map (fun q => q k)),
          sq_nonneg ‖(p k).2‖]
      have hδ : QBoundedJets 3 (R*h) (fun z => vectorIncrementChain
          (tail.map (fun q => q k)) f z-f z) := by
        apply (qBoundedJets_chain_sub _ htailsp
          (fun q hq => hm q (htailmem q hq)) (fun q hq => hv q (htailmem q hq))).mono
        calc
          _ ≤ K*(A*h) := mul_le_mul_of_nonneg_left (htailE.trans henergy) hK
          _ ≤ R*h := by dsimp only [R,K]; nlinarith only [mul_nonneg hC₁.le hh.le]
      have hj := hvariations r hr h hh hhJ' N hN lam hlam k hkhalf
        ((ps.take (j.val+1)++front)++[p]) tail (by simpa only [List.append_assoc,List.singleton_append] using hsplitFull)
      have hbound : C₁*h ≤ R*h := by dsimp only [R]; nlinarith only [mul_nonneg (mul_nonneg hK hA.le) hh.le]
      have hdirs := hdir _ _ _ hh.le N p hp k hkhalf
      apply abs_chainHeadRemainder_jets_le hf hR ha0 hh hh1 hRh hd p tail
        (fun q hq => (hinputs q (hsub q hq)).1)
        (fun q hq => ha0.trans_le (hinputs q (hsub q hq)).2.1.1)
        ((htailsp 0).of_le (by norm_num)) hδ
        ((hj.1.of_le (by norm_num : 4 ≤ 6)).mono hbound) (hj.2.mono hbound)
        (hinputs p hp).2.1 (hinputs p hp).2.2.1 (hinputs p hp).2.2.2
        hdirs.1 hdirs.2.1 hdirs.2.2 _ y a ha
      exact (hv (p k) (by rw [← hpath]; exact List.mem_map.mpr ⟨p,hp,rfl⟩)).1
    have H := abs_chainFirstOrderRemainder_jets_le_of_local hf qs hreg hpos hlocal x c hc
    have heq (t : ℝ) : qs.map (fun p => p t) =
        (massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam).drop (j.val+1) := by
      dsimp only [qs]
      rw [List.map_drop]
      dsimp only [ps]
      rw [windowKCurves_apply β _ (r-h) h t N hh.le,massPath_window_eq]
    have hfun : (fun t => chainFirstOrderRemainder f (qs.map (fun q => q t)) x) =
        fun t => orderedInnerValueRemainder β α (α (r-h)) (r-h) h N lam j t x := by
      funext t
      rw [heq]
      rfl
    rw [hfun] at H
    have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr hN
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hJ : J ≤ C*h^2/(N:ℝ) := by
      dsimp only [J,C]
      rw [hd2,hd4]
      have HN : V*L^4*h^2/(N:ℝ)^2 ≤ V*L^4*h^2/(N:ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hNpos (by nlinarith only [hN1])
      convert add_le_add_left HN (((21*B+6)*R*L^2)*h^2/(N:ℝ)) using 1 <;> ring
    have hlength : (qs.length:ℝ) ≤ 12*(N:ℝ) := by
      exact_mod_cast (show qs.length ≤ 12*N from by
        dsimp only [qs,ps]
        rw [List.length_drop,windowKCurves_length]
        omega)
    exact H.trans ((mul_le_mul hlength hJ hJ0 (by positivity)).trans_eq (by
      dsimp only [C]
      field_simp [ne_of_gt hNpos]))
  · refine ⟨0,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim

end SKBarriers2.Corner
