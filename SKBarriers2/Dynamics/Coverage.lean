module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import SKBarriers2.Interfaces
public import OAI.Probability.SKBarriers.Coverage.CoverageTheorem

@[expose] public section

/-! Coverage with the overlap cutoff chosen before the sublinear scale.
The proofs are adapted from upstream `CoverageLimit` and `CoverageTheorem`;
only the quantifier order changes. -/

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
open OAI.SK OAI.SK.Analytic

namespace SKBarriers2

/-- Pair coverage with a temperature-dependent cutoff independent of `L`. -/
theorem uniform_coverage_pair' {β : ℝ} (hβ : 1 < β) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ L : ℕ → ℝ,
      Tendsto L atTop atTop →
      Tendsto (fun n => L n / (n : ℝ)) atTop (𝓝 0) →
      ∀ D : ℝ, 0 < D → ∃ D₂ : ℝ, 0 < D₂ ∧
        Tendsto (fun n => (disorderLaw n).real
          (coveragePairBad n β (Real.exp (-D * L n)) (Real.exp (-D₂ * L n)) q))
          atTop (𝓝 0) := by
  obtain ⟨e,he,cE,hcE,N₀,hN₀⟩ := coverage_energy_tail hβ
  have hβpos : 0 < β := lt_trans zero_lt_one hβ
  obtain ⟨q,hq,hq1,hK⟩ := exists_positive_coverageGainRate hβpos he.2
  refine ⟨q,hq,hq1,?_⟩
  intro L hL hsub D hD
  obtain ⟨M,D₂,hM,hD₂,hpars⟩ := coverage_eventually_parameters (e := e) (q := q) L hβpos hcE hD hK hL hsub
  refine ⟨D₂,hD₂,?_⟩
  have hbound : ∀ᶠ n : ℕ in atTop,
      (disorderLaw n).real (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q) ≤
        Real.exp (-cE*(n:ℝ))+2*Real.exp (-L n/(β^2*M)) := by
    filter_upwards [hpars,eventually_ge_atTop N₀] with n hn hlarge
    obtain ⟨hnpos,hLn,hb,htrim,hsecond,hgain⟩ := hn
    have HH := coveragePairBad_probability_le hnpos hβpos.le
      (Real.exp_pos (-D*L n)) (Real.exp_nonneg (-D₂*L n)) hq.le hb htrim hLn.le hsecond hgain
    have HE := hN₀ n hlarge
    have hn' : (0:ℝ) < n := by exact_mod_cast hnpos
    have hθ : coverageAngle L M n^2 = M*L n/(n:ℝ) := Real.sq_sqrt (by positivity)
    have hquot : -(L n)^2/((coverageAngle L M n)^2*β^2*(n:ℝ)) = -L n/(β^2*M) := by
      rw [hθ]
      field_simp
    rw [hquot] at HH
    exact HH.trans (add_le_add HE le_rfl)
  have hE : Tendsto (fun n : ℕ => Real.exp (-cE*(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (neg_neg_of_pos hcE))
  have hR : Tendsto (fun n => Real.exp (-L n/(β^2*M))) atTop (𝓝 0) := by
    have H := Real.tendsto_exp_atBot.comp
      (hL.const_mul_atTop_of_neg (neg_lt_zero.mpr (show 0 < 1/(β^2*M) by positivity)))
    convert H using 1
    funext n
    congr 1
    ring
  have H := hE.add (hR.const_mul 2)
  simp only [mul_zero,add_zero] at H
  exact squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) hbound H

/-- Uniform coverage: choose `q` before choosing any diverging sublinear scale. -/
theorem uniform_coverage' {β : ℝ} (hβ : 1 < β) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ L : ℕ → ℝ,
      Tendsto L atTop atTop →
      Tendsto (fun n => L n / (n : ℝ)) atTop (𝓝 0) →
      ∀ D : ℝ, 0 < D → ∃ c : ℝ, 0 < c ∧
        ∃ C : (n : ℕ) → Set (Disorder n), (∀ n, MeasurableSet (C n)) ∧
          Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
          ∀ n J, J ∈ C n → ∀ S : Finset (Config n),
            finiteMass (gibbs β J) (S.filter (fun x =>
              finiteMass (gibbs β J) (S.filter (fun y => q ≤ |overlap x y|)) <
                Real.exp (-c * L n))) < Real.exp (-D * L n) := by
  obtain ⟨q, hq, hq1, H⟩ := uniform_coverage_pair' hβ
  refine ⟨q, hq, hq1, ?_⟩
  intro L hL hsub D hD
  obtain ⟨D₂,hD₂,hlim⟩ := H L hL hsub D hD
  let C (n : ℕ) := (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q)ᶜ
  have hm (n : ℕ) := measurableSet_coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q
  refine ⟨D+D₂,add_pos hD hD₂,C,(fun n => (hm n).compl),?_,?_⟩
  · have Hlim := (tendsto_const_nhds (x := (1:ℝ))).sub hlim
    simp only [sub_zero] at Hlim
    convert Hlim using 1
    funext n
    dsimp only [C]
    rw [measureReal_compl (hm n),probReal_univ]
  · intro n J hJ S
    have hpair (T : Finset (Config n)) (hT : Real.exp (-D*L n) ≤ finiteMass (gibbs β J) T) :
        Real.exp (-D₂*L n) ≤ weightedOverlapMass (conditionalWeights (gibbs β J) T) q := by
      have hraw : Real.exp (-D₂*L n)*(finiteMass (gibbs β J) T)^2 ≤
          finiteOverlapMass (gibbs β J) T q := by
        apply le_of_not_gt
        intro hbad
        exact hJ ⟨T,hT,hbad⟩
      rw [weightedOverlapMass_conditional]
      exact (le_div_iff₀ (sq_pos_of_pos ((Real.exp_pos _).trans_le hT))).mpr hraw
    have Hcov := finite_coverage_of_pair_bound (gibbs β J) (fun x => (gibbs_pos β J x).le)
      (Real.exp_pos (-D*L n)) (Real.exp_nonneg (-D₂*L n)) hpair S
    have heq : Real.exp (-D*L n)*Real.exp (-D₂*L n) = Real.exp (-(D+D₂)*L n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq] at Hcov

end SKBarriers2
