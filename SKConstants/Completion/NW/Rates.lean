module

public import SKConstants.Completion.N13bc.Node
public import SKConstants.Completion.N13A.Statements

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped NNReal Topology

namespace SKConstants.Completion.NW
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4 N13A N13bc

theorem log_proxy_le_rpow (N R C u ε : ℝ) (hN : 1 ≤ N) (hR : 1 ≤ R)
    (hC : 0 < C) (hu : 0 ≤ u) (hε : 0 < ε) (hRC : R ≤ C * N^u) :
    Real.log (2+R) ≤ (1+|Real.log (2+C)|+u/ε)*N^ε := by
  have hN0 : 0 < N := by linarith
  have hpow := Real.one_le_rpow hN hu
  have hpowε := Real.one_le_rpow hN hε.le
  have hl : Real.log (2+R) ≤ Real.log (2+C) + u * Real.log N := by
    calc
      _ ≤ Real.log ((2+C)*N^u) := Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0]
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hN0.le hε) hu
  rw [show u*(N^ε/ε) = (u/ε)*N^ε by ring] at hlog
  have habs := mul_le_mul_of_nonneg_left hpowε (abs_nonneg (Real.log (2+C)))
  nlinarith [le_abs_self (Real.log (2+C))]

theorem sqrt_proxy_le_rpow (N R C b ε : ℝ) (hN : 1 ≤ N) (hR : 0 ≤ R)
    (hC : 0 < C) (hε : 0 ≤ ε) (hRC : R ≤ C * N^(b/2+ε)) :
    Real.sqrt R ≤ Real.sqrt C * N^(b/4+ε) := by
  have hN0 : 0 < N := by linarith
  have hp : N^(b/2+ε) ≤ N^(b/2+2*ε) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hs : (Real.sqrt C * N^(b/4+ε))^2 = C * N^(b/2+2*ε) := by
    rw [mul_pow, Real.sq_sqrt hC.le, ← Real.rpow_mul_natCast hN0.le]
    congr 2
    push_cast
    ring
  have ht : R ≤ (Real.sqrt C * N^(b/4+ε))^2 := by rw [hs]; nlinarith
  nlinarith [Real.sq_sqrt hR, Real.sqrt_nonneg R,
    show 0 ≤ Real.sqrt C * N^(b/4+ε) by positivity]

theorem coarsePosteriorProxy_eventually
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a b ε : ℝ) (hb : 0 < b) (hba : b/4 ≤ a) (ha1 : a < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (actualParisiPosteriorRowMGFProxy W β (readoutTime a b n) : ℝ) ≤
        C * (n : ℝ)^(b/2+ε) := by
  obtain ⟨C,hC,hproxy⟩ := actualParisiPosteriorRowMGFProxy_global_bound W β hβ
  refine ⟨C * Real.exp (1/2) * (2+b/ε), by positivity, ?_⟩
  filter_upwards [schedule_eventually a b hb hba ha1] with n hsched
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hV : (readoutTime a b n : ℝ) ≤ b * Real.log n + 1 :=
    (horizon_bounds a b hb hba n hsched.1 hsched.2.1).2
  have he : Real.exp ((readoutTime a b n : ℝ)/2) ≤ Real.exp (1/2) * (n : ℝ)^(b/2) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hroot : Real.sqrt (1+(readoutTime a b n : ℝ)) ≤ 1+(readoutTime a b n : ℝ) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1+(readoutTime a b n : ℝ)),
      Real.sqrt_nonneg (1+(readoutTime a b n : ℝ)), (readoutTime a b n).coe_nonneg]
  have hlog := log_term_le (n : ℝ) (readoutTime a b n) b ε hnR hb.le hε hV
  calc
    _ ≤ C * Real.exp ((readoutTime a b n : ℝ)/2) *
        Real.sqrt (1+(readoutTime a b n : ℝ)) := hproxy _
    _ ≤ (C * (Real.exp (1/2) * (n : ℝ)^(b/2))) *
        ((2+b/ε) * (n : ℝ)^ε) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he hC.le) (hroot.trans hlog)
        (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_add hn0]; ring

theorem padded_dimension_le (k : ℕ) : 2^(Nat.clog 2 k) ≤ 2*k+1 := by
  cases he : Nat.clog 2 k with
  | zero => simp
  | succ r =>
    have H : 2^r < k := Nat.pow_lt_of_lt_clog (by omega : r < Nat.clog 2 k)
    rw [pow_succ]
    omega

theorem coarsePaddedDimension_bound (p : Parameters) (hf : FineExponents p)
    (hb : CoarseExponents4 p) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ)^(paddingDepth (coarseCount p n)) ≤ 17*(n : ℝ)^p.a := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have hq : (coarseCount p n : ℝ) ≤ 8*(n : ℝ)^p.a :=
    (Nat.cast_le.mpr (show coarseCount p n ≤ stopIndex p.a p.b n by
      unfold coarseCount queryCount; omega)).trans
      (stopIndex_le p.a p.b hb.1 hb.2.2.1.le n (by omega))
  have hpad : (2 : ℝ)^(paddingDepth (coarseCount p n)) ≤ 2*(coarseCount p n : ℝ)+1 := by
    exact_mod_cast padded_dimension_le (coarseCount p n)
  have h1 := Real.one_le_rpow (show (1 : ℝ) ≤ n by exact_mod_cast hn) ha.le
  linarith

theorem coarseWeightedDenominators_eventually
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hb : CoarseExponents4 p)
    (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      let r := paddingDepth (coarseCount p n)
      let R : ℝ := actualParisiPosteriorRowMGFProxy W β (coarseTime p n)
      4096*B^2*(r+1 : ℝ)^2*Real.log (2+R) ≤ C*(n : ℝ)^(3*ε) ∧
      256*B*(r+1 : ℝ)*Real.sqrt R*Real.log (2+R) ≤ C*(n : ℝ)^(p.b/4+3*ε) := by
  have ha1 : p.a < 1 := by linarith [hf.2.2.2.2.2, hf.2.2.1]
  obtain ⟨C,hC,hproxy⟩ := coarsePosteriorProxy_eventually W β hβ p.a p.b ε
    hb.1 hb.2.2.1.le ha1 hε
  let A := 2+1/(ε*Real.log 2)
  let L := 1+|Real.log (2+C)|+(p.b/2+ε)/ε
  have hA : 0 < A := by dsimp [A]; positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hu : 0 ≤ p.b/2+ε := by linarith [hb.1]
  have hL : 0 < L := by dsimp [L]; positivity
  let Dq := 4096*B^2*A^2*L
  let Dl := 256*B*A*Real.sqrt C*L
  have hDq : 0 < Dq := by dsimp [Dq]; positivity
  have hDl : 0 < Dl := by dsimp [Dl]; positivity
  refine ⟨Dq+Dl, by positivity, ?_⟩
  filter_upwards [hproxy, eventually_ge_atTop (1 : ℕ)] with n hproxy hn
  dsimp only
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let R : ℝ := actualParisiPosteriorRowMGFProxy W β (coarseTime p n)
  have hR : 1 ≤ R := NNReal.coe_le_coe.mpr (actualParisiPosteriorRowMGFProxy_one_le W β hβ _)
  have hdepth : (paddingDepth (coarseCount p n)+1 : ℝ) ≤ A*(n : ℝ)^ε := by
    exact_mod_cast clog_depth_le_rpow (coarseCount p n) n (Nat.min_le_right _ _) hn ε hε
  have hlog : Real.log (2+R) ≤ L*(n : ℝ)^ε :=
    log_proxy_le_rpow _ _ C (p.b/2+ε) ε hnR hR hC hu hε hproxy
  have hroot : Real.sqrt R ≤ Real.sqrt C * (n : ℝ)^(p.b/4+ε) :=
    sqrt_proxy_le_rpow _ _ C p.b ε hnR (by linarith) hC hε.le hproxy
  have hdepth2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ paddingDepth (coarseCount p n)+1)
    hdepth 2
  have hq : 4096*B^2*(paddingDepth (coarseCount p n)+1 : ℝ)^2*Real.log (2+R) ≤
      Dq*(n : ℝ)^(3*ε) := by
    calc
      _ ≤ 4096*B^2*(A*(n : ℝ)^ε)^2*(L*(n : ℝ)^ε) := by
        gcongr
        exact Real.log_nonneg (by linarith)
      _ = Dq * (((n : ℝ)^ε)^2 * (n : ℝ)^ε) := by dsimp [Dq]; ring
      _ = _ := by
        rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
        congr 2
        push_cast
        ring
  have hl : 256*B*(paddingDepth (coarseCount p n)+1 : ℝ)*Real.sqrt R*Real.log (2+R) ≤
      Dl*(n : ℝ)^(p.b/4+3*ε) := by
    calc
      _ ≤ 256*B*(A*(n : ℝ)^ε)*(Real.sqrt C*(n : ℝ)^(p.b/4+ε))*(L*(n : ℝ)^ε) := by
        gcongr
        exact Real.log_nonneg (by linarith)
      _ = Dl * ((n : ℝ)^ε * (n : ℝ)^(p.b/4+ε) * (n : ℝ)^ε) := by dsimp [Dl]; ring
      _ = _ := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
        congr 2
        ring
  exact ⟨hq.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),
    hl.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))⟩

theorem coarseWeightedBudget_eventually
    {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (hf : FineExponents p) (hb : CoarseExponents4 p)
    (B M : ℝ) (hB : 0 < B) (hM : 0 < M) :
    ∀ᶠ n : ℕ in atTop,
      sevenTailBudget n (paddingDepth (coarseCount p n)) B
        (actualParisiPosteriorRowMGFProxy W β (coarseTime p n)) ((n : ℝ)^(-p.gamma)) ≤
      Real.exp (-(M*(n : ℝ)^(1-p.sb))) := by
  obtain ⟨ε,hε,hq,hl⟩ := sharpWeighted_strict_margin p hb
  obtain ⟨C,hC,hden⟩ := coarseWeightedDenominators_eventually W β hβ p hf hb B (ε/3) hB
    (by positivity)
  have ha : 0 < p.a := lt_trans hf.2.2.1 hf.2.2.2.1
  have has : p.a < 1-p.sb := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,h⟩ := hb
    exact h
  apply sevenTailBudget_eventually_le _ _ B p.a (3*(ε/3)) (p.b/4+3*(ε/3)) p.gamma p.sb
    C 17 M hB has (by linarith) (by linarith) (by linarith) hC (by norm_num) hM
  · exact Filter.Eventually.of_forall fun n =>
      NNReal.coe_le_coe.mpr (actualParisiPosteriorRowMGFProxy_one_le W β hβ _)
  · exact coarsePaddedDimension_bound p hf hb
  · exact hden.mono fun _ h => h.1
  · exact hden.mono fun _ h => h.2

theorem coarseWeightedThreshold_eventually (p : Parameters) (hf : FineExponents p)
    (hb : CoarseExponents4 p) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      4*((n : ℝ)^(-p.gamma))^2 *
        (2+5*(paddingDepth (coarseCount p n)+1 : ℝ)*
          (growingQueryTime (coarseMesh p n) (coarseCount p n) : ℝ)) ≤
      C*(n : ℝ)^(-2*p.gamma)*(Real.log (n : ℝ))^2 := by
  let A := 1/Real.log 2+2
  let C := 4*(2+5*A*(p.b+1))
  have hA : 0 < A := by dsimp [A]; positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hC : 0 < C := by dsimp [C]; positivity [hb.1]
  have ha1 : p.a < 1 := by linarith [hf.2.2.1, hf.2.2.2.2.2]
  refine ⟨C,hC,?_⟩
  filter_upwards [schedule_eventually p.a p.b hb.1 hb.2.2.1.le ha1,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1]
      with n hn hlog
  change 1 ≤ Real.log (n : ℝ) at hlog
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hdepth : (paddingDepth (coarseCount p n)+1 : ℝ) ≤ A*Real.log (n : ℝ) := by
    have H := clog_depth_le_log (coarseCount p n) n (Nat.min_le_right _ _) (by omega)
    dsimp [paddingDepth, A]
    push_cast at H
    rw [show (1/Real.log 2+2)*Real.log (n : ℝ) =
      Real.log (n : ℝ)/Real.log 2+2*Real.log (n : ℝ) by ring]
    linarith
  have ht : (growingQueryTime (coarseMesh p n) (coarseCount p n) : ℝ) ≤
      (p.b+1)*Real.log (n : ℝ) := by
    have H := (horizon_bounds p.a p.b hb.1 hb.2.2.1.le n hn.1 hn.2.1).2
    have Ht : (growingQueryTime (coarseMesh p n) (coarseCount p n) : ℝ) ≤
        (coarseTime p n : ℝ) := NNReal.coe_le_coe.mpr
      ((M1.growingQueryTime_monotone (coarseMesh p n)) (Nat.le_succ _))
    change (coarseTime p n : ℝ) ≤ _ at H
    nlinarith
  have hdt := mul_le_mul hdepth ht
    (growingQueryTime (coarseMesh p n) (coarseCount p n)).coe_nonneg (by positivity)
  have hscale : 2+5*(paddingDepth (coarseCount p n)+1 : ℝ)*
      (growingQueryTime (coarseMesh p n) (coarseCount p n) : ℝ) ≤
      (2+5*A*(p.b+1))*(Real.log (n : ℝ))^2 := by nlinarith
  have hpow : ((n : ℝ)^(-p.gamma))^2 = (n : ℝ)^(-2*p.gamma) := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    push_cast
    ring
  have H := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ 4*((n : ℝ)^(-p.gamma))^2 by positivity)
  rw [hpow] at H
  rw [hpow]
  dsimp [C]
  convert H using 1 <;> ring

end SKConstants.Completion.NW
