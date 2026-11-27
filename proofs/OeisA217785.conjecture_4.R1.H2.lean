import OMAReductions.R_OeisA217785_conjecture_4_R1
import Mathlib

-- Step OeisA217785.conjecture_4.R1.H2: hypothesis H2 of reduction OeisA217785.conjecture_4.R1
-- Credit: @bryding
-- Proof: Stickelberger parity argument. (X-1)^2 s_n = (n+1)X^(n+2) - (n+2)X^(n+1) + 1; for
-- n = 8k(k+1) the discriminant of s_n is a square, so s_n mod p cannot be irreducible of even degree.

open Finset Polynomial

namespace OMAW

lemma shift_sign {K : Type*} [CommRing K] (a : ℕ → K) (m : ℕ) (h : a (m + 1) = a 0) :
    ∏ j ∈ range (m + 1), ∏ i ∈ range j, (a (i + 1) - a (j + 1)) =
      (-1) ^ m * ∏ j ∈ range (m + 1), ∏ i ∈ range j, (a i - a j) := by
  have h1 : ∏ j ∈ range (m + 1), ∏ i ∈ range j, (a i - a j) =
      (∏ j ∈ range m, ∏ i ∈ range j, (a (i + 1) - a (j + 1))) *
        ∏ j ∈ range m, (a 0 - a (j + 1)) := by
    rw [Finset.prod_range_succ', Finset.prod_range_zero, mul_one, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_range_succ']
  have h2 : ∏ i ∈ range m, (a (i + 1) - a (m + 1)) = (-1) ^ m * ∏ j ∈ range m, (a 0 - a (j + 1)) := by
    rw [h, ← Finset.card_range m, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [Finset.prod_range_succ, h2, h1]
  ring

lemma disc_sq {K : Type*} [CommRing K] (a : ℕ → K) (m : ℕ) :
    ∏ i ∈ range m, ∏ j ∈ (range m).erase i, (a i - a j) =
      (-1) ^ (m.choose 2) * (∏ j ∈ range m, ∏ i ∈ range j, (a i - a j)) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : (range (m + 1)).erase m = range m := by
      ext x; simp; omega
    have e2 : ∀ i ∈ range m, ∏ j ∈ (range (m + 1)).erase i, (a i - a j) =
        (a i - a m) * ∏ j ∈ (range m).erase i, (a i - a j) := by
      intro i hi
      have hne : m ≠ i := by
        have := Finset.mem_range.1 hi; omega
      rw [Finset.range_add_one, Finset.erase_insert_of_ne hne, Finset.prod_insert]
      simp
    rw [Finset.prod_range_succ, e1, Finset.prod_congr rfl e2, Finset.prod_mul_distrib, ih,
      Finset.prod_range_succ (fun j => ∏ i ∈ range j, (a i - a j))]
    have h3 : ∏ j ∈ range m, (a m - a j) = (-1) ^ m * ∏ i ∈ range m, (a i - a m) := by
      rw [← Finset.card_range m, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      ring
    have h4 : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ' m 1]; simp [add_comm]
    rw [h3, h4, pow_add]
    ring

/-- the polynomial `s_n` over a commutative ring -/
noncomputable def sP (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((k : R) + 1) * X ^ k

lemma sP_identity (R : Type*) [CommRing R] (n : ℕ) :
    (X - 1) ^ 2 * sP R n =
      C ((n : R) + 1) * X ^ (n + 2) - C ((n : R) + 2) * X ^ (n + 1) + 1 := by
  unfold sP
  induction n with
  | zero =>
    have h2 : (C (2 : R) : R[X]) = 2 := map_ofNat C 2
    simp [h2]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, C_ofNat]
    ring

lemma sP_coeff (R : Type*) [CommRing R] (n j : ℕ) :
    (sP R n).coeff j = if j ≤ n then (j : R) + 1 else 0 := by
  unfold sP
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hj; exact absurd (Finset.mem_range.2 (by omega)) hj
  · refine Finset.sum_eq_zero fun b hb => ?_
    have := Finset.mem_range.1 hb
    have : j ≠ b := by omega
    simp [this]

lemma sP_natDegree_le (R : Type*) [CommRing R] (n : ℕ) : (sP R n).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [sP_coeff, if_neg (by omega)]

lemma sP_natDegree (R : Type*) [CommRing R] (n : ℕ) (h : (n : R) + 1 ≠ 0) :
    (sP R n).natDegree = n := by
  refine le_antisymm (sP_natDegree_le R n) ?_
  apply le_natDegree_of_ne_zero
  rw [sP_coeff, if_pos le_rfl]; exact h

lemma sP_eval_zero (R : Type*) [CommRing R] (n : ℕ) : (sP R n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, sP_coeff]; simp

lemma sP_eval_one (R : Type*) [CommRing R] (n : ℕ) :
    2 * (sP R n).eval 1 = ((n : R) + 1) * ((n : R) + 2) := by
  unfold sP
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, eval_add, mul_add, ih]
    simp
    ring

lemma sP_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    (sP R n).map φ = sP S n := by
  unfold sP
  simp [Polynomial.map_sum]


section field
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

/-- special primes: `p ∣ N` with `g = 1 - X^N` -/
lemma special (N : ℕ) (hN : 17 ≤ N) (hpN : p ∣ N) (f : (ZMod p)[X])
    (hf : (X - 1) ^ 2 * f = 1 - X ^ N) : ¬ Irreducible f := by
  intro hirr
  obtain ⟨m, rfl⟩ := hpN
  have hpp := hp.out
  have e : (1 : (ZMod p)[X]) - X ^ (p * m) = -((X ^ m - 1) ^ p) := by
    rw [sub_pow_char, one_pow, ← pow_mul, mul_comm m p]; ring
  have hdvd : f ∣ (X ^ m - 1) ^ p := by
    refine ⟨-(X - 1) ^ 2, ?_⟩
    have := hf.trans e
    linear_combination this
  have hdvd2 : f ∣ X ^ m - 1 := hirr.prime.dvd_of_dvd_pow hdvd
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hne : (X ^ m - 1 : (ZMod p)[X]) ≠ 0 := (monic_X_pow_sub_C (1 : ZMod p) hm.ne').ne_zero
  have hXm : (X ^ m - 1 : (ZMod p)[X]).natDegree = m := by
    have := natDegree_X_pow_sub_C (R := ZMod p) (n := m) (r := 1)
    simpa using this
  have hX1 : (X - 1 : (ZMod p)[X]).natDegree = 1 := by
    have := natDegree_X_sub_C (1 : ZMod p)
    simpa using this
  have hd1 : f.natDegree ≤ m := by
    have := natDegree_le_of_dvd hdvd2 hne
    rwa [hXm] at this
  have hd2 : ((X - 1) ^ 2 * f : (ZMod p)[X]).natDegree = 2 + f.natDegree := by
    have hmon : ((X - 1) ^ 2 : (ZMod p)[X]).Monic := (monic_X_sub_C (1 : ZMod p)).pow 2
    rw [hmon.natDegree_mul' hirr.ne_zero]
    congr 1
    rw [natDegree_pow, hX1]
  have hd3 : ((1 : (ZMod p)[X]) - X ^ (p * m)).natDegree = p * m := by
    rw [e, natDegree_neg, natDegree_pow, hXm]
  rw [hf, hd3] at hd2
  have h2 : 2 ≤ p := hpp.two_le
  nlinarith [Nat.mul_le_mul_right m h2]


lemma main_case (k : ℕ) (hk : 0 < k) (hn : n = 8 * k * (k + 1)) (hp2 : p ≠ 2)
    (hL : ((n : ZMod p) + 1) ≠ 0) (hM : ((n : ZMod p) + 2) ≠ 0) :
    ¬ Irreducible (sP (ZMod p) n) := by
  intro hirr
  have hpp := hp.out
  obtain ⟨f, hfdef⟩ : ∃ f, f = sP (ZMod p) n := ⟨_, rfl⟩
  rw [← hfdef] at hirr
  haveI : Fact (Irreducible f) := ⟨hirr⟩
  have hdeg : f.natDegree = n := by rw [hfdef]; exact sP_natDegree _ n hL
  let K := AdjoinRoot f
  obtain ⟨α, hαdef⟩ : ∃ α : K, α = AdjoinRoot.root f := ⟨_, rfl⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  haveI : ExpChar K p := ExpChar.prime hpp
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite (ZMod p) K := pb.finite
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := K), ZMod.card, pb.finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have hc : ∀ (c : ZMod p) (i : ℕ), (algebraMap (ZMod p) K c) ^ p ^ i = algebraMap (ZMod p) K c := by
    intro c i; rw [← map_pow, ZMod.pow_card_pow]
  obtain ⟨a, ha⟩ : ∃ a : ℕ → K, ∀ i, a i = α ^ p ^ i := ⟨fun i => α ^ p ^ i, fun _ => rfl⟩
  have hfrob : ∀ (i : ℕ) (q : (ZMod p)[X]), (aeval α q) ^ p ^ i = aeval (a i) q := by
    intro i q
    have : ((iterateFrobenius K p i).comp (aeval α : (ZMod p)[X] →ₐ[ZMod p] K).toRingHom) =
        (aeval (a i) : (ZMod p)[X] →ₐ[ZMod p] K).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [iterateFrobenius_def, hc]
      · simp [iterateFrobenius_def, ha]
    have h := congrArg (fun φ => φ q) this
    simpa [iterateFrobenius_def] using h
  have hα : aeval α f = 0 := by
    rw [hαdef, AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_self
  have hroot : ∀ i, aeval (a i) f = 0 := fun i => by
    rw [← hfrob, hα, zero_pow (pow_pos hpp.pos i).ne']
  have hfix : ∀ x : K, x ^ p ^ n = x := by
    intro x; rw [← hcard]; exact FiniteField.pow_card x
  have han : a n = a 0 := by rw [ha, ha, hfix]; simp
  have hne : ∀ i j, i < j → j < n → a i ≠ a j := by
    intro i j hij hjn h
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd : 0 < d := by omega
    have h1 : α ^ p ^ d = α := by
      have h0 : (α ^ p ^ d - α) ^ p ^ i = 0 := by
        rw [sub_pow_expChar_pow, ← pow_mul, ← pow_add, add_comm d i, ← ha, ← ha, h, sub_self]
      exact sub_eq_zero.1 (pow_eq_zero_iff (pow_pos hpp.pos i).ne' |>.1 h0)
    have h2 : ∀ x : K, x ^ p ^ d = x := by
      intro x
      obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [← AdjoinRoot.aeval_eq, ← hαdef, hfrob, ha, h1]
    have h3 : Fintype.card K ≤ p ^ d := by
      have hq : (X ^ p ^ d - X : K[X]) ≠ 0 :=
        FiniteField.X_pow_card_pow_sub_X_ne_zero K hd.ne' hpp.one_lt
      calc Fintype.card K = (Finset.univ : Finset K).card := rfl
        _ ≤ (X ^ p ^ d - X : K[X]).roots.toFinset.card := by
            apply Finset.card_le_card
            intro x _
            rw [Multiset.mem_toFinset, mem_roots hq]
            simp [h2 x]
        _ ≤ Multiset.card (X ^ p ^ d - X : K[X]).roots := Multiset.toFinset_card_le _
        _ ≤ (X ^ p ^ d - X : K[X]).natDegree := card_roots' _
        _ = p ^ d := FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hd.ne' hpp.one_lt
    rw [hcard] at h3
    have := Nat.pow_lt_pow_right hpp.one_lt (show d < n by omega)
    omega
  have hinj : ∀ x ∈ range n, ∀ y ∈ range n, a x = a y → x = y := by
    intro x hx y hy h
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with h' | h'
    · exact hne x y h' (Finset.mem_range.1 hy) h
    · exact hne y x h' (Finset.mem_range.1 hx) h.symm
  -- the polynomial over K
  obtain ⟨fK, hfKdef⟩ : ∃ g, g = f.map (algebraMap (ZMod p) K) := ⟨_, rfl⟩
  have hfK : fK = sP K n :=
    hfKdef.trans ((congrArg (Polynomial.map (algebraMap (ZMod p) K)) hfdef).trans (sP_map _ n))
  have e2 : algebraMap (ZMod p) K 2 = 2 := map_ofNat _ 2
  have hLK : ((n : K) + 1) ≠ 0 := by
    have := (algebraMap (ZMod p) K).injective.ne hL
    simpa using this
  have hMK : ((n : K) + 2) ≠ 0 := by
    have := (algebraMap (ZMod p) K).injective.ne hM
    simpa [e2] using this
  have h2K : (2 : K) ≠ 0 := by
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this)
    have := (algebraMap (ZMod p) K).injective.ne h2
    intro h; apply this; rw [e2, map_zero, h]
  have hdegK : fK.natDegree = n := by rw [hfK]; exact sP_natDegree K n hLK
  have hlc : fK.leadingCoeff = (n : K) + 1 := by
    rw [leadingCoeff, hdegK, hfK, sP_coeff, if_pos le_rfl]
  have hfK0 : fK ≠ 0 := by
    intro h; rw [h] at hlc; simp at hlc; exact hLK hlc.symm
  have hrootK : ∀ i, eval (a i) fK = 0 := by
    intro i; rw [hfKdef, eval_map_algebraMap]; exact hroot i
  have hScard : ((range n).image a).card = n := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy h
    exact hinj x (by simpa using hx) y (by simpa using hy) h
  have hroots : fK.roots = ((range n).image a).val := by
    symm
    apply Multiset.eq_of_le_of_card_le
    · rw [Multiset.le_iff_subset ((range n).image a).nodup]
      intro x hx
      have hx' : x ∈ (range n).image a := hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx'
      exact (mem_roots hfK0).2 (hrootK i)
    · calc Multiset.card fK.roots ≤ fK.natDegree := card_roots' _
        _ = Multiset.card ((range n).image a).val := by rw [hdegK]; exact hScard.symm
  have hfact : fK = C ((n : K) + 1) * Lagrange.nodal (range n) a := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := fK)
      (by rw [hroots, hdegK]; exact hScard)
    rw [hroots, hlc] at h
    rw [← h, Lagrange.nodal]
    congr 1
    exact Finset.prod_image (s := range n) (g := a) (f := fun x => X - C x) hinj
  -- evaluations
  have hEven : Even n := ⟨4 * k * (k + 1), by rw [hn]; ring⟩
  obtain ⟨A, hA⟩ : ∃ A : K, A = ∏ i ∈ range n, a i := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : K, B = ∏ i ∈ range n, (a i - 1) := ⟨_, rfl⟩
  obtain ⟨Rr, hR⟩ : ∃ Rr : K, Rr = ∏ i ∈ range n, ∏ j ∈ (range n).erase i, (a i - a j) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : K, P = ∏ j ∈ range n, ∏ i ∈ range j, (a i - a j) := ⟨_, rfl⟩
  have hLA : ((n : K) + 1) * A = 1 := by
    have h := congrArg (eval 0) hfact
    rw [hfK, sP_eval_zero, eval_mul, eval_C, Lagrange.eval_nodal] at h
    have h' : ∏ i ∈ range n, ((0 : K) - a i) = A := by
      simp only [zero_sub]
      rw [Finset.prod_neg, Finset.card_range, hEven.neg_one_pow, one_mul, hA]
    rw [h'] at h; exact h.symm
  have h2B : 2 * B = (n : K) + 2 := by
    have h : 2 * eval 1 fK = 2 * eval 1 (C ((n : K) + 1) * Lagrange.nodal (range n) a) :=
      congrArg (fun q => 2 * eval 1 q) hfact
    have h' : ∏ i ∈ range n, ((1 : K) - a i) = B := by
      have : ∀ i ∈ range n, (1 : K) - a i = -(a i - 1) := fun i _ => by ring
      rw [Finset.prod_congr rfl this, Finset.prod_neg, Finset.card_range, hEven.neg_one_pow,
        one_mul, hB]
    rw [hfK, sP_eval_one, eval_mul, eval_C, Lagrange.eval_nodal, h'] at h
    apply mul_left_cancel₀ hLK
    linear_combination -h
  have hder : ∀ i ∈ range n, (a i - 1) * (((n : K) + 1) * ∏ j ∈ (range n).erase i, (a i - a j)) =
      ((n : K) + 1) * ((n : K) + 2) * a i ^ n := by
    intro i hi
    have hd1 : eval (a i) (derivative fK) =
        ((n : K) + 1) * ∏ j ∈ (range n).erase i, (a i - a j) := by
      rw [hfact, derivative_C_mul, eval_mul, eval_C,
        Lagrange.eval_nodal_derivative_eval_node_eq hi, Lagrange.eval_nodal]
    have hid : (X - 1) ^ 2 * fK =
        C ((n : K) + 1) * X ^ (n + 2) - C ((n : K) + 2) * X ^ (n + 1) + 1 := by
      rw [hfK]; exact sP_identity K n
    have hid2 := congrArg (fun q => eval (a i) (derivative q)) hid
    simp [derivative_mul, hrootK i] at hid2
    rw [← hd1]
    have hne1 : a i - 1 ≠ 0 := by
      intro h1
      have h1' : a i = 1 := sub_eq_zero.1 h1
      have h0 := hrootK i
      rw [h1'] at h0
      have h3 := sP_eval_one K n
      rw [← hfK, h0, mul_zero] at h3
      exact mul_ne_zero hLK hMK h3.symm
    apply mul_left_cancel₀ hne1
    linear_combination hid2
  have hprod : B * (((n : K) + 1) ^ n * Rr) = (((n : K) + 1) * ((n : K) + 2)) ^ n * A ^ n := by
    have h := Finset.prod_congr rfl hder
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_pow] at h
    rw [← hA, ← hB, ← hR] at h
    rw [mul_pow]; exact h
  have hBM : B * (((n : K) + 1) ^ n * Rr) = ((n : K) + 2) ^ n := by
    rw [hprod, ← mul_pow]
    congr 1
    linear_combination ((n : K) + 2) * hLA
  have hnpos : 0 < n := by rw [hn]; positivity
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hodd : Odd m := by
    have h := hEven
    rw [hm] at h
    exact Nat.not_even_iff_odd.1 (Nat.even_add_one.1 h)
  obtain ⟨t, ht⟩ := hodd
  have hpn : ∀ x : K, x ^ n = (x ^ (t + 1)) ^ 2 := fun x => by rw [hm, ht]; ring
  have hpm : ∀ x : K, x ^ m = x * (x ^ t) ^ 2 := fun x => by rw [ht]; ring
  have hpnm : ∀ x : K, x ^ n = x * x ^ m := fun x => by rw [hm, pow_succ']
  have hLR : ((n : K) + 1) ^ n * Rr = 2 * ((n : K) + 2) ^ m := by
    apply mul_left_cancel₀ hMK
    linear_combination (-(((n : K) + 1) ^ n * Rr)) * h2B + 2 * hBM + 2 * hpnm ((n : K) + 2)
  have hch : Even (n.choose 2) := by
    rw [Nat.choose_two_right, hn,
      show 8 * k * (k + 1) * (8 * k * (k + 1) - 1) = 2 * (2 * (2 * k * (k + 1) * (8 * k * (k + 1) - 1))) by ring,
      Nat.mul_div_cancel_left _ two_pos]
    exact even_two_mul _
  have hRP : Rr = P ^ 2 := by
    rw [hR, disc_sq, ← hP, hch.neg_one_pow, one_mul]
  have hPp : P ^ p = -P := by
    have h := shift_sign a m (by rw [← hm]; exact han)
    rw [← hm] at h
    have e : ∏ j ∈ range n, ∏ i ∈ range j, (a (i + 1) - a (j + 1)) = P ^ p := by
      rw [hP, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [sub_pow_expChar, ha, ha, ha, ha, ← pow_mul, ← pow_mul, ← pow_succ, ← pow_succ]
    have hodd' : Odd m := ⟨t, ht⟩
    rw [e, hodd'.neg_one_pow, ← hP] at h
    linear_combination h
  have hfixp : ∀ c : ZMod p, (algebraMap (ZMod p) K c) ^ p = algebraMap (ZMod p) K c := fun c => by
    simpa using hc c 1
  have hMq : (n : K) + 2 = 2 * (2 * (k : K) + 1) ^ 2 := by
    rw [hn, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; ring
  obtain ⟨c0, hc0⟩ : ∃ c0 : ZMod p, c0 = 2 * (2 * (k : ZMod p) + 1) * ((n : ZMod p) + 2) ^ t := ⟨_, rfl⟩
  have hc1 : algebraMap (ZMod p) K c0 = 2 * (2 * (k : K) + 1) * ((n : K) + 2) ^ t := by
    rw [hc0]; simp [e2]
  obtain ⟨u, hu⟩ : ∃ u : K, u = ((n : K) + 1) ^ (t + 1) * P := ⟨_, rfl⟩
  have husq : u ^ 2 = (algebraMap (ZMod p) K c0) ^ 2 := by
    rw [hc1, hu]
    rw [hRP] at hLR
    linear_combination hLR - P ^ 2 * hpn ((n : K) + 1) + 2 * hpm ((n : K) + 2)
      + 2 * (((n : K) + 2) ^ t) ^ 2 * hMq
  have hup : u ^ p = u := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ husq with h | h
    · rw [h]; exact hfixp c0
    · rw [h, ← map_neg]; exact hfixp (-c0)
  have hLp : (((n : K) + 1) ^ (t + 1)) ^ p = ((n : K) + 1) ^ (t + 1) := by
    have h := hfixp (((n : ZMod p) + 1) ^ (t + 1))
    simpa using h
  have hu0 : u = 0 := by
    have h : u = -u := by
      conv_lhs => rw [← hup, hu, mul_pow, hLp, hPp]
      rw [hu]; ring
    have h' : (2 : K) * u = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd h'' h2K
    · exact h''
  have hP0 : P = 0 := by
    rw [hu] at hu0
    rcases mul_eq_zero.1 hu0 with h | h
    · exact absurd (pow_eq_zero_iff (Nat.succ_ne_zero t) |>.1 h) hLK
    · exact h
  rw [hRP, hP0] at hLR
  have : (2 : K) * ((n : K) + 2) ^ m ≠ 0 := mul_ne_zero h2K (pow_ne_zero m hMK)
  apply this
  rw [← hLR]; ring_nf

end field

end OMAW

theorem OMA.solution : OMA.R_OeisA217785_conjecture_4_R1.H2 := by
  intro n _ hex p hp
  obtain ⟨k, hk, hn⟩ := hex
  haveI : Fact p.Prime := ⟨hp⟩
  have hmap : Polynomial.map (Int.castRingHom (ZMod p)) (OeisA217785.polyS n) =
      OMAW.sP (ZMod p) n := by
    unfold OeisA217785.polyS OMAW.sP
    simp [Polynomial.map_sum]
  rw [hmap]
  have h16 : 16 ≤ n := by rw [hn]; nlinarith
  have hid := OMAW.sP_identity (ZMod p) n
  by_cases hL : ((n : ZMod p) + 1) = 0
  · have hdvd : p ∣ n + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast; exact hL
    refine OMAW.special p (n + 1) (by omega) hdvd _ ?_
    have hM : ((n : ZMod p) + 2) = 1 := by linear_combination hL
    rw [hid, hL, hM]; simp; ring
  · by_cases hM : ((n : ZMod p) + 2) = 0
    · have hdvd : p ∣ n + 2 := by
        rw [← ZMod.natCast_eq_zero_iff]; push_cast; exact hM
      refine OMAW.special p (n + 2) (by omega) hdvd _ ?_
      have hL' : ((n : ZMod p) + 1) = -1 := by linear_combination hM
      rw [hid, hL', hM]; simp; ring
    · have hp2 : p ≠ 2 := by
        intro h2
        apply hM
        have : ((n + 2 : ℕ) : ZMod p) = 0 := by
          rw [ZMod.natCast_eq_zero_iff, h2, hn]
          exact ⟨4 * k * (k + 1) + 1, by ring⟩
        push_cast at this; exact this
      exact OMAW.main_case p n k hk hn hp2 hL hM
