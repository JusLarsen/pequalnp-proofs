import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16927
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev ALL : ℕ := 18446744073709551615

theorem all_bit : ∀ p : Fin 64, ALL.testBit p = true := by decide +kernel

def nc (pool : List ℕ) : List ℕ := pool.filter (fun a => decide (a ≠ 0) && decide (a ≠ ALL))

theorem mem_nc (pool : List ℕ) (a : ℕ) : a ∈ nc pool ↔ a ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL := by
  simp [nc, List.mem_filter]

def cand (pool : List ℕ) : List ℕ :=
  pool ++ ((nc pool).map (fun a => ALL ^^^ a) ++
    (nc pool).flatMap (fun a => (nc pool).flatMap (fun b => [a &&& b, a ||| b])))

def Inv (pool : List ℕ) (ws : Fin 64 → List Bool) : Prop :=
  0 ∈ pool ∧ ALL ∈ pool ∧ ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 64, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem cand_not (pool : List ℕ) (h0 : 0 ∈ pool) (hA : ALL ∈ pool) (m : ℕ) (hm : m ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = !m.testBit p := by
  by_cases e0 : m = 0
  · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [e0, all_bit p]; simp⟩
  · by_cases eA : m = ALL
    · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [eA, all_bit p]; simp⟩
    · refine ⟨ALL ^^^ m, List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨m, (mem_nc pool m).mpr ⟨hm, e0, eA⟩, rfl⟩)), fun p => ?_⟩
      rw [Nat.testBit_xor, all_bit p]
      simp

theorem cand_and (pool : List ℕ) (h0 : 0 ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = (ma.testBit p && mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma &&& mb, ?_, fun p => Nat.testBit_and ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem cand_or (pool : List ℕ) (hA : ALL ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 64, c.testBit p = (ma.testBit p || mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma ||| mb, ?_, fun p => Nat.testBit_or ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem gate_vec (pool : List ℕ) (ws : Fin 64 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ cand pool, ∀ p : Fin 64,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨h0, hA, hw⟩ := h
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
    · exact ⟨0, List.mem_append_left _ h0, fun p => by simp [GateOp.eval]⟩
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    rcases hop with rfl | rfl | rfl
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    obtain ⟨mb, hmb, hb⟩ := hw b
    rcases hop with rfl | rfl | rfl
    · obtain ⟨c, hc, hcv⟩ := cand_and pool h0 ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_or pool hA ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (pool pool' : List ℕ) (ws : Fin 64 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 64 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 64, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  obtain ⟨h0, hA, hw⟩ := hI
  refine ⟨hsub 0 h0, hsub ALL hA, fun i => ?_⟩
  obtain ⟨m, hm, hmb⟩ := hw i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

def pool0 : List ℕ := [12297829382473034410, 14757395258967641292, 17361641481138401520, 18374966859414961920, 18446462603027742720, 18446744069414584320, 0, ALL]

def X (p : Fin 64) : List Bool := List.ofFn (fun i : Fin 6 => p.val.testBit i.val)

theorem X_len (p : Fin 64) : (X p).length = 6 := by simp [X]

theorem inv0 : Inv pool0 X := by
  refine ⟨by decide, by decide, fun i => ?_⟩
  by_cases hi : i < 6
  · have key : ∀ j : Fin 6, ∀ p : Fin 64,
        (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide +kernel
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by decide, fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

abbrev Good (T : ℕ) (G : Finset ℕ) : Prop :=
  ∀ p q : Fin 64, T.testBit p = true → T.testBit q = false →
    ∃ w ∈ G, w.testBit p ≠ w.testBit q

theorem good_mono (T : ℕ) (G H : Finset ℕ) (h : G ⊆ H) (hG : Good T G) : Good T H := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  exact ⟨w, h hw, h1⟩

theorem good_split (T : ℕ) (G : Finset ℕ) (a b c : ℕ) (hG : Good T G)
    (hc : ∀ p q : Fin 64, c.testBit p ≠ c.testBit q →
      a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q) :
    Good T (insert a (insert b (G.erase c))) := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  by_cases hwc : w = c
  · rw [hwc] at h1
    rcases hc p q h1 with h2 | h2
    · exact ⟨a, Finset.mem_insert_self _ _, h2⟩
    · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h2⟩
  · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hwc, hw⟩)), h1⟩

theorem all_bit' (i : ℕ) : ALL.testBit i = decide (i < 64) := by
  have h : ALL = 2 ^ 64 - 1 := by decide +kernel
  rw [h, Nat.testBit_two_pow_sub_one]

theorem all_lt : ALL < 2 ^ 64 := by decide +kernel

def rep (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | _ :: zs => Nat.add (Nat.mul (2 ^ 64) (rep x zs)) x

theorem rep_bit (x : ℕ) (hx : x < 2 ^ 64) : ∀ (zs : List ℕ) (i : ℕ),
    (rep x zs).testBit i = (decide (i / 64 < zs.length) && x.testBit (i % 64))
  | [], i => by simp [rep]
  | q :: zs, i => by
    rw [rep]
    change (2 ^ 64 * rep x zs + x).testBit i = _
    rw [Nat.testBit_two_pow_mul_add _ hx]
    by_cases hi : i < 64
    · have e1 : i / 64 = 0 := Nat.div_eq_of_lt hi
      have e2 : i % 64 = i := Nat.mod_eq_of_lt hi
      rw [if_pos hi, e1, e2]
      simp
    · have e1 : i / 64 = (i - 64) / 64 + 1 := by omega
      have e2 : i % 64 = (i - 64) % 64 := by omega
      rw [if_neg hi, rep_bit x hx zs (i - 64), e1, e2, List.length_cons]
      simp

theorem mul_rep (x : ℕ) : ∀ zs : List ℕ, x * rep 1 zs = rep x zs
  | [] => by simp [rep]
  | q :: zs => by
    rw [rep, rep]
    change x * (2 ^ 64 * rep 1 zs + 1) = 2 ^ 64 * rep x zs + x
    rw [← mul_rep x zs]
    ring

def msk (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | q :: zs => Nat.add (Nat.mul (2 ^ 64) (msk w zs)) (Nat.mul ALL (Nat.mod (Nat.shiftRight w q) 2))

theorem msk_bit (w : ℕ) : ∀ (zs : List ℕ) (i : ℕ),
    (msk w zs).testBit i = (decide (i / 64 < zs.length) && w.testBit (zs.getD (i / 64) 0))
  | [], i => by simp [msk]
  | q :: zs, i => by
    rw [msk]
    change (2 ^ 64 * msk w zs + ALL * ((w >>> q) % 2)).testBit i = _
    have hb : (w >>> q) % 2 = (w.testBit q).toNat := by
      rw [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]
    rw [hb]
    have hlt : ALL * (w.testBit q).toNat < 2 ^ 64 := by
      cases w.testBit q
      · show ALL * 0 < 2 ^ 64
        rw [Nat.mul_zero]
        exact Nat.two_pow_pos 64
      · show ALL * 1 < 2 ^ 64
        rw [Nat.mul_one]
        exact all_lt
    rw [Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hi : i < 64
    · have e1 : i / 64 = 0 := Nat.div_eq_of_lt hi
      rw [if_pos hi, e1, List.getD_cons_zero]
      cases w.testBit q
      · show (ALL * 0).testBit i = _
        simp
      · show (ALL * 1).testBit i = _
        rw [Nat.mul_one, all_bit']
        simp [hi]
    · have e1 : i / 64 = (i - 64) / 64 + 1 := by omega
      rw [if_neg hi, msk_bit w zs (i - 64), e1, List.getD_cons_succ, List.length_cons]
      simp

def ppos (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ := Nat.mul (Nat.land T w) (rep 1 zs)

def pneg (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ := Nat.mul (Nat.land T (Nat.xor ALL w)) (rep 1 zs)

def full (zs : List ℕ) : ℕ := Nat.mul ALL (rep 1 zs)

theorem ppos_bit (T : ℕ) (zs : List ℕ) (w : ℕ) (hT : T < 2 ^ 64) (i : ℕ) :
    (ppos T zs w).testBit i =
      (decide (i / 64 < zs.length) && (T.testBit (i % 64) && w.testBit (i % 64))) := by
  unfold ppos
  change ((T &&& w) * rep 1 zs).testBit i = _
  rw [mul_rep, rep_bit _ (lt_of_le_of_lt Nat.and_le_left hT), Nat.testBit_and]

theorem pneg_bit (T : ℕ) (zs : List ℕ) (w : ℕ) (hT : T < 2 ^ 64) (i : ℕ) :
    (pneg T zs w).testBit i =
      (decide (i / 64 < zs.length) && (T.testBit (i % 64) && !w.testBit (i % 64))) := by
  unfold pneg
  change ((T &&& (ALL ^^^ w)) * rep 1 zs).testBit i = _
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [mul_rep, rep_bit _ (lt_of_le_of_lt Nat.and_le_left hT), Nat.testBit_and, Nat.testBit_xor,
    all_bit']
  simp [hp]

theorem full_bit (zs : List ℕ) (i : ℕ) : (full zs).testBit i = decide (i / 64 < zs.length) := by
  unfold full
  change (ALL * rep 1 zs).testBit i = _
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [mul_rep, rep_bit _ all_lt, all_bit']
  simp [hp]

def pkF (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ :=
  Nat.lor (Nat.land (ppos T zs w) (msk w zs))
    (Nat.land (pneg T zs w) (Nat.xor (msk w zs) (full zs)))

abbrev Cov (T : ℕ) (zs : List ℕ) (w P : ℕ) : Prop :=
  ∀ i : ℕ, P.testBit i = true → i / 64 < zs.length ∧ T.testBit (i % 64) = true ∧
    w.testBit (i % 64) = w.testBit (zs.getD (i / 64) 0)

theorem cov_pkF (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64) (w : ℕ) : Cov T zs w (pkF T zs w) := by
  intro i h
  unfold pkF at h
  change ((ppos T zs w &&& msk w zs) ||| (pneg T zs w &&& (msk w zs ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h
  by_cases hd : i / 64 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 64) <;> cases w.testBit (i % 64) <;>
      cases w.testBit (zs.getD (i / 64) 0) <;> simp [hd]
  · simp [hd] at h

def vand (T : ℕ) (zs : List ℕ) (a b : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.land (ppos T zs a) (ppos T zs b)) (Nat.land (msk a zs) (msk b zs)))
    (Nat.land (Nat.lor (pneg T zs a) (pneg T zs b))
      (Nat.xor (Nat.land (msk a zs) (msk b zs)) (full zs)))

theorem cov_and (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64) (a b : ℕ) :
    Cov T zs (a &&& b) (vand T zs a b) := by
  intro i h
  unfold vand at h
  change (((ppos T zs a &&& ppos T zs b) &&& (msk a zs &&& msk b zs)) |||
    ((pneg T zs a ||| pneg T zs b) &&& ((msk a zs &&& msk b zs) ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h ⊢
  by_cases hd : i / 64 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 64) <;> cases a.testBit (i % 64) <;> cases b.testBit (i % 64) <;>
      cases a.testBit (zs.getD (i / 64) 0) <;> cases b.testBit (zs.getD (i / 64) 0) <;>
      simp [hd]
  · simp [hd] at h

def vor (T : ℕ) (zs : List ℕ) (a b : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.lor (ppos T zs a) (ppos T zs b)) (Nat.lor (msk a zs) (msk b zs)))
    (Nat.land (Nat.land (pneg T zs a) (pneg T zs b))
      (Nat.xor (Nat.lor (msk a zs) (msk b zs)) (full zs)))

theorem cov_or (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64) (a b : ℕ) :
    Cov T zs (a ||| b) (vor T zs a b) := by
  intro i h
  unfold vor at h
  change (((ppos T zs a ||| ppos T zs b) &&& (msk a zs ||| msk b zs)) |||
    ((pneg T zs a &&& pneg T zs b) &&& ((msk a zs ||| msk b zs) ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h ⊢
  by_cases hd : i / 64 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 64) <;> cases a.testBit (i % 64) <;> cases b.testBit (i % 64) <;>
      cases a.testBit (zs.getD (i / 64) 0) <;> cases b.testBit (zs.getD (i / 64) 0) <;>
      simp [hd]
  · simp [hd] at h

theorem cov_not (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (a : ℕ) :
    Cov T zs (ALL ^^^ a) (pkF T zs a) := by
  intro i h
  obtain ⟨h1, h2, h3⟩ := cov_pkF T zs hT a i h
  refine ⟨h1, h2, ?_⟩
  have hq := (hzs (zs.getD (i / 64) 0) (by
    rw [List.getD_eq_getElem _ _ h1]
    exact List.getElem_mem h1)).1
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [Nat.testBit_xor, Nat.testBit_xor, all_bit', all_bit', h3, decide_eq_true hp,
    decide_eq_true hq]

def andL (T : ℕ) (zs : List ℕ) (L : List ℕ) : ℕ :=
  L.foldr (fun w acc => Nat.land (pkF T zs w) acc) (ppos T zs ALL)

theorem fold_bits (T : ℕ) (zs : List ℕ) (i : ℕ) : ∀ (L : List ℕ),
    (andL T zs L).testBit i = true →
    (ppos T zs ALL).testBit i = true ∧ ∀ w ∈ L, (pkF T zs w).testBit i = true
  | [], h => ⟨h, by simp⟩
  | w :: L, h => by
    change (pkF T zs w &&& andL T zs L).testBit i = true at h
    rw [Nat.testBit_and, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := fold_bits T zs i L h.2
    refine ⟨h1, fun w' hw' => ?_⟩
    rcases List.mem_cons.mp hw' with e | e
    · rw [e]
      exact h.1
    · exact h2 w' e

abbrev GoodL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop := andL T zs L = 0

theorem goodL_of_good (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (L : List ℕ) (hg : Good T L.toFinset) :
    GoodL T zs L := by
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨h0, hall⟩ := fold_bits T zs i L hi
  rw [ppos_bit T zs ALL hT] at h0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
  obtain ⟨hk, hTp, _⟩ := h0
  have hq := hzs (zs.getD (i / 64) 0) (by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk)
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  obtain ⟨w, hw, hsep⟩ := hg ⟨i % 64, hp⟩ ⟨zs.getD (i / 64) 0, hq.1⟩ hTp hq.2
  apply hsep
  show w.testBit (i % 64) = w.testBit (zs.getD (i / 64) 0)
  exact (cov_pkF T zs hT w i (hall w (List.mem_toFinset.mp hw))).2.2

theorem good_zero (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (L : List ℕ) (c P : ℕ)
    (hP : Cov T zs c P) (hg : Good T (insert c L.toFinset)) :
    Nat.land P (andL T zs L) = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  change (P &&& andL T zs L).testBit i = true at hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  obtain ⟨_, hall⟩ := fold_bits T zs i L hi.2
  obtain ⟨hk, hTp, hcp⟩ := hP i hi.1
  have hq := hzs (zs.getD (i / 64) 0) (by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk)
  have hp : i % 64 < 64 := Nat.mod_lt _ (by norm_num)
  obtain ⟨w, hw, hsep⟩ := hg ⟨i % 64, hp⟩ ⟨zs.getD (i / 64) 0, hq.1⟩ hTp hq.2
  apply hsep
  show w.testBit (i % 64) = w.testBit (zs.getD (i / 64) 0)
  rcases Finset.mem_insert.mp hw with e | e
  · rw [e]
    exact hcp
  · exact (cov_pkF T zs hT w i (hall w (List.mem_toFinset.mp e))).2.2

def goodC (T : ℕ) (zs : List ℕ) (P : ℕ) (E : List ℕ) : Bool :=
  Nat.beq (Nat.land P (andL T zs E)) 0

theorem goodC_true (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (E : List ℕ) (c P : ℕ)
    (hP : Cov T zs c P) (hg : Good T (insert c E.toFinset)) : goodC T zs P E = true := by
  unfold goodC
  rw [good_zero T zs hT hzs E c P hP hg]
  rfl

def Sym (T : ℕ) (f : ℕ → ℕ) : Prop :=
  Function.Injective f ∧ f 0 = 0 ∧ f ALL = ALL ∧ (∀ a b : ℕ, f (a &&& b) = f a &&& f b) ∧
    (∀ a b : ℕ, f (a ||| b) = f a ||| f b) ∧ (∀ a : ℕ, f (ALL ^^^ a) = ALL ^^^ f a) ∧
    ∀ G : Finset ℕ, Good T (G.image f) → Good T G

theorem sym_id (T : ℕ) : Sym T (fun x => x) :=
  ⟨fun _ _ h => h, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun G h => by rwa [Finset.image_id'] at h⟩

theorem sym_comp (T : ℕ) (f g : ℕ → ℕ) (hf : Sym T f) (hg : Sym T g) :
    Sym T (fun x => f (g x)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hg
  refine ⟨fun a b h => g1 (f1 h), ?_, ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun G h => ?_⟩
  · show f (g 0) = 0
    rw [g2, f2]
  · show f (g ALL) = ALL
    rw [g3, f3]
  · show f (g (a &&& b)) = f (g a) &&& f (g b)
    rw [g4, f4]
  · show f (g (a ||| b)) = f (g a) ||| f (g b)
    rw [g5, f5]
  · show f (g (ALL ^^^ a)) = ALL ^^^ f (g a)
    rw [g6, f6]
  · apply g7
    apply f7
    rw [Finset.image_image]
    exact h

def appG (w : ℕ) : List ℕ → ℕ → ℕ
  | [], init => init
  | j :: π, init => Nat.add (Nat.mul 2 (appG w π init)) (Nat.mod (Nat.shiftRight w j) 2)

theorem appG_cons (w j : ℕ) (π : List ℕ) (init : ℕ) :
    appG w (j :: π) init = Nat.bit (w.testBit j) (appG w π init) := by
  rw [appG]
  show 2 * appG w π init + (w >>> j) % 2 = _
  rw [Nat.bit_val, Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]

def app (π : List ℕ) (w : ℕ) : ℕ := appG w π (w >>> π.length)

theorem appG_bit (w : ℕ) : ∀ (π : List ℕ) (init i : ℕ),
    (appG w π init).testBit i =
      if i < π.length then w.testBit (π.getD i 0) else init.testBit (i - π.length)
  | [], init, i => by simp [appG]
  | j :: π, init, 0 => by simp [appG_cons, Nat.testBit_bit_zero]
  | j :: π, init, i + 1 => by
    rw [appG_cons, Nat.testBit_bit_succ, appG_bit w π init i]
    simp

theorem app_bit (π : List ℕ) (w i : ℕ) :
    (app π w).testBit i = if i < π.length then w.testBit (π.getD i 0) else w.testBit i := by
  unfold app
  rw [appG_bit]
  split
  · rfl
  · rw [Nat.testBit_shiftRight]
    congr 1
    omega

abbrev PermOk (T : ℕ) (π : List ℕ) : Prop :=
  π.length = 64 ∧ (∀ j ∈ π, j < 64) ∧ (∀ j ∈ List.range 64, j ∈ π) ∧
    ∀ i ∈ List.range 64, T.testBit (π.getD i 0) = T.testBit i

theorem sym_app (T : ℕ) (π : List ℕ) (hπ : PermOk T π) : Sym T (app π) := by
  obtain ⟨hlen, hlt, hsurj, hT⟩ := hπ
  have hb : ∀ w i : ℕ, (app π w).testBit i =
      if i < 64 then w.testBit (π.getD i 0) else w.testBit i := by
    intro w i
    rw [app_bit, hlen]
  have hget : ∀ i : ℕ, i < 64 → π.getD i 0 < 64 := by
    intro i hi
    have hi' : i < π.length := by omega
    rw [List.getD_eq_getElem _ _ hi']
    exact hlt _ (List.getElem_mem hi')
  have hidx : ∀ j : ℕ, j < 64 → ∃ i : ℕ, i < 64 ∧ π.getD i 0 = j := by
    intro j hj
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem (hsurj j (List.mem_range.mpr hj))
    exact ⟨i, by omega, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 64
    · obtain ⟨i, hi, e⟩ := hidx j hj
      have h1 := hb a i
      have h2 := hb b i
      rw [if_pos hi, e] at h1 h2
      rw [← h1, ← h2, h]
    · have h1 := hb a j
      have h2 := hb b j
      rw [if_neg hj] at h1 h2
      rw [← h1, ← h2, h]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [hb]
    simp
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [hb, all_bit', all_bit']
    by_cases hi : i < 64
    · rw [if_pos hi, decide_eq_true (hget i hi), decide_eq_true hi]
    · rw [if_neg hi]
  · intro a b
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_and]
    split <;> rfl
  · intro a b
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_or]
    split <;> rfl
  · intro a
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_xor, all_bit']
    by_cases hi : i < 64
    · rw [if_pos hi, if_pos hi, decide_eq_true (hget i hi), decide_eq_true hi]
    · rw [if_neg hi, if_neg hi]
  · intro G hG p q hp hq
    obtain ⟨p', hp', ep⟩ := hidx p.val p.isLt
    obtain ⟨q', hq', eq⟩ := hidx q.val q.isLt
    have hTp : T.testBit p' = true := by
      rw [← hT p' (List.mem_range.mpr hp'), ep]
      exact hp
    have hTq : T.testBit q' = false := by
      rw [← hT q' (List.mem_range.mpr hq'), eq]
      exact hq
    obtain ⟨w, hw, hne⟩ := hG ⟨p', hp'⟩ ⟨q', hq'⟩ hTp hTq
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨w0, hw0, ?_⟩
    have h1 := hb w0 p'
    have h2 := hb w0 q'
    rw [if_pos hp', ep] at h1
    rw [if_pos hq', eq] at h2
    rw [← h1, ← h2]
    exact hne

def Leaf (T : ℕ) (S : Finset ℕ) : Prop :=
  S.card ≠ 1 ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c : ℕ, (c = a &&& b ∨ c = a ||| b) →
    ¬ Good T (insert c ((S.erase a).erase b))

theorem leaf_sym (T : ℕ) (f : ℕ → ℕ) (hf : Sym T f) (S : Finset ℕ) (h : Leaf T S) :
    Leaf T (S.image f) := by
  obtain ⟨f1, _, _, f4, f5, _, f7⟩ := hf
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Finset.card_image_of_injective _ f1]; exact h1, ?_⟩
  intro a ha b hb hab c hc hg
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
  have hab0 : a0 ≠ b0 := fun e => hab (by rw [e])
  have him : ∀ c0 : ℕ, insert (f c0) (((S.image f).erase (f a0)).erase (f b0)) =
      (insert c0 ((S.erase a0).erase b0)).image f := by
    intro c0
    rw [Finset.image_insert, Finset.image_erase f1, Finset.image_erase f1]
  rcases hc with e | e
  · refine h2 a0 ha0 b0 hb0 hab0 (a0 &&& b0) (Or.inl rfl) (f7 _ ?_)
    rw [← him, f4, ← e]
    exact hg
  · refine h2 a0 ha0 b0 hb0 hab0 (a0 ||| b0) (Or.inr rfl) (f7 _ ?_)
    rw [← him, f5, ← e]
    exact hg

def InF (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (δ : ℕ) (S : Finset ℕ) : Prop :=
  (∃ e ∈ fam, e.1 ≤ δ ∧ ∃ f : ℕ → ℕ, Sym T f ∧ e.2.1.toFinset.image f = S) ∨
    (D ≤ δ + 1 ∧ Leaf T S)

theorem inF_mono (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (δ δ' : ℕ) (h : δ ≤ δ') (S : Finset ℕ)
    (hS : InF T D fam δ S) : InF T D fam δ' S := by
  rcases hS with ⟨e, he, h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨e, he, le_trans h1 h, h2⟩
  · exact Or.inr ⟨by omega, h2⟩

def Clos (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) : Prop :=
  ∀ δ : ℕ, ∀ S : Finset ℕ, InF T D fam δ S → ∀ a ∈ S, ∀ b ∈ S, ∀ c : ℕ,
    ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) →
    c ∉ S → c ≠ 0 → c ≠ ALL →
    ∀ E : Finset ℕ, E ⊆ S → S ⊆ insert a (insert b E) → Good T (insert c E) →
    ∀ δ' : ℕ, δ' < D → δ' + S.card = δ + E.card + 2 → InF T D fam δ' (insert c E)

def Jn (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (pool : List ℕ) (j : ℕ) : Prop :=
  ∀ G : Finset ℕ, G ⊆ pool.toFinset → 0 ∉ G → ALL ∉ G → Good T G →
    N ≤ G.card + j ∧ ∀ δ : ℕ, δ < D → G.card + j = N + δ → InF T D fam δ G

theorem jn_weak (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (pool : List ℕ) (j : ℕ)
    (h : Jn T N D fam pool j) : Jn T N D fam pool (j + 1) := by
  intro G hG hG0 hGA hg
  obtain ⟨h1, h2⟩ := h G hG hG0 hGA hg
  exact ⟨by omega, fun δ hδ hcd =>
    inF_mono T D fam (δ - 1) δ (by omega) G (h2 (δ - 1) (by omega) (by omega))⟩

theorem jn_step (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (hcl : Clos T D fam)
    (pool : List ℕ) (j c : ℕ) (h : Jn T N D fam pool j) (hc : c ∈ cand pool) (hcn : c ∉ pool) :
    Jn T N D fam (pool ++ [c]) (j + 1) := by
  intro G hG hG0 hGA hg
  have hmem : ∀ x ∈ G, x ≠ c → x ∈ pool.toFinset := by
    intro x hx hxc
    have h1 := hG hx
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
      List.mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exact absurd h1 hxc
  by_cases hcG : c ∈ G
  · have hsubE : G.erase c ⊆ pool.toFinset := by
      intro x hx
      obtain ⟨hxc, hxG⟩ := Finset.mem_erase.mp hx
      exact hmem x hxG hxc
    have hcard : (G.erase c).card + 1 = G.card := Finset.card_erase_add_one hcG
    have hIns : insert c (G.erase c) = G := Finset.insert_erase hcG
    have hc0 : c ≠ 0 := fun e => hG0 (e ▸ hcG)
    have hcA : c ≠ ALL := fun e => hGA (e ▸ hcG)
    have key : ∃ a b : ℕ, a ∈ pool ∧ b ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL ∧ b ≠ 0 ∧ b ≠ ALL ∧
        ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) ∧
        ∀ p q : Fin 64, c.testBit p ≠ c.testBit q →
          a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q := by
      simp only [cand, List.mem_append, List.mem_map, List.mem_flatMap] at hc
      rcases hc with hc | ⟨a, ha, hc⟩ | ⟨a, ha, b, hb, hc⟩
      · exact absurd hc hcn
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        refine ⟨a, a, ha1, ha1, ha2, ha3, ha2, ha3, Or.inr ⟨rfl, hc.symm⟩,
          fun p q hpq => Or.inl ?_⟩
        intro e
        apply hpq
        rw [← hc, Nat.testBit_xor, Nat.testBit_xor, all_bit p, all_bit q, e]
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        obtain ⟨hb1, hb2, hb3⟩ := (mem_nc pool b).mp hb
        have hc' : c = a &&& b ∨ c = a ||| b := by simpa using hc
        have hab : a ≠ b := by
          intro e
          apply hcn
          rcases hc' with e2 | e2
          · rw [e2, e, Nat.and_self]
            exact hb1
          · rw [e2, e, Nat.or_self]
            exact hb1
        refine ⟨a, b, ha1, hb1, ha2, ha3, hb2, hb3, Or.inl ⟨hab, hc'⟩, fun p q hpq => ?_⟩
        by_contra hno
        rw [not_or, not_not, not_not] at hno
        apply hpq
        rcases hc' with e2 | e2
        · rw [e2, Nat.testBit_and, Nat.testBit_and, hno.1, hno.2]
        · rw [e2, Nat.testBit_or, Nat.testBit_or, hno.1, hno.2]
    obtain ⟨a, b, ha, hb, ha0, haA, hb0, hbA, hcand, hsep⟩ := key
    have hgA : Good T (insert a (insert b (G.erase c))) := good_split T G a b c hg hsep
    have hsubA : insert a (insert b (G.erase c)) ⊆ pool.toFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · rw [hx]
        exact List.mem_toFinset.mpr ha
      · rcases Finset.mem_insert.mp hx with hx | hx
        · rw [hx]
          exact List.mem_toFinset.mpr hb
        · exact hsubE hx
    have h0A : 0 ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact ha0 e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hb0 e.symm
        · exact hG0 (Finset.mem_of_mem_erase e)
    have hAA : ALL ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact haA e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hbA e.symm
        · exact hGA (Finset.mem_of_mem_erase e)
    obtain ⟨h1, h2⟩ := h _ hsubA h0A hAA hgA
    have hcA' : c ∉ insert a (insert b (G.erase c)) :=
      fun e => hcn (List.mem_toFinset.mp (hsubA e))
    have hEA : G.erase c ⊆ insert a (insert b (G.erase c)) :=
      fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    have h3 := Finset.card_insert_le a (insert b (G.erase c))
    have h4 := Finset.card_insert_le b (G.erase c)
    refine ⟨by omega, fun δ hδ hcd => ?_⟩
    have hfin := hcl ((insert a (insert b (G.erase c))).card + j - N) _
      (h2 _ (by omega) (by omega)) a (Finset.mem_insert_self _ _) b
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) c hcand hcA' hc0 hcA
      (G.erase c) hEA (Finset.Subset.refl _) (by rw [hIns]; exact hg) δ hδ (by omega)
    rw [hIns] at hfin
    exact hfin
  · have hsubG : G ⊆ pool.toFinset := fun x hx => hmem x hx (fun e => hcG (e ▸ hx))
    exact jn_weak T N D fam pool j h G hsubG hG0 hGA hg

theorem filter_ne (L : List ℕ) (a : ℕ) :
    (L.filter (fun x => decide (x ≠ a))).toFinset = L.toFinset.erase a := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq]
  tauto

theorem filter_ne2 (L : List ℕ) (a b : ℕ) :
    (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))).toFinset =
      (L.toFinset.erase a).erase b := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq,
    Bool.and_eq_true]
  tauto

theorem sub_cases (S E : Finset ℕ) (a b : ℕ) (h1 : E ⊆ S) (h2 : S ⊆ insert a (insert b E)) :
    E = S ∨ E = S.erase a ∨ E = S.erase b ∨ E = (S.erase a).erase b := by
  have hx : ∀ x ∈ S, x = a ∨ x = b ∨ x ∈ E := by
    intro x hx
    rcases Finset.mem_insert.mp (h2 hx) with e | e
    · exact Or.inl e
    · exact Or.inr (Finset.mem_insert.mp e)
  by_cases ha : a ∈ E
  · by_cases hb : b ∈ E
    · left
      refine Finset.Subset.antisymm h1 (fun x hxS => ?_)
      rcases hx x hxS with e | e | e
      · rw [e]
        exact ha
      · rw [e]
        exact hb
      · exact e
    · right; right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · rw [e]
        exact ha
      · exact absurd e hxS.1
      · exact e
  · by_cases hb : b ∈ E
    · right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · exact absurd e hxS.1
      · rw [e]
        exact hb
      · exact e
    · right; right; right
      ext x
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE),
        fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2.2 with e | e | e
      · exact absurd e hxS.2.1
      · exact absurd e hxS.1
      · exact e

abbrev LeafL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop :=
  L.length ≠ 1 ∧ ∀ a ∈ L, ∀ b ∈ L, a < b →
    goodC T zs (vand T zs a b) (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = false ∧
    goodC T zs (vor T zs a b) (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = false

theorem leaf_of_leafL (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (L : List ℕ) (hnd : L.Nodup)
    (h : LeafL T zs L) : Leaf T L.toFinset := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [List.toFinset_card_of_nodup hnd]; exact h1, ?_⟩
  intro a ha b hb hab c hc hg
  have key : ∀ a' b' : ℕ, a' ∈ L → b' ∈ L → a' < b' → (c = a' &&& b' ∨ c = a' ||| b') →
      Good T (insert c ((L.toFinset.erase a').erase b')) → False := by
    intro a' b' ha' hb' hlt hc' hg'
    obtain ⟨hA, hO⟩ := h2 a' ha' b' hb' hlt
    rw [← filter_ne2] at hg'
    rcases hc' with e | e
    · rw [e] at hg'
      rw [goodC_true T zs hT hzs _ _ _ (cov_and T zs hT a' b') hg'] at hA
      exact absurd hA (by decide)
    · rw [e] at hg'
      rw [goodC_true T zs hT hzs _ _ _ (cov_or T zs hT a' b') hg'] at hO
      exact absurd hO (by decide)
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact key a b (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hlt hc hg
  · refine key b a (List.mem_toFinset.mp hb) (List.mem_toFinset.mp ha) hgt ?_ ?_
    · rcases hc with e | e
      · exact Or.inl (e.trans (Nat.and_comm a b))
      · exact Or.inr (e.trans (Nat.or_comm a b))
    · rw [Finset.erase_right_comm]
      exact hg

def leafB (T : ℕ) (zs : List ℕ) (L : List ℕ) : Bool :=
  decide (LeafL T zs L)

theorem leafB_ok (T : ℕ) (zs : List ℕ) (L : List ℕ)
    (h : leafB T zs L = true) : LeafL T zs L := by
  unfold leafB at h
  exact of_decide_eq_true h

theorem map_fin (f : ℕ → ℕ) (L : List ℕ) : (L.map f).toFinset = L.toFinset.image f := by
  ext y
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

def ent (parts : List (List (ℕ × List ℕ × List ℕ))) (t : ℕ) : ℕ × List ℕ × List ℕ :=
  (parts.getD (t / 16) []).getD (t % 16) (0, [], [])

abbrev Hit2 (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Prop :=
  (w % 1000) / 16 < parts.length ∧
    (w % 1000) % 16 < (parts.getD ((w % 1000) / 16) []).length ∧
    (w / 1000) % 10 < perms.length ∧ (ent parts (w % 1000)).1 ≤ lv ∧
    (if (w / 1000) % 10 = 0 then (ent parts (w % 1000)).2.1
      else ((ent parts (w % 1000)).2.1.map (app (perms.getD ((w / 1000) % 10) []))).insertionSort
        (fun x y => x ≤ y)) = E.orderedInsert (fun x y => x ≤ y) c

def hit2B (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Bool :=
  decide (Hit2 parts perms lv E c w)

theorem hit2B_ok (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ)
    (h : hit2B parts perms lv E c w = true) : Hit2 parts perms lv E c w := by
  unfold hit2B at h
  exact of_decide_eq_true h

abbrev Hit (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Prop :=
  w / 10000 = (c + 3 * E.sum) % 100 ∧ hit2B parts perms lv E c w = true

def hitB (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Bool :=
  decide (Hit parts perms lv E c w)

theorem hitB_ok (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ)
    (h : hitB parts perms lv E c w = true) : Hit parts perms lv E c w := by
  unfold hitB at h
  exact of_decide_eq_true h

abbrev Opt (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ) : Prop :=
  D ≤ lv ∨ goodC T zs P E = false ∨ (∃ w ∈ wit, hitB parts perms lv E c w = true) ∨
    (D ≤ lv + 1 ∧ leafB T zs (c :: E) = true)

def optB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ) : Bool :=
  decide (Opt T zs D parts perms wit c P lv E)

theorem optB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ)
    (h : optB T zs D parts perms wit c P lv E = true) : Opt T zs D parts perms wit c P lv E := by
  unfold optB at h
  exact of_decide_eq_true h

abbrev OkOne (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ (optB T zs D parts perms wit c P (i + 2) L = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ a))) = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ b))) = true ∧
      optB T zs D parts perms wit c P i
        (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = true)

def okOneB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ) : Bool :=
  decide (OkOne T zs D parts perms i L wit a b c P)

theorem okOneB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ)
    (h : okOneB T zs D parts perms i L wit a b c P = true) : OkOne T zs D parts perms i L wit a b c P := by
  unfold okOneB at h
  exact of_decide_eq_true h

abbrev OkNot (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ (optB T zs D parts perms wit c P (i + 2) L = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ a))) = true)

def okNotB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ) : Bool :=
  decide (OkNot T zs D parts perms i L wit a c P)

theorem okNotB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ)
    (h : okNotB T zs D parts perms i L wit a c P = true) : OkNot T zs D parts perms i L wit a c P := by
  unfold okNotB at h
  exact of_decide_eq_true h

abbrev OkEntry (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (e : ℕ × List ℕ × List ℕ) : Prop :=
  e.2.1.Nodup ∧ e.2.1.length ≠ 1 ∧ ∀ a ∈ e.2.1, ∀ b ∈ e.2.1,
    (a < b → okOneB T zs D parts perms e.1 e.2.1 e.2.2 a b (a &&& b) (vand T zs a b) = true ∧
      okOneB T zs D parts perms e.1 e.2.1 e.2.2 a b (a ||| b) (vor T zs a b) = true) ∧
    (a = b → okNotB T zs D parts perms e.1 e.2.1 e.2.2 a (ALL ^^^ a) (pkF T zs a) = true)

theorem opt_inF (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 64) (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π) (wit : List ℕ) (c P : ℕ) (hP : Cov T zs c P) (lv : ℕ)
    (El : List ℕ) (hopt : optB T zs D parts perms wit c P lv El = true) (hnd : El.Nodup)
    (hc : c ∉ El) (hg : Good T (insert c El.toFinset)) (δ' : ℕ) (hδ' : δ' < D) (hle : lv ≤ δ') :
    InF T D parts.flatten δ' (insert c El.toFinset) := by
  have hcons : (c :: El).toFinset = insert c El.toFinset := List.toFinset_cons
  rcases optB_ok T zs D parts perms wit c P lv El hopt with h3 | h3 | ⟨w, hw, hh⟩ | ⟨h3, h4⟩
  · omega
  · rw [goodC_true T zs hT hzs El c P hP hg] at h3
    exact absurd h3 (by decide)
  · obtain ⟨hkey, hh2⟩ := hitB_ok parts perms lv El c w hh
    obtain ⟨hp1, hp2, hp3, hlv', heq⟩ := hit2B_ok parts perms lv El c w hh2
    left
    have hmem : ent parts (w % 1000) ∈ parts.flatten := by
      refine List.mem_flatten.mpr ⟨parts.getD ((w % 1000) / 16) [], ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hp1]
        exact List.getElem_mem hp1
      · unfold ent
        rw [List.getD_eq_getElem _ _ hp2]
        exact List.getElem_mem hp2
    by_cases h0 : (w / 1000) % 10 = 0
    · rw [if_pos h0] at heq
      refine ⟨ent parts (w % 1000), hmem, le_trans hlv' hle, fun x => x, sym_id T, ?_⟩
      rw [Finset.image_id', heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _),
        hcons]
    · rw [if_neg h0] at heq
      refine ⟨ent parts (w % 1000), hmem, le_trans hlv' hle,
        app (perms.getD ((w / 1000) % 10) []), sym_app T _ (hperm _ ?_), ?_⟩
      · rw [List.getD_eq_getElem _ _ hp3]
        exact List.getElem_mem hp3
      · rw [← map_fin, ← List.toFinset_eq_of_perm _ _
          (List.perm_insertionSort (fun x y : ℕ => x ≤ y) _),
          heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _), hcons]
  · right
    refine ⟨by omega, ?_⟩
    rw [← hcons]
    exact leaf_of_leafL T zs hT hzs (c :: El) (List.nodup_cons.mpr ⟨hc, hnd⟩)
      (leafB_ok T zs _ h4)

theorem clos_rep (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 64) (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e)
    (e : ℕ × List ℕ × List ℕ) (he : e ∈ parts.flatten) (δ : ℕ) (hlv : e.1 ≤ δ)
    (a : ℕ) (ha : a ∈ e.2.1.toFinset) (b : ℕ) (hb : b ∈ e.2.1.toFinset) (c : ℕ)
    (hcand : (a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a))
    (hcS : c ∉ e.2.1.toFinset) (hc0 : c ≠ 0) (hcA : c ≠ ALL) (E : Finset ℕ)
    (hES : E ⊆ e.2.1.toFinset) (hSE : e.2.1.toFinset ⊆ insert a (insert b E))
    (hg : Good T (insert c E)) (δ' : ℕ) (hδ' : δ' < D)
    (hlev : δ' + e.2.1.toFinset.card = δ + E.card + 2) :
    InF T D parts.flatten δ' (insert c E) := by
  obtain ⟨part, hpart, hep⟩ := List.mem_flatten.mp he
  obtain ⟨hnd, _, hall⟩ := hok part hpart e hep
  have hcL : c ∉ e.2.1 := fun h => hcS (List.mem_toFinset.mpr h)
  have fin : ∀ (P : ℕ), Cov T zs c P → ∀ (lv : ℕ) (El : List ℕ),
      optB T zs D parts perms e.2.2 c P lv El = true → El.Nodup →
      (∀ x ∈ El, x ∈ e.2.1) → El.toFinset = E → lv ≤ δ' →
      InF T D parts.flatten δ' (insert c E) := by
    intro P hP lv El hopt hEl hsub hEq hle
    have h := opt_inF T D zs parts perms hT hzs hperm e.2.2 c P hP lv El hopt hEl
      (fun h2 => hcL (hsub c h2)) (by rw [hEq]; exact hg) δ' hδ' hle
    rw [hEq] at h
    exact h
  have same : E = e.2.1.toFinset → δ' = δ + 2 := by
    intro h1
    rw [h1] at hlev
    omega
  have one : ∀ x : ℕ, x ∈ e.2.1.toFinset → E = e.2.1.toFinset.erase x → δ' = δ + 1 := by
    intro x hx h1
    have hpos : 0 < e.2.1.toFinset.card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [h1, Finset.card_erase_of_mem hx] at hlev
    omega
  have two : ∀ x y : ℕ, x ∈ e.2.1.toFinset → y ∈ e.2.1.toFinset → x ≠ y →
      E = (e.2.1.toFinset.erase x).erase y → δ' = δ := by
    intro x y hx hy hxy h1
    have h2 : 1 < e.2.1.toFinset.card := Finset.one_lt_card.mpr ⟨x, hx, y, hy, hxy⟩
    rw [h1, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx] at hlev
    omega
  have bin : ∀ a' b' : ℕ, a' ∈ e.2.1.toFinset → b' ∈ e.2.1.toFinset → a' < b' →
      (c = a' &&& b' ∨ c = a' ||| b') → e.2.1.toFinset ⊆ insert a' (insert b' E) →
      InF T D parts.flatten δ' (insert c E) := by
    intro a' b' ha' hb' hlt hc hSE'
    obtain ⟨hA, hO⟩ := (hall a' (List.mem_toFinset.mp ha') b' (List.mem_toFinset.mp hb')).1 hlt
    have hP : ∃ P : ℕ, Cov T zs c P ∧
        okOneB T zs D parts perms e.1 e.2.1 e.2.2 a' b' c P = true := by
      rcases hc with e2 | e2
      · rw [e2]
        exact ⟨_, cov_and T zs hT a' b', hA⟩
      · rw [e2]
        exact ⟨_, cov_or T zs hT a' b', hO⟩
    obtain ⟨P, hcov, hok1⟩ := hP
    rcases okOneB_ok T zs D parts perms e.1 e.2.1 e.2.2 a' b' c P hok1 with
      h | h | h | ⟨o2, o1a, o1b, o0⟩
    · exact absurd h hcL
    · exact absurd h hc0
    · exact absurd h hcA
    · rcases sub_cases e.2.1.toFinset E a' b' hES hSE' with h1 | h1 | h1 | h1
      · have h2 := same h1
        exact fin _ hcov _ e.2.1 o2 hnd (fun x hx => hx) h1.symm (by rw [h2]; exact Nat.add_le_add_right hlv 2)
      · have h2 := one a' ha' h1
        exact fin _ hcov _ _ o1a (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      · have h2 := one b' hb' h1
        exact fin _ hcov _ _ o1b (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      · have h2 := two a' b' ha' hb' (Nat.ne_of_lt hlt) h1
        exact fin _ hcov _ _ o0 (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne2, h1]) (by rw [h2]; exact hlv)
  rcases hcand with ⟨hab, hc⟩ | ⟨hab, hc⟩
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact bin a b ha hb hlt hc hSE
    · refine bin b a hb ha hgt ?_ (by rw [Finset.insert_comm]; exact hSE)
      rcases hc with e2 | e2
      · exact Or.inl (e2.trans (Nat.and_comm a b))
      · exact Or.inr (e2.trans (Nat.or_comm a b))
  · subst hab
    subst hc
    have hcov := cov_not T zs hT hzs a
    rcases okNotB_ok T zs D parts perms e.1 e.2.1 e.2.2 a (ALL ^^^ a) (pkF T zs a)
      ((hall a (List.mem_toFinset.mp ha) a (List.mem_toFinset.mp ha)).2 rfl) with
      h | h | h | ⟨o2, o1⟩
    · exact absurd h hcL
    · exact absurd h hc0
    · exact absurd h hcA
    · have fin1 : E = e.2.1.toFinset.erase a → InF T D parts.flatten δ' (insert (ALL ^^^ a) E) := by
        intro h1
        have h2 := one a ha h1
        exact fin _ hcov _ _ o1 (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      rcases sub_cases e.2.1.toFinset E a a hES hSE with h1 | h1 | h1 | h1
      · have h2 := same h1
        exact fin _ hcov _ e.2.1 o2 hnd (fun x hx => hx) h1.symm (by rw [h2]; exact Nat.add_le_add_right hlv 2)
      · exact fin1 h1
      · exact fin1 h1
      · rw [Finset.erase_idem] at h1
        exact fin1 h1

theorem clos_of_ok (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 64) (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e) :
    Clos T D parts.flatten := by
  intro δ S hS a ha b hb c hcand hcS hc0 hcA E hES hSE hg δ' hδ' hlev
  rcases hS with ⟨e, he, hlv, f, hf, himg⟩ | ⟨hD, hl1, hl2⟩
  · have hf' := hf
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
    subst himg
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
    have hc0ex : ∃ c0 : ℕ, f c0 = c ∧ ((a0 ≠ b0 ∧ (c0 = a0 &&& b0 ∨ c0 = a0 ||| b0)) ∨
        (a0 = b0 ∧ c0 = ALL ^^^ a0)) := by
      rcases hcand with ⟨hab, hc | hc⟩ | ⟨hab, hc⟩
      · exact ⟨a0 &&& b0, by rw [f4, hc], Or.inl ⟨fun e2 => hab (by rw [e2]), Or.inl rfl⟩⟩
      · exact ⟨a0 ||| b0, by rw [f5, hc], Or.inl ⟨fun e2 => hab (by rw [e2]), Or.inr rfl⟩⟩
      · exact ⟨ALL ^^^ a0, by rw [f6, hc], Or.inr ⟨f1 hab, rfl⟩⟩
    obtain ⟨c0, rfl, hcand0⟩ := hc0ex
    have hE0 : (e.2.1.toFinset.filter (fun x => f x ∈ E)).image f = E := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hES hy)
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    have hS0E : e.2.1.toFinset ⊆
        insert a0 (insert b0 (e.2.1.toFinset.filter (fun x => f x ∈ E))) := by
      intro x hx
      rcases Finset.mem_insert.mp (hSE (Finset.mem_image_of_mem f hx)) with h1 | h1
      · rw [f1 h1]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_insert.mp h1 with h1 | h1
        · rw [f1 h1]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨hx, h1⟩))
    have himg2 : (insert c0 (e.2.1.toFinset.filter (fun x => f x ∈ E))).image f =
        insert (f c0) E := by rw [Finset.image_insert, hE0]
    have hcard1 : (e.2.1.toFinset.image f).card = e.2.1.toFinset.card :=
      Finset.card_image_of_injective _ f1
    have hcard2 : E.card = (e.2.1.toFinset.filter (fun x => f x ∈ E)).card := by
      conv_lhs => rw [← hE0]
      exact Finset.card_image_of_injective _ f1
    have hrep := clos_rep T D zs parts perms hT hzs hperm hok e he δ hlv a0 ha0 b0 hb0 c0
      hcand0 (fun h => hcS (Finset.mem_image_of_mem f h)) (fun h => hc0 (by rw [h, f2]))
      (fun h => hcA (by rw [h, f3])) _ (Finset.filter_subset _ _) hS0E
      (f7 _ (by rw [himg2]; exact hg)) δ' hδ' (by omega)
    rw [← himg2]
    rcases hrep with ⟨e', he', hlv', g, hgs, hgi⟩ | ⟨hD', hleaf'⟩
    · refine Or.inl ⟨e', he', hlv', fun x => f (g x), sym_comp T f g hf' hgs, ?_⟩
      rw [← hgi, Finset.image_image]
      rfl
    · exact Or.inr ⟨hD', leaf_sym T f hf' _ hleaf'⟩
  · exfalso
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
    rcases hcand with ⟨hab, hc⟩ | ⟨hab, hc⟩
    · rcases sub_cases S E a b hES hSE with h1 | h1 | h1 | h1
      · rw [h1] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem hb] at hlev
        omega
      · rw [h1] at hg
        exact hl2 a ha b hb hab c hc hg
    · subst hab
      rcases sub_cases S E a a hES hSE with h1 | h1 | h1 | h1
      · rw [h1] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.erase_idem, Finset.card_erase_of_mem ha] at hlev
        omega

theorem jn_base (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (zs : List ℕ) (hT : T < 2 ^ 64)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (base : List ℕ)
    (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : ∃ e ∈ fam, e.1 = 0 ∧ e.2.1 = base) (hcard : base.length = N) (hnd : base.Nodup) :
    Jn T N D fam pool0 0 := by
  intro G hG hG0 hGA hg
  have hGb : G ⊆ base.toFinset := by
    intro x hx
    have h1 := List.mem_toFinset.mp (hG hx)
    rw [hpool] at h1
    rcases List.mem_append.mp h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exfalso
      rcases List.mem_cons.mp h1 with h1 | h1
      · exact hG0 (by rw [← h1]; exact hx)
      · exact hGA (by rw [← List.mem_singleton.mp h1]; exact hx)
  have hbG : base.toFinset ⊆ G := by
    intro a ha
    by_contra hna
    apply hnec a (List.mem_toFinset.mp ha)
    apply goodL_of_good T zs hT hzs
    rw [filter_ne]
    exact good_mono T G _ (fun x hx => Finset.mem_erase.mpr
      ⟨fun e => hna (by rw [← e]; exact hx), hGb hx⟩) hg
  have hEq : G = base.toFinset := Finset.Subset.antisymm hGb hbG
  have hc : G.card = N := by rw [hEq, List.toFinset_card_of_nodup hnd, hcard]
  obtain ⟨e0, he0, h01, h02⟩ := hbase
  exact ⟨by omega, fun δ _ _ => Or.inl ⟨e0, he0, by omega, fun x => x, sym_id T, by
    rw [Finset.image_id', h02]
    exact hEq.symm⟩⟩

theorem main (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (hcl : Clos T D fam)
    (hT1 : ∃ p : Fin 64, T.testBit p = true) (hT0 : ∃ q : Fin 64, T.testBit q = false) :
    ∀ (gs : List Gate) (pool : List ℕ) (ws : Fin 64 → List Bool) (L j o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv pool ws → Jn T N D fam pool j →
    (∀ p : Fin 64, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    N ≤ 1 + (j + gs.length) ∧
      ∀ δ : ℕ, δ < D → 1 + (j + gs.length) = N + δ → ∃ m : ℕ, InF T D fam δ {m}
  | [], pool, ws, L, j, o, _, _, hI, hJ, hout => by
    obtain ⟨m, hm, hmb⟩ := hI.2.2 o
    have hmT : ∀ p : Fin 64, m.testBit p = T.testBit p := fun p => (hmb p).trans (hout p)
    have hg : Good T {m} := by
      intro p q hp hq
      refine ⟨m, Finset.mem_singleton_self m, ?_⟩
      rw [hmT p, hmT q, hp, hq]
      simp
    have hm0 : (0 : ℕ) ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨p, hp⟩ := hT1
      have h1 := hmT p
      rw [← Finset.mem_singleton.mp e, Nat.zero_testBit, hp] at h1
      exact absurd h1 (by simp)
    have hmA : ALL ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨q, hq⟩ := hT0
      have h1 := hmT q
      rw [← Finset.mem_singleton.mp e, all_bit q, hq] at h1
      exact absurd h1 (by simp)
    obtain ⟨h1, h2⟩ := hJ {m} (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact List.mem_toFinset.mpr hm) hm0 hmA hg
    rw [Finset.card_singleton] at h1 h2
    simp only [List.length_nil, Nat.add_zero]
    exact ⟨by omega, fun δ hδ e => ⟨m, h2 δ hδ (by omega)⟩⟩
  | g :: gs, pool, ws, L, j, o, hg, hL, hI, hJ, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hout' : ∀ p : Fin 64, (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by
        have h3 := hout p
        rw [List.foldl_cons] at h3
        exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    have hlen2 : 1 + (j + (g :: gs).length) = 1 + ((j + 1) + gs.length) := by
      simp only [List.length_cons]
      omega
    rw [hlen2]
    by_cases hcin : c ∈ pool
    · exact main T N D fam hcl hT1 hT0 gs pool _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool pool ws L hL hI _ c hcv (fun m hm => hm) hcin)
        (jn_weak T N D fam pool j hJ) hout'
    · exact main T N D fam hcl hT1 hT0 gs (pool ++ [c]) _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        (jn_step T N D fam hcl pool j c hJ hc hcin) hout'

theorem lower (T N D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ))
    (zs base : List ℕ) (hT : T < 2 ^ 64)
    (hT1 : ∃ p : Fin 64, T.testBit p = true) (hT0 : ∃ q : Fin 64, T.testBit q = false)
    (hzs : ∀ q ∈ zs, q < 64 ∧ T.testBit q = false) (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e)
    (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : ∃ e ∈ parts.flatten, e.1 = 0 ∧ e.2.1 = base) (hcard : base.length = N)
    (hnd : base.Nodup)
    (C : Circuit) (hC : FanInTwo C) (hev : ∀ p : Fin 64, C.eval (X p) = T.testBit p) :
    N + D ≤ C.gates.length + 1 := by
  obtain ⟨h1, h2⟩ := main T N D parts.flatten (clos_of_ok T D zs parts perms hT hzs hperm hok)
    hT1 hT0 C.gates pool0 X 6 0 C.output hC X_len inv0
    (jn_base T N D parts.flatten zs hT hzs base hpool hnec hbase hcard hnd) hev
  by_contra hlt
  obtain ⟨m, hm⟩ := h2 (1 + (0 + C.gates.length) - N) (by omega) (by omega)
  rcases hm with ⟨e, he, _, f, hf, hem⟩ | ⟨_, hl1, _⟩
  · obtain ⟨part, hpart, hep⟩ := List.mem_flatten.mp he
    obtain ⟨hnd', hlen, _⟩ := hok part hpart e hep
    apply hlen
    rw [← List.toFinset_card_of_nodup hnd', ← Finset.card_image_of_injective _ hf.1, hem,
      Finset.card_singleton]
  · exact hl1 (Finset.card_singleton m)

def tab : ℕ := 18369895817292738688

def zs : List ℕ := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 16, 18, 20, 22, 24, 32, 34, 36, 40, 42, 48, 52, 56]

def t0 : ℕ := 2863311530
def t1 : ℕ := 3435973836
def t2 : ℕ := 4042322160
def t3 : ℕ := 4278255360
def t4 : ℕ := 4294901760
def t5 : ℕ := 4294967295
def t6 : ℕ := 16557098929935
def t7 : ℕ := 187647121205930
def t8 : ℕ := 225176545447116
def t9 : ℕ := 264913582878960
def t10 : ℕ := 280375465148160
def t11 : ℕ := 281470681743360
def t12 : ℕ := 281470681808895
def t13 : ℕ := 14355442858917939
def t14 : ℕ := 47851476196393130
def t15 : ℕ := 57421771435671756
def t16 : ℕ := 67555025218437360
def t17 : ℕ := 71776119077928960
def t18 : ℕ := 71777214277877760
def t19 : ℕ := 71777214294589695
def t20 : ℕ := 72057589759737855
def t21 : ℕ := 217020518514230019
def t22 : ℕ := 723401728380766730
def t23 : ℕ := 868082074056920076
def t24 : ℕ := 1080880403494997760
def t25 : ℕ := 1085086035472220160
def t26 : ℕ := 1085102592318504960
def t27 : ℕ := 1085102592571150095
def t28 : ℕ := 1085102596613472255
def t29 : ℕ := 1152657617789587455
def t30 : ℕ := 1229782938247303441
def t31 : ℕ := 2459565876494606882
def t32 : ℕ := 3472328296227680304
def t33 : ℕ := 3674993371882992384
def t34 : ℕ := 3689292520605548544
def t35 : ℕ := 3689348813882916864
def t36 : ℕ := 3689348814741910323
def t37 : ℕ := 3689348818177884159
def t38 : ℕ := 3689573991287357439
def t39 : ℕ := 4557430888798830399
def t40 : ℕ := 4919131752989213764
def t41 : ℕ := 5787213827046133840
def t42 : ℕ := 6124988953138320640
def t43 : ℕ := 6148820867675914240
def t44 : ℕ := 6148914689804861440
def t45 : ℕ := 6148914691236517205
def t46 : ℕ := 6148914694099828735
def t47 : ℕ := 6149102338357723135
def t48 : ℕ := 6196766167432910335
def t49 : ℕ := 8608480567731124087
def t50 : ℕ := 9259542123273814144
def t51 : ℕ := 9799982325021313024
def t52 : ℕ := 9838113388281462784
def t53 : ℕ := 9838263503687778304
def t54 : ℕ := 9838263505978427528
def t55 : ℕ := 11529390970613309440
def t56 : ℕ := 11574251045037015040
def t57 : ℕ := 11574427651397386240
def t58 : ℕ := 11574427654092267680
def t59 : ℕ := 12153149036796881064
def t60 : ℕ := 12249790989299875840
def t61 : ℕ := 12249977903424471040
def t62 : ℕ := 12249977906276641280
def t63 : ℕ := 12288259087233755784
def t64 : ℕ := 12295014589755599520
def t65 : ℕ := 12297641732488560640
def t66 : ℕ := 12297641735351828480
def t67 : ℕ := 12297791853048793224
def t68 : ℕ := 12297818344407081120
def t69 : ℕ := 12297828652328593920
def t70 : ℕ := 12297829379609722880
def t71 : ℕ := 12297829381900372104
def t72 : ℕ := 12297829382304604320
def t73 : ℕ := 12297829382461893120
def t74 : ℕ := 12297829382472990720
def t75 : ℕ := 12297829382473034410
def t76 : ℕ := 12297829383904690175
def t77 : ℕ := 12297923206033637375
def t78 : ℕ := 12321755120571230975
def t79 : ℕ := 12659530246663417775
def t80 : ℕ := 13527612320720337851
def t81 : ℕ := 13835269164735971328
def t82 : ℕ := 13889101254044418048
def t83 : ℕ := 13889313181676863488
def t84 : ℕ := 13889313184910721216
def t85 : ℕ := 14468034567615334600
def t86 : ℕ := 14699749187159851008
def t87 : ℕ := 14699973484109365248
def t88 : ℕ := 14699973487531969536
def t89 : ℕ := 14738254668489084040
def t90 : ℕ := 14754017507706719424
def t91 : ℕ := 14757170078986272768
def t92 : ℕ := 14757170082422194176
def t93 : ℕ := 14757320200119158920
def t94 : ℕ := 14757382013288497344
def t95 : ℕ := 14757394382794312704
def t96 : ℕ := 14757395255531667456
def t97 : ℕ := 14757395257822316680
def t98 : ℕ := 14757395258765525184
def t99 : ℕ := 14757395258954271744
def t100 : ℕ := 14757395258967588864
def t101 : ℕ := 14757395258967641292
def t102 : ℕ := 14757395259826634751
def t103 : ℕ := 14757451553104003071
def t104 : ℕ := 14771750701826559231
def t105 : ℕ := 14974415777481871311
def t106 : ℕ := 15987178197214944733
def t107 : ℕ := 16204198715729174752
def t108 : ℕ := 16927600444109941482
def t109 : ℕ := 17072280789786094828
def t110 : ℕ := 17149969068787297792
def t111 : ℕ := 17197820544983690922
def t112 : ℕ := 17207390840222969548
def t113 : ℕ := 17216698429492559872
def t114 : ℕ := 17216886076613765802
def t115 : ℕ := 17216923606038006988
def t116 : ℕ := 17216961131453612032
def t117 : ℕ := 17216961134316923562
def t118 : ℕ := 17216961134889585868
def t119 : ℕ := 17216961135462248174
def t120 : ℕ := 17293822573129236480
def t121 : ℕ := 17294086451893370880
def t122 : ℕ := 17294086455919964160
def t123 : ℕ := 17339123139398922400
def t124 : ℕ := 17348130476094714048
def t125 : ℕ := 17361376563513262080
def t126 : ℕ := 17361376567555522560
def t127 : ℕ := 17361553176610775200
def t128 : ℕ := 17361588498421825728
def t129 : ℕ := 17361640450346250240
def t130 : ℕ := 17361641477096079360
def t131 : ℕ := 17361641479790960800
def t132 : ℕ := 17361641480329937088
def t133 : ℕ := 17361641481122672640
def t134 : ℕ := 17361641481138339840
def t135 : ℕ := 17361641481138401520
def t136 : ℕ := 17361641481391046655
def t137 : ℕ := 17361658038237331455
def t138 : ℕ := 17365863670214553855
def t139 : ℕ := 17578661999652631539
def t140 : ℕ := 17723342345328784885
def t141 : ℕ := 17940362863843014904
def t142 : ℕ := 18014673391583296000
def t143 : ℕ := 18062524867779689130
def t144 : ℕ := 18082228416801733360
def t145 : ℕ := 18084767257870336000
def t146 : ℕ := 18084954904991541930
def t147 : ℕ := 18085032171453214960
def t148 : ℕ := 18085043205308416000
def t149 : ℕ := 18085043208171727530
def t150 : ℕ := 18085043209350738160
def t151 : ℕ := 18085043209519168250
def t152 : ℕ := 18158777584576425984
def t153 : ℕ := 18158790778715962368
def t154 : ℕ := 18216212550151634124
def t155 : ℕ := 18226345803934399728
def t156 : ℕ := 18229445395933298688
def t157 : ℕ := 18229670572478745804
def t158 : ℕ := 18229710309516177648
def t159 : ℕ := 18229723550950883328
def t160 : ℕ := 18229723554386857164
def t161 : ℕ := 18229723554993205488
def t162 : ℕ := 18229723555195321596
def t163 : ℕ := 18374388447579140336
def t164 : ℕ := 18374403900871474942
def t165 : ℕ := 18374686479671623680
def t166 : ℕ := 18374686483949813760
def t167 : ℕ := 18374873400926579200
def t168 : ℕ := 18374910784321932288
def t169 : ℕ := 18374950366740541440
def t170 : ℕ := 18374966855136706560
def t171 : ℕ := 18374966857988876800
def t172 : ℕ := 18374966858559310848
def t173 : ℕ := 18374966859163299840
def t174 : ℕ := 18374966859414896640
def t175 : ℕ := 18374966859414961920
def t176 : ℕ := 18374966859431673855
def t177 : ℕ := 18374967954631622655
def t178 : ℕ := 18379189048491114255
def t179 : ℕ := 18389322302273879859
def t180 : ℕ := 18398892597513158485
def t181 : ℕ := 18413248040372076424
def t182 : ℕ := 18420003542893920160
def t183 : ℕ := 18422537230001766400
def t184 : ℕ := 18422724877122972330
def t185 : ℕ := 18422817605466914560
def t186 : ℕ := 18422818331321958400
def t187 : ℕ := 18422818334185269930
def t188 : ℕ := 18422818335600213760
def t189 : ℕ := 18422818335611355050
def t190 : ℕ := 18429010879589711808
def t191 : ℕ := 18432107379212156928
def t192 : ℕ := 18432332555757604044
def t193 : ℕ := 18432387754677305088
def t194 : ℕ := 18432388626559008768
def t195 : ℕ := 18432388629994982604
def t196 : ℕ := 18432388630837264128
def t197 : ℕ := 18432388630850633676
def t198 : ℕ := 18441958926089912302
def t199 : ℕ := 18442240478376099840
def t200 : ℕ := 18442505391958978800
def t201 : ℕ := 18442520853841248000
def t202 : ℕ := 18442521880339415040
def t203 : ℕ := 18442521884381737200
def t204 : ℕ := 18442521884617670400
def t205 : ℕ := 18442521884633399280
def t206 : ℕ := 18445336677350834170
def t207 : ℕ := 18445899635894321148
def t208 : ℕ := 18446462598732840960
def t209 : ℕ := 18446462601596108800
def t210 : ℕ := 18446462602168762368
def t211 : ℕ := 18446462602775101440
def t212 : ℕ := 18446462603011031040
def t213 : ℕ := 18446462603027742720
def t214 : ℕ := 18446462603027808255
def t215 : ℕ := 18446463698244403455
def t216 : ℕ := 18446479160126672655
def t217 : ℕ := 18446518897164104499
def t218 : ℕ := 18446556426588345685
def t219 : ℕ := 18446612720724707464
def t220 : ℕ := 18446639212082995360
def t221 : ℕ := 18446649520004508160
def t222 : ℕ := 18446650245854003200
def t223 : ℕ := 18446650248717314730
def t224 : ℕ := 18446650250148904960
def t225 : ℕ := 18446650250148948650
def t226 : ℕ := 18446674533894045888
def t227 : ℕ := 18446686903399861248
def t228 : ℕ := 18446687775278235648
def t229 : ℕ := 18446687778714209484
def t230 : ℕ := 18446687779573137408
def t231 : ℕ := 18446687779573189836
def t232 : ℕ := 18446725308997431022
def t233 : ℕ := 18446726485818470400
def t234 : ℕ := 18446727310452191424
def t235 : ℕ := 18446727512315658240
def t236 : ℕ := 18446727516357980400
def t237 : ℕ := 18446727516610560000
def t238 : ℕ := 18446727516610621680
def t239 : ℕ := 18446738554676574970
def t240 : ℕ := 18446740762289765628
def t241 : ℕ := 18446742974197923840
def t242 : ℕ := 18446742978476179200
def t243 : ℕ := 18446742978492825600
def t244 : ℕ := 18446742978492890880
def t245 : ℕ := 18446743708637331370
def t246 : ℕ := 18446743854666219468
def t247 : ℕ := 18446744009285042160
def t248 : ℕ := 18446744069414584320
def t249 : ℕ := 18446744069414649855
def t250 : ℕ := 18446744069431296255
def t251 : ℕ := 18446744069667229455
def t252 : ℕ := 18446744070273577779
def t253 : ℕ := 18446744070846240085
def t254 : ℕ := 18446744071705233544
def t255 : ℕ := 18446744072109465760
def t256 : ℕ := 18446744072266754560
def t257 : ℕ := 18446744072277852160
def t258 : ℕ := 18446744072277895850
def t259 : ℕ := 18446744072648442048
def t260 : ℕ := 18446744072837188608
def t261 : ℕ := 18446744072850505728
def t262 : ℕ := 18446744072850558156
def t263 : ℕ := 18446744073423220462
def t264 : ℕ := 18446744073441177600
def t265 : ℕ := 18446744073456844800
def t266 : ℕ := 18446744073456906480
def t267 : ℕ := 18446744073625336570
def t268 : ℕ := 18446744073659022588
def t269 : ℕ := 18446744073692774400
def t270 : ℕ := 18446744073692839680
def t271 : ℕ := 18446744073703980970
def t272 : ℕ := 18446744073706209228
def t273 : ℕ := 18446744073708568560
def t274 : ℕ := 18446744073709486080
def t275 : ℕ := 18446744073709529770
def t276 : ℕ := 18446744073709538508
def t277 : ℕ := 18446744073709547760
def t278 : ℕ := 18446744073709551360

def base : List ℕ := [t75, t101, t135, t175, t213, t248]

def perms : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]

def fam0 : List (ℕ × List ℕ × List ℕ) := [
  (0, [t75, t101, t135, t175, t213, t248], [210096, 510192, 930080, 690176, 810064, 410160, 810048, 410144, 810032, 410128, 810016, 410112, 740208, 200352, 260224, 960416, 260240, 960480, 260256, 960544, 260272, 960608, 620288, 420432, 820304, 220496, 220320, 820560, 20336, 20624, 60368, 260512, 60384, 260576, 60400, 260640, 60448, 260592, 60464, 260001, 60528, 260017]),
  (2, [t75, t101, t135, t175, t213, t248, t270], [610536, 330423, 210310, 210213, 210132, 210051, 760606, 60441, 660553, 160350, 20622, 900458, 740366, 860235, 60478, 860427, 60382, 60494, 860237, 60446]),
  (2, [t101, t135, t143, t175, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t213, t258], []),
  (3, [t12, t75, t101, t135, t175, t225, t248], []),
  (3, [t19, t75, t101, t135, t189, t213, t248], []),
  (3, [t27, t75, t101, t130, t175, t213, t248], []),
  (3, [t36, t75, t88, t135, t175, t213, t248], []),
  (3, [t45, t54, t101, t135, t175, t213, t248], []),
  (3, [t52, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t81, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t113, t119, t135, t175, t248], []),
  (3, [t75, t101, t135, t149, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t195, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t245, t248], []),
  (3, [t75, t101, t162, t175, t213, t238, t248], [340577])]

def fam1 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t5, t75, t101, t135, t175, t213], [60000, 910112, 460097, 180081, 60065, 60049, 60033, 10018, 460258, 70050, 220338, 310082, 260418, 310114, 260498, 310146, 260578, 990178, 450354, 510194, 210434, 510210, 210514, 510226, 210594, 870274, 670450, 70290, 470530, 470306, 70610, 310370, 510546, 310386, 510626, 310466, 510642]),
  (2, [t75, t101, t135, t175, t213, t248, t274], [610552, 330439, 210326, 210229, 210148, 210067, 760510, 760462, 660569, 160398, 20282, 820394, 100474, 540414, 60558, 860443, 60430, 60494, 860364, 60446]),
  (3, [t0, t5, t75, t101, t135, t175, t213], []),
  (3, [t5, t75, t101, t135, t175, t213, t262], []),
  (3, [t12, t75, t101, t135, t175, t231, t248], []),
  (3, [t19, t75, t101, t135, t197, t213, t248], []),
  (3, [t27, t75, t101, t151, t175, t213, t248], []),
  (3, [t36, t75, t92, t135, t175, t213, t248], []),
  (3, [t45, t58, t101, t135, t175, t213, t248], []),
  (3, [t53, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t82, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t113, t135, t175, t213, t248], [580609]),
  (3, [t75, t101, t135, t150, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t196, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t246, t248], []),
  (3, [t75, t119, t135, t175, t197, t213, t248], [180593, 100415, 800447])]

def fam2 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t12, t75, t101, t135, t175, t248], [60000, 910128, 460161, 180145, 60129, 60113, 60033, 10099, 460339, 870131, 420419, 310163, 260499, 310195, 260579, 310227, 260068, 990259, 450435, 510275, 210515, 510291, 210595, 510323, 210084, 870355, 670531, 70371, 470611, 270403, 270100, 310451, 510627, 310483, 510116, 310563, 510132]),
  (2, [t5, t12, t75, t101, t135, t175], [310032, 310016]),
  (3, [t0, t75, t101, t135, t175, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t213, t266], []),
  (3, [t12, t75, t101, t135, t175, t238, t248], []),
  (3, [t19, t75, t101, t135, t205, t213, t248], []),
  (3, [t27, t75, t101, t162, t175, t213, t248], []),
  (3, [t36, t75, t96, t135, t175, t213, t248], []),
  (3, [t45, t62, t101, t135, t175, t213, t248], []),
  (3, [t54, t75, t101, t135, t181, t213, t248], []),
  (3, [t75, t83, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t114, t135, t175, t213, t248], [580289]),
  (3, [t75, t101, t135, t153, t162, t213, t248], []),
  (3, [t75, t101, t135, t175, t198, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t247, t248], []),
  (3, [t75, t119, t135, t175, t213, t231, t248], [580609])]

def fam3 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t19, t75, t101, t135, t213, t248], [60000, 910144, 460209, 180193, 60177, 60113, 60049, 10180, 460420, 270212, 20500, 310244, 260580, 310276, 260069, 310308, 260149, 990340, 450516, 510356, 210596, 510388, 210085, 510404, 210165, 870436, 670612, 470468, 70101, 270484, 270181, 310548, 510117, 310564, 510197, 310053, 510229]),
  (2, [t5, t19, t75, t101, t135, t213], [310048, 310016]),
  (3, [t1, t5, t75, t101, t135, t175, t213], []),
  (3, [t5, t75, t101, t135, t175, t213, t270], []),
  (3, [t12, t75, t101, t135, t175, t244, t248], []),
  (3, [t19, t75, t101, t135, t208, t213, t248], []),
  (3, [t27, t75, t101, t166, t175, t213, t248], []),
  (3, [t36, t75, t119, t135, t175, t213, t248], []),
  (3, [t45, t66, t101, t135, t175, t213, t248], []),
  (3, [t54, t75, t119, t135, t175, t213, t248], []),
  (3, [t75, t84, t92, t135, t175, t213, t248], [140273]),
  (3, [t75, t101, t115, t135, t175, t213, t248], [580289]),
  (3, [t75, t101, t135, t153, t175, t213, t248], [940641]),
  (3, [t75, t101, t135, t175, t199, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t249], []),
  (3, [t75, t119, t135, t175, t213, t248, t262], [380625])]

def fam4 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t27, t75, t101, t175, t213, t248], [60000, 910160, 460241, 180225, 60177, 60129, 60065, 10277, 460517, 470309, 820597, 310341, 260086, 310373, 260166, 310405, 260246, 990437, 450613, 510469, 210102, 510485, 210182, 510501, 210262, 70549, 470118, 470565, 70198, 270581, 270278, 310054, 510230, 310070, 510310, 310150, 510326]),
  (2, [t5, t27, t75, t101, t175, t213], [310064, 310016]),
  (3, [t1, t75, t101, t135, t175, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t213, t274], []),
  (3, [t12, t75, t101, t135, t175, t248, t249], []),
  (3, [t19, t75, t101, t135, t213, t215, t248], []),
  (3, [t27, t75, t101, t170, t175, t213, t248], []),
  (3, [t36, t75, t122, t135, t175, t213, t248], []),
  (3, [t45, t70, t101, t135, t175, t213, t248], []),
  (3, [t55, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t84, t101, t122, t175, t213, t248], [340321]),
  (3, [t75, t101, t116, t119, t135, t175, t213], []),
  (3, [t75, t101, t135, t154, t175, t213, t248], [340321, 540337]),
  (3, [t75, t101, t135, t175, t200, t213, t248], [260353]),
  (3, [t75, t101, t135, t175, t213, t248, t250], []),
  (3, [t75, t122, t135, t154, t175, t213, t248], [])]

def fam5 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t36, t75, t135, t175, t213, t248], [620000, 310176, 140257, 740225, 740193, 740145, 740081, 210390, 900630, 430422, 780119, 230454, 980199, 830486, 380279, 30518, 180359, 190566, 890135, 190582, 890215, 190598, 890295, 190614, 890375, 990071, 190247, 990087, 190327, 990103, 190407, 990167, 190343, 990183, 190423, 990263, 190439]),
  (2, [t5, t36, t75, t135, t175, t213], [990080, 870016]),
  (3, [t2, t5, t75, t101, t135, t175, t213], []),
  (3, [t6, t75, t101, t135, t175, t213, t248], []),
  (3, [t12, t75, t101, t135, t175, t248, t258], []),
  (3, [t19, t75, t101, t135, t213, t225, t248], []),
  (3, [t27, t75, t101, t175, t178, t213, t248], []),
  (3, [t36, t75, t126, t135, t175, t213, t248], []),
  (3, [t45, t84, t101, t135, t175, t213, t248], []),
  (3, [t56, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t84, t101, t135, t175, t226, t248], []),
  (3, [t75, t101, t116, t135, t175, t213, t248], [380625]),
  (3, [t75, t101, t135, t155, t175, t213, t248], [540337]),
  (3, [t75, t101, t135, t175, t201, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t251], []),
  (3, [t75, t135, t162, t175, t197, t213, t248], [940641])]

def fam6 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t45, t101, t135, t175, t213, t248], [260000, 410192, 780257, 660241, 660209, 660161, 660097, 950503, 640152, 710535, 160232, 710567, 160312, 710599, 160392, 710631, 160472, 470088, 270264, 670104, 70344, 70120, 670424, 870136, 870504, 910184, 110360, 910200, 110440, 910216, 110520, 910280, 110456, 910296, 110536, 910376, 110552]),
  (2, [t5, t45, t101, t135, t175, t213], [910096, 510016]),
  (3, [t2, t75, t101, t135, t175, t213, t248], []),
  (3, [t7, t12, t75, t101, t135, t175, t248], []),
  (3, [t12, t75, t101, t135, t175, t248, t262], []),
  (3, [t19, t75, t101, t135, t213, t231, t248], []),
  (3, [t27, t75, t101, t175, t189, t213, t248], []),
  (3, [t36, t75, t130, t135, t175, t213, t248], []),
  (3, [t45, t88, t101, t135, t175, t213, t248], []),
  (3, [t57, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t84, t101, t162, t175, t213, t248], [20383, 420207]),
  (3, [t75, t101, t117, t135, t175, t213, t248], [220191, 180305]),
  (3, [t75, t101, t135, t156, t175, t213, t248], [340577]),
  (3, [t75, t101, t135, t175, t202, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t252], []),
  (3, [t101, t122, t135, t143, t175, t213, t248], [])]

def fam7 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t5, t75, t101, t135, t175, t213, t248], [760034, 210585, 820066, 970490, 60098, 10459, 60130, 10380, 60162, 10253, 510242, 210003, 270322, 270019, 310402, 510035, 310482, 510051, 310562, 510067]),
  (2, [t12, t19, t75, t101, t135, t248], [310048, 310032]),
  (3, [t3, t5, t75, t101, t135, t175, t213], []),
  (3, [t7, t75, t101, t135, t175, t213, t248], []),
  (3, [t12, t75, t101, t135, t175, t248, t266], []),
  (3, [t19, t75, t101, t135, t213, t238, t248], []),
  (3, [t27, t75, t101, t175, t197, t213, t248], []),
  (3, [t36, t75, t135, t139, t175, t213, t248], []),
  (3, [t45, t92, t101, t135, t175, t213, t248], []),
  (3, [t59, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t84, t119, t135, t175, t213, t248], [200463, 300223]),
  (3, [t75, t101, t118, t135, t175, t213, t248], [180305]),
  (3, [t75, t101, t135, t157, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t203, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t253], []),
  (3, [t101, t135, t151, t175, t189, t213, t248], [460002])]

def fam8 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t12, t75, t101, t135, t175, t213, t248], [760115, 210601, 620147, 170506, 60179, 10475, 60211, 10396, 60243, 10062, 510307, 210004, 470387, 70020, 310467, 510036, 310547, 510052, 310643, 510148]),
  (2, [t12, t27, t75, t101, t175, t248], [310064, 310032]),
  (3, [t3, t75, t101, t135, t175, t213, t248], []),
  (3, [t8, t12, t75, t101, t135, t175, t248], []),
  (3, [t12, t75, t101, t135, t175, t248, t270], []),
  (3, [t19, t75, t101, t135, t213, t244, t248], []),
  (3, [t27, t75, t101, t175, t205, t213, t248], []),
  (3, [t36, t75, t135, t151, t175, t213, t248], []),
  (3, [t45, t96, t101, t135, t175, t213, t248], []),
  (3, [t60, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t85, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t120, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t158, t175, t213, t248], [140273]),
  (3, [t75, t101, t135, t175, t204, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t254], []),
  (3, [t66, t75, t94, t135, t175, t248], [])]

def fam9 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t19, t75, t101, t135, t175, t213, t248], [760196, 210617, 20228, 770522, 60260, 10491, 60292, 10269, 60324, 10078, 510372, 210005, 70452, 470021, 310532, 510037, 310628, 510133, 310644, 510213]),
  (2, [t12, t36, t75, t135, t175, t248], [990080, 870032]),
  (3, [t4, t5, t75, t101, t135, t175, t213], []),
  (3, [t8, t75, t101, t135, t175, t213, t248], []),
  (3, [t12, t75, t101, t135, t175, t248, t274], []),
  (3, [t19, t75, t101, t135, t213, t248, t250], []),
  (3, [t27, t75, t101, t175, t208, t213, t248], []),
  (3, [t36, t75, t135, t162, t175, t213, t248], []),
  (3, [t45, t101, t106, t135, t175, t213, t248], []),
  (3, [t61, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t86, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t121, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t159, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t206, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t255], []),
  (3, [t66, t75, t101, t158, t175, t248], [])]

def fam10 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t27, t75, t101, t135, t175, t213, t248], [760293, 210633, 220325, 570538, 60357, 10412, 60389, 10285, 60421, 10094, 510453, 210022, 870533, 670038, 310629, 510134, 310645, 510214, 310006, 510294]),
  (2, [t12, t45, t101, t135, t175, t248], [910096, 510032]),
  (3, [t4, t75, t101, t135, t175, t213, t248], []),
  (3, [t9, t12, t75, t101, t135, t175, t248], []),
  (3, [t13, t75, t101, t135, t175, t213, t248], []),
  (3, [t19, t75, t101, t135, t213, t248, t258], []),
  (3, [t27, t75, t101, t175, t213, t216, t248], []),
  (3, [t36, t75, t135, t166, t175, t213, t248], []),
  (3, [t45, t101, t119, t135, t175, t213, t248], []),
  (3, [t62, t75, t101, t135, t189, t213, t248], []),
  (3, [t75, t87, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t122, t135, t166, t213, t248], [260353]),
  (3, [t75, t101, t135, t160, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t207, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t256], []),
  (3, [t70, t75, t101, t135, t196, t213], [])]

def fam11 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t36, t75, t101, t135, t175, t213, t248], [280406, 970649, 500438, 850507, 300470, 50428, 900502, 450301, 100534, 250110, 670550, 130055, 550646, 350151, 750007, 150231, 150023, 750311, 950039, 950391]),
  (2, [t19, t27, t75, t101, t213, t248], [310064, 310048]),
  (3, [t5, t54, t75, t101, t135, t175, t213], []),
  (3, [t9, t75, t101, t135, t175, t213, t248], []),
  (3, [t14, t19, t75, t101, t135, t213, t248], []),
  (3, [t19, t75, t101, t135, t213, t248, t262], []),
  (3, [t27, t75, t101, t175, t213, t225, t248], []),
  (3, [t36, t75, t135, t170, t175, t213, t248], []),
  (3, [t45, t101, t122, t135, t175, t213, t248], []),
  (3, [t62, t75, t112, t135, t175, t213, t248], []),
  (3, [t75, t88, t101, t122, t135, t213, t248], [540337]),
  (3, [t75, t101, t122, t135, t175, t213, t264], []),
  (3, [t75, t101, t135, t161, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t209, t213, t248], [460369]),
  (3, [t75, t101, t135, t175, t213, t248, t257], []),
  (3, [t70, t101, t117, t135, t175, t213], [])]

def fam12 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t45, t75, t101, t135, t175, t213, t248], [100519, 790554, 860551, 310523, 860583, 310444, 860615, 310317, 860647, 310126, 590008, 50168, 110024, 810248, 110040, 810328, 110056, 810408, 110072, 810488]),
  (2, [t19, t36, t75, t135, t213, t248], [990080, 870048]),
  (3, [t5, t58, t75, t101, t135, t175, t213], []),
  (3, [t10, t12, t75, t101, t135, t175, t248], []),
  (3, [t14, t75, t101, t135, t175, t213, t248], []),
  (3, [t19, t75, t101, t135, t213, t248, t266], []),
  (3, [t27, t75, t101, t175, t213, t231, t248], []),
  (3, [t36, t75, t135, t175, t179, t213, t248], []),
  (3, [t45, t101, t126, t135, t175, t213, t248], []),
  (3, [t63, t75, t101, t135, t175, t213, t248], [180593, 100481]),
  (3, [t75, t88, t101, t135, t197, t213, t248], []),
  (3, [t75, t101, t122, t135, t175, t233, t248], []),
  (3, [t75, t101, t135, t164, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t210, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t259], []),
  (3, [t75, t84, t101, t153, t213, t248], [])]

def fam13 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t54, t75, t101, t135, t175, t213, t248], [330616, 50008, 770550, 650437, 650340, 650259, 650178, 900632, 500539, 700648, 100481, 700460, 940041, 300009, 100333, 500025, 900142, 280057]),
  (2, [t19, t45, t101, t135, t213, t248], [910096, 510048]),
  (3, [t5, t62, t75, t101, t135, t175, t213], []),
  (3, [t10, t75, t101, t135, t175, t213, t248], []),
  (3, [t15, t19, t75, t101, t135, t213, t248], []),
  (3, [t19, t75, t101, t135, t213, t248, t270], []),
  (3, [t27, t75, t101, t175, t213, t238, t248], []),
  (3, [t36, t75, t135, t175, t189, t213, t248], []),
  (3, [t45, t101, t130, t135, t175, t213, t248], []),
  (3, [t64, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t89, t101, t135, t175, t213, t248], [100481]),
  (3, [t75, t101, t122, t135, t189, t213, t248], []),
  (3, [t75, t101, t135, t165, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t211, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t260], []),
  (3, [t75, t84, t113, t135, t175, t248], [])]

def fam14 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t58, t75, t101, t135, t175, t213, t248], [610024, 330566, 210453, 210356, 210275, 210194, 900632, 740602, 860073, 60476, 860089, 60349, 860105, 60158]),
  (2, [t27, t36, t75, t175, t213, t248], [990080, 870064]),
  (3, [t5, t66, t75, t101, t135, t175, t213], []),
  (3, [t11, t12, t75, t101, t135, t175, t248], []),
  (3, [t15, t75, t101, t135, t175, t213, t248], []),
  (3, [t19, t75, t101, t135, t213, t248, t274], []),
  (3, [t27, t75, t101, t175, t213, t244, t248], []),
  (3, [t36, t75, t135, t175, t197, t213, t248], []),
  (3, [t45, t101, t135, t140, t175, t213, t248], []),
  (3, [t65, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t90, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t122, t135, t213, t248, t270], []),
  (3, [t75, t101, t135, t166, t175, t213, t269], []),
  (3, [t75, t101, t135, t175, t212, t213, t248], [860401]),
  (3, [t75, t101, t135, t175, t213, t248, t261], []),
  (3, [t75, t92, t101, t135, t175, t257], [])]

def fam15 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t62, t75, t101, t135, t175, t213, t248], [810600, 610040, 330582, 210469, 210372, 210291, 210210, 700648, 180593, 940650, 580185, 860073, 60587, 860137, 60365, 860153, 60174, 760169]),
  (2, [t27, t45, t101, t175, t213, t248], [910096, 510064]),
  (3, [t5, t70, t75, t101, t135, t175, t213], []),
  (3, [t11, t75, t101, t135, t175, t213, t248], []),
  (3, [t16, t19, t75, t101, t135, t213, t248], []),
  (3, [t20, t75, t101, t135, t175, t213, t248], []),
  (3, [t27, t75, t101, t175, t213, t248, t251], []),
  (3, [t36, t75, t135, t175, t205, t213, t248], []),
  (3, [t45, t101, t135, t151, t175, t213, t248], []),
  (3, [t66, t75, t92, t101, t135, t175, t248], [580289, 140239, 140159]),
  (3, [t75, t91, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t122, t175, t213, t238, t248], [740495, 340271]),
  (3, [t75, t101, t135, t167, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t214, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t263], []),
  (3, [t75, t92, t124, t175, t213, t248], [])]

def fam16 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t66, t75, t101, t135, t175, t213, t248], [810584, 610056, 330598, 210485, 210388, 210307, 210226, 300009, 580609, 340059, 980345, 860089, 460545, 60635, 860329, 860137, 460497, 60524, 860313, 860233, 460369, 60190, 860265, 760281, 20249, 60297]),
  (2, [t36, t45, t135, t175, t213, t248], [470096, 190080]),
  (3, [t5, t75, t76, t101, t135, t175, t213], []),
  (3, [t12, t54, t75, t101, t135, t175, t248], []),
  (3, [t16, t75, t101, t135, t175, t213, t248], []),
  (3, [t21, t75, t101, t135, t175, t213, t248], []),
  (3, [t27, t75, t101, t175, t213, t248, t258], []),
  (3, [t36, t75, t135, t175, t208, t213, t248], []),
  (3, [t45, t101, t135, t162, t175, t213, t248], []),
  (3, [t66, t75, t101, t135, t175, t213, t257], []),
  (3, [t75, t92, t101, t135, t175, t231, t248], []),
  (3, [t75, t101, t123, t135, t175, t213, t248], [460002]),
  (3, [t75, t101, t135, t168, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t215, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t264], []),
  (3, [t75, t94, t122, t175, t213, t248], [])]

def fam17 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t70, t75, t101, t135, t175, t213, t248], [810568, 610072, 330614, 210501, 210404, 210323, 210242, 500025, 380625, 140123, 780505, 860105, 460561, 60028, 860489, 860153, 460513, 60572, 860473, 860233, 460417, 60413, 860457, 760425, 820409, 60441]),
  (2, [t75, t94, t135, t175, t213, t248], [220143, 900287, 20271]),
  (3, [t5, t75, t84, t101, t135, t175, t213], []),
  (3, [t12, t58, t75, t101, t135, t175, t248], []),
  (3, [t17, t19, t75, t101, t135, t213, t248], []),
  (3, [t22, t27, t75, t101, t175, t213, t248], []),
  (3, [t27, t75, t101, t175, t213, t248, t262], []),
  (3, [t36, t75, t135, t175, t213, t217, t248], []),
  (3, [t45, t101, t135, t166, t175, t213, t248], []),
  (3, [t66, t75, t101, t135, t175, t225, t248], []),
  (3, [t75, t92, t101, t135, t175, t248, t274], []),
  (3, [t75, t101, t124, t135, t175, t213, t248], [940641]),
  (3, [t75, t101, t135, t169, t175, t213, t248], [860449]),
  (3, [t75, t101, t135, t175, t213, t216, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t265], []),
  (3, [t75, t94, t158, t175, t213, t248], [])]

def fam18 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t84, t101, t135, t175, t213, t248], [690088, 450487, 410646, 290533, 290436, 290355, 290274, 900632, 280586, 920122, 740010, 540588, 940026, 740433, 340429, 220090, 340042, 940206, 300106, 940058, 940074]),
  (2, [t75, t101, t113, t135, t175, t248], [140399, 420223, 20415, 780319]),
  (3, [t5, t75, t88, t101, t135, t175, t213], []),
  (3, [t12, t62, t75, t101, t135, t175, t248], []),
  (3, [t17, t75, t101, t135, t175, t213, t248], []),
  (3, [t22, t75, t101, t135, t175, t213, t248], []),
  (3, [t27, t75, t101, t175, t213, t248, t266], []),
  (3, [t36, t75, t135, t175, t213, t225, t248], []),
  (3, [t45, t101, t135, t170, t175, t213, t248], []),
  (3, [t66, t75, t101, t135, t175, t238, t248], [380431, 260351, 940143]),
  (3, [t75, t92, t101, t158, t175, t213, t248], []),
  (3, [t75, t101, t124, t175, t197, t213, t248], []),
  (3, [t75, t101, t135, t169, t213, t238, t248], []),
  (3, [t75, t101, t135, t175, t213, t217, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t267], []),
  (3, [t75, t96, t101, t135, t175, t224], [])]

def fam19 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t88, t101, t135, t175, t213, t248], [290104, 10007, 890549, 890452, 890371, 890290, 700648, 680634, 740010, 740092, 540154, 940445, 940170, 540222, 700202, 540186]),
  (2, [t75, t101, t116, t135, t175, t213], []),
  (3, [t5, t75, t92, t101, t135, t175, t213], []),
  (3, [t12, t66, t75, t101, t135, t175, t248], []),
  (3, [t18, t19, t75, t101, t135, t213, t248], []),
  (3, [t23, t27, t75, t101, t175, t213, t248], []),
  (3, [t27, t75, t101, t175, t213, t248, t270], []),
  (3, [t36, t75, t135, t175, t213, t231, t248], []),
  (3, [t45, t101, t135, t175, t180, t213, t248], []),
  (3, [t66, t75, t101, t135, t185, t213, t248], []),
  (3, [t75, t92, t135, t175, t197, t213, t248], [860511, 860255]),
  (3, [t75, t101, t125, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t171, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t218, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t268], []),
  (3, [t75, t101, t113, t163, t175, t248], [])]

def fam20 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t92, t101, t135, t175, t213, t248], [490120, 850471, 210023, 90565, 90468, 90387, 90306, 300009, 480043, 940249, 940026, 340577, 940140, 620298, 540154, 340636, 140250, 740238, 140058, 740314, 500266, 940282]),
  (2, [t75, t101, t124, t175, t213, t248], [280447, 780479, 300255, 940335]),
  (3, [t5, t75, t96, t101, t135, t175, t213], []),
  (3, [t12, t70, t75, t101, t135, t175, t248], []),
  (3, [t18, t75, t101, t135, t175, t213, t248], []),
  (3, [t23, t75, t101, t135, t175, t213, t248], []),
  (3, [t27, t75, t101, t175, t213, t248, t274], []),
  (3, [t36, t75, t135, t175, t213, t238, t248], []),
  (3, [t45, t101, t135, t175, t189, t213, t248], []),
  (3, [t66, t75, t101, t147, t175, t213, t248], []),
  (3, [t75, t93, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t127, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t172, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t219, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t269], []),
  (3, [t75, t101, t124, t175, t234, t248], [])]

def fam21 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t96, t101, t135, t175, t213, t248], [890136, 50455, 610039, 490581, 490484, 490403, 490322, 500025, 80107, 340409, 340042, 340188, 940170, 140529, 740029, 820410, 140250, 540493, 340394]),
  (2, [t75, t101, t135, t153, t213, t248], [460207]),
  (3, [t5, t75, t101, t102, t135, t175, t213], []),
  (3, [t12, t75, t77, t101, t135, t175, t248], []),
  (3, [t19, t54, t75, t101, t135, t213, t248], []),
  (3, [t24, t27, t75, t101, t175, t213, t248], []),
  (3, [t28, t75, t101, t135, t175, t213, t248], []),
  (3, [t36, t75, t135, t175, t213, t244, t248], []),
  (3, [t45, t101, t135, t175, t197, t213, t248], []),
  (3, [t66, t75, t115, t135, t175, t213, t248], []),
  (3, [t75, t94, t101, t135, t175, t213, t248], [340577, 740433]),
  (3, [t75, t101, t128, t135, t175, t213, t248], [740433]),
  (3, [t75, t101, t135, t173, t175, t213, t248], [860385]),
  (3, [t75, t101, t135, t175, t213, t220, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t271], []),
  (3, [t75, t101, t135, t175, t238, t257], [])]

def fam22 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t119, t135, t175, t213, t248], [430168, 150055, 870374, 30613, 30516, 30435, 30354, 200057, 80122, 680031, 280047, 480063, 980570, 880204, 380618, 480045, 580289, 180027, 800011, 680509, 180305, 780091, 400075, 80254]),
  (2, [t75, t101, t135, t169, t213, t248], []),
  (3, [t5, t75, t101, t119, t135, t175, t213], []),
  (3, [t12, t75, t84, t101, t135, t175, t248], []),
  (3, [t19, t58, t75, t101, t135, t213, t248], []),
  (3, [t24, t75, t101, t135, t175, t213, t248], []),
  (3, [t29, t75, t101, t135, t175, t213, t248], []),
  (3, [t36, t75, t135, t175, t213, t248, t252], []),
  (3, [t45, t101, t135, t175, t205, t213, t248], []),
  (3, [t67, t75, t101, t135, t175, t213, t248], [580609]),
  (3, [t75, t94, t135, t175, t213, t238, t248], []),
  (3, [t75, t101, t129, t135, t175, t213, t248], [860449]),
  (3, [t75, t101, t135, t174, t175, t213, t248], [860401]),
  (3, [t75, t101, t135, t175, t213, t221, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t272], []),
  (3, [t75, t101, t152, t158, t213, t248], [])]

def fam23 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t122, t135, t175, t213, t248], [10184, 730071, 10358, 610629, 610532, 610451, 610370, 860073, 460002, 260111, 760571, 160219, 740010, 940641, 740079, 700076, 820074, 20186, 260139, 860449, 460525, 660203, 260155, 860385, 460270, 660187, 460251, 260171, 460235]),
  (2, [t75, t101, t135, t175, t213, t257], [820239, 860351]),
  (3, [t5, t75, t101, t122, t135, t175, t213], []),
  (3, [t12, t75, t88, t101, t135, t175, t248], []),
  (3, [t19, t62, t75, t101, t135, t213, t248], []),
  (3, [t25, t27, t75, t101, t175, t213, t248], []),
  (3, [t30, t75, t101, t135, t175, t213, t248], []),
  (3, [t36, t75, t135, t175, t213, t248, t258], []),
  (3, [t45, t101, t135, t175, t208, t213, t248], []),
  (3, [t68, t75, t101, t135, t175, t213, t248], [460545]),
  (3, [t75, t95, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t130, t135, t175, t237, t248], []),
  (3, [t75, t101, t135, t175, t176, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t222, t248], [460417]),
  (3, [t75, t101, t135, t175, t213, t248, t273], []),
  (3, [t75, t101, t162, t175, t226, t248], [])]

def fam24 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t126, t135, t175, t213, t248], [10200, 730087, 610645, 610548, 610467, 610386, 860089, 760619, 940026, 500124, 260139, 460093, 260315, 460286]),
  (2, [t75, t101, t135, t175, t213, t264], []),
  (3, [t5, t75, t101, t126, t135, t175, t213], []),
  (3, [t12, t75, t92, t101, t135, t175, t248], []),
  (3, [t19, t66, t75, t101, t135, t213, t248], []),
  (3, [t25, t75, t101, t135, t175, t213, t248], []),
  (3, [t31, t36, t75, t135, t175, t213, t248], []),
  (3, [t36, t75, t135, t175, t213, t248, t262], []),
  (3, [t45, t101, t135, t175, t213, t218, t248], []),
  (3, [t69, t75, t101, t135, t175, t213, t248], [460497]),
  (3, [t75, t96, t101, t135, t175, t213, t274], []),
  (3, [t75, t101, t131, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t177, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t223, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t275], []),
  (3, [t75, t113, t115, t135, t175, t248], [])]

def fam25 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t130, t135, t175, t213, t248], [10216, 730103, 10342, 610006, 610564, 610483, 610402, 860105, 760012, 340042, 100172, 260155, 460141, 260315, 860465, 460573, 660379]),
  (2, [t75, t101, t135, t175, t213, t269], []),
  (3, [t5, t75, t101, t130, t135, t175, t213], []),
  (3, [t12, t75, t96, t101, t135, t175, t248], []),
  (3, [t19, t70, t75, t101, t135, t213, t248], []),
  (3, [t26, t27, t75, t101, t175, t213, t248], []),
  (3, [t31, t75, t101, t135, t175, t213, t248], []),
  (3, [t36, t75, t135, t175, t213, t248, t266], []),
  (3, [t45, t101, t135, t175, t213, t225, t248], []),
  (3, [t70, t75, t96, t101, t135, t175, t213], [180305, 540303, 580191, 940175]),
  (3, [t75, t96, t101, t135, t196, t213, t248], []),
  (3, [t75, t101, t132, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t178, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t224, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t276], []),
  (3, [t75, t113, t135, t175, t197, t248], [140527])]

def fam26 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t151, t175, t213, t248], [710248, 430135, 310022, 310596, 310515, 310434, 160127, 460138, 880204, 160638, 160654, 460555, 160157, 460603, 160589, 460651, 160302]),
  (2, [t75, t101, t135, t175, t224, t248], [620303]),
  (3, [t5, t75, t101, t135, t136, t175, t213], []),
  (3, [t12, t75, t101, t103, t135, t175, t248], []),
  (3, [t19, t75, t78, t101, t135, t213, t248], []),
  (3, [t26, t75, t101, t135, t175, t213, t248], []),
  (3, [t32, t36, t75, t135, t175, t213, t248], []),
  (3, [t36, t75, t135, t175, t213, t248, t270], []),
  (3, [t45, t101, t135, t175, t213, t231, t248], []),
  (3, [t70, t75, t101, t135, t175, t213, t258], []),
  (3, [t75, t97, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t133, t135, t175, t213, t248], [860385]),
  (3, [t75, t101, t135, t175, t179, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t226, t248], [140273]),
  (3, [t75, t101, t135, t175, t213, t248, t277], []),
  (3, [t75, t115, t135, t175, t238, t248], [])]

def fam27 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t162, t175, t213, t248], [90264, 810151, 690038, 650261, 690612, 690531, 690450, 100121, 880204, 900106, 340095, 540015, 540337, 140060, 420044, 940173, 340108, 740605, 740156, 340318]),
  (2, [t75, t101, t135, t175, t226, t248], [480463, 860383]),
  (3, [t5, t75, t101, t135, t151, t175, t213], []),
  (3, [t12, t75, t101, t119, t135, t175, t248], []),
  (3, [t19, t75, t84, t101, t135, t213, t248], []),
  (3, [t27, t54, t75, t101, t175, t213, t248], []),
  (3, [t32, t75, t101, t135, t175, t213, t248], []),
  (3, [t36, t75, t135, t175, t213, t248, t274], []),
  (3, [t45, t101, t135, t175, t213, t238, t248], []),
  (3, [t70, t75, t101, t135, t175, t213, t270], []),
  (3, [t75, t98, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t134, t135, t175, t213, t248], [860465]),
  (3, [t75, t101, t135, t175, t180, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t227, t248], []),
  (3, [t75, t101, t135, t175, t213, t248, t278], []),
  (3, [t75, t119, t124, t175, t213, t248], [660527])]

def fam28 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t166, t175, t213, t248], [10280, 730167, 610054, 10245, 610628, 610547, 610466, 860137, 760508, 540154, 900620, 260139, 460077, 260171, 260220, 860401, 460334, 660236]),
  (2, [t75, t101, t135, t175, t233, t248], []),
  (3, [t5, t75, t101, t135, t162, t175, t213], []),
  (3, [t12, t75, t101, t122, t135, t175, t248], []),
  (3, [t19, t75, t88, t101, t135, t213, t248], []),
  (3, [t27, t58, t75, t101, t175, t213, t248], []),
  (3, [t33, t36, t75, t135, t175, t213, t248], []),
  (3, [t37, t75, t101, t135, t175, t213, t248], []),
  (3, [t45, t101, t135, t175, t213, t244, t248], []),
  (3, [t70, t75, t101, t135, t175, t224, t248], []),
  (3, [t75, t99, t101, t135, t175, t213, t248], [140529]),
  (3, [t75, t101, t135, t136, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t181, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t228, t248], []),
  (3, [t75, t101, t135, t175, t213, t258, t274], [460369]),
  (3, [t75, t119, t135, t175, t226, t248], [])]

def fam29 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t170, t175, t213, t248], [10296, 730183, 610070, 610644, 610563, 610482, 860153, 760556, 940170, 500013, 260155, 460125, 260220, 460653]),
  (2, [t75, t101, t135, t175, t237, t248], []),
  (3, [t5, t75, t101, t135, t166, t175, t213], []),
  (3, [t12, t75, t101, t126, t135, t175, t248], []),
  (3, [t19, t75, t92, t101, t135, t213, t248], []),
  (3, [t27, t62, t75, t101, t175, t213, t248], []),
  (3, [t33, t75, t101, t135, t175, t213, t248], []),
  (3, [t38, t75, t101, t135, t175, t213, t248], []),
  (3, [t45, t101, t135, t175, t213, t248, t253], []),
  (3, [t70, t75, t101, t135, t188, t213, t248], []),
  (3, [t75, t100, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t137, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t182, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t229, t248], []),
  (3, [t75, t101, t135, t175, t213, t266, t270], [860385]),
  (3, [t75, t124, t154, t175, t213, t248], [])]

def fam30 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t189, t213, t248], [710328, 430215, 310102, 310005, 310595, 310514, 160127, 160169, 120574, 860218, 480045, 960219, 460267, 160157, 160590, 160606, 460492, 160014, 460540, 160350]),
  (2, [t75, t101, t135, t181, t213, t248], []),
  (3, [t5, t75, t101, t135, t170, t175, t213], []),
  (3, [t12, t75, t101, t130, t135, t175, t248], []),
  (3, [t19, t75, t96, t101, t135, t213, t248], []),
  (3, [t27, t66, t75, t101, t175, t213, t248], []),
  (3, [t34, t36, t75, t135, t175, t213, t248], []),
  (3, [t39, t75, t101, t135, t175, t213, t248], []),
  (3, [t45, t101, t135, t175, t213, t248, t258], []),
  (3, [t70, t75, t101, t150, t175, t213, t248], []),
  (3, [t75, t101, t102, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t138, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t183, t213, t248], [460497]),
  (3, [t75, t101, t135, t175, t213, t230, t248], []),
  (3, [t75, t101, t135, t175, t213, t270, t274], [860401]),
  (3, [t75, t154, t175, t213, t238, t248], [])]

def fam31 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t197, t213, t248], [490344, 210231, 90118, 90021, 850164, 90611, 90530, 720031, 640574, 300201, 480045, 940095, 500202, 740314, 340321, 620299, 940283, 940173, 940622, 740604, 140030, 140652, 740366]),
  (2, [t75, t101, t135, t185, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t176, t213], []),
  (3, [t12, t75, t101, t135, t137, t175, t248], []),
  (3, [t19, t75, t101, t104, t135, t213, t248], []),
  (3, [t27, t70, t75, t101, t175, t213, t248], []),
  (3, [t34, t75, t101, t135, t175, t213, t248], []),
  (3, [t40, t45, t101, t135, t175, t213, t248], []),
  (3, [t45, t101, t135, t175, t213, t248, t262], []),
  (3, [t70, t75, t118, t135, t175, t213, t248], []),
  (3, [t75, t101, t103, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t139, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t184, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t232, t248], []),
  (3, [t75, t101, t135, t175, t225, t248, t274], [460417]),
  (3, [t75, t158, t175, t197, t213, t248], [])]

def fam32 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t205, t213, t248], [610360, 330247, 210134, 210037, 210627, 210546, 660217, 160157, 700234, 940173, 860061, 60046, 860109, 60382]),
  (2, [t75, t101, t135, t188, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t189, t213], []),
  (3, [t12, t75, t101, t135, t151, t175, t248], []),
  (3, [t19, t75, t101, t119, t135, t213, t248], []),
  (3, [t27, t75, t79, t101, t175, t213, t248], []),
  (3, [t35, t36, t75, t135, t175, t213, t248], []),
  (3, [t40, t75, t101, t135, t175, t213, t248], []),
  (3, [t45, t101, t135, t175, t213, t248, t266], []),
  (3, [t71, t75, t101, t135, t175, t213, t248], [380625]),
  (3, [t75, t101, t104, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t140, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t185, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t233, t248], [260353]),
  (3, [t75, t101, t135, t175, t231, t238, t248], [740433]),
  (3, [t75, t113, t124, t175, t248], [])]

def fam33 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t208, t213, t248], [10376, 730263, 610150, 610053, 610643, 610562, 860233, 760397, 140250, 300477, 260315, 460557, 260220, 460637]),
  (2, [t75, t101, t135, t196, t213, t248], [900175]),
  (3, [t5, t75, t101, t135, t175, t197, t213], []),
  (3, [t12, t75, t101, t135, t162, t175, t248], []),
  (3, [t19, t75, t101, t122, t135, t213, t248], []),
  (3, [t27, t75, t84, t101, t175, t213, t248], []),
  (3, [t35, t75, t101, t135, t175, t213, t248], []),
  (3, [t41, t45, t101, t135, t175, t213, t248], []),
  (3, [t45, t101, t135, t175, t213, t248, t270], []),
  (3, [t72, t75, t101, t135, t175, t213, t248], [460561]),
  (3, [t75, t101, t105, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t141, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t186, t213, t248], [460513]),
  (3, [t75, t101, t135, t175, t213, t235, t248], [860465]),
  (3, [t75, t101, t135, t175, t238, t244, t248], [860449])]

def fam34 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t213, t225, t248], [710408, 430295, 310182, 310085, 310004, 310594, 160281, 660330, 680509, 460331, 160589, 460252, 160014, 160510, 460381, 160398]),
  (2, [t75, t101, t147, t175, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t205, t213], []),
  (3, [t12, t75, t101, t135, t166, t175, t248], []),
  (3, [t19, t75, t101, t126, t135, t213, t248], []),
  (3, [t27, t75, t88, t101, t175, t213, t248], []),
  (3, [t36, t54, t75, t135, t175, t213, t248], []),
  (3, [t41, t75, t101, t135, t175, t213, t248], []),
  (3, [t45, t101, t135, t175, t213, t248, t274], []),
  (3, [t73, t75, t101, t135, t175, t213, t248], [460513]),
  (3, [t75, t101, t106, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t142, t175, t213, t248], [460002]),
  (3, [t75, t101, t135, t175, t187, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t236, t248], []),
  (3, [t75, t101, t135, t175, t238, t248, t274], [860465])]

def fam35 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t213, t231, t248], [290424, 10311, 890198, 890101, 890020, 890610, 520047, 700361, 680509, 700266, 740526, 740347, 740605, 340268, 140030, 940461, 540414]),
  (2, [t75, t101, t150, t175, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t208, t213], []),
  (3, [t12, t75, t101, t135, t170, t175, t248], []),
  (3, [t19, t75, t101, t130, t135, t213, t248], []),
  (3, [t27, t75, t92, t101, t175, t213, t248], []),
  (3, [t36, t58, t75, t135, t175, t213, t248], []),
  (3, [t42, t45, t101, t135, t175, t213, t248], []),
  (3, [t46, t75, t101, t135, t175, t213, t248], []),
  (3, [t74, t75, t101, t135, t175, t213, t248], [460417, 460369]),
  (3, [t75, t101, t107, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t143, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t188, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t237, t248], []),
  (3, [t75, t101, t135, t189, t197, t213, t248], [100481])]

def fam36 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t213, t238, t248], [610440, 330327, 210214, 210117, 210036, 810083, 210626, 760638, 60297, 660377, 160589, 220015, 620526, 140273, 540362, 900346, 740605, 860251, 60542, 260353, 660300, 860284, 60046, 60558, 860541, 60430]),
  (2, [t75, t101, t158, t175, t213, t248], [500159, 980287, 300511, 540367]),
  (3, [t5, t75, t101, t135, t175, t213, t214], []),
  (3, [t12, t75, t101, t135, t175, t177, t248], []),
  (3, [t19, t75, t101, t135, t138, t213, t248], []),
  (3, [t27, t75, t96, t101, t175, t213, t248], []),
  (3, [t36, t62, t75, t135, t175, t213, t248], []),
  (3, [t42, t75, t101, t135, t175, t213, t248], []),
  (3, [t47, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t76, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t108, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t144, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t190, t213, t248], [340321]),
  (3, [t75, t101, t135, t175, t213, t239, t248], []),
  (3, [t75, t101, t135, t189, t213, t244, t248], [460497])]

def fam37 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t213, t244, t248], [610456, 330343, 210230, 210133, 210052, 210642, 760590, 660393, 160014, 500378, 140030, 60542, 860363, 60046, 860621, 60446]),
  (2, [t75, t112, t135, t175, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t213, t225], []),
  (3, [t12, t75, t101, t135, t175, t189, t248], []),
  (3, [t19, t75, t101, t135, t151, t213, t248], []),
  (3, [t27, t75, t101, t105, t175, t213, t248], []),
  (3, [t36, t66, t75, t135, t175, t213, t248], []),
  (3, [t43, t45, t101, t135, t175, t213, t248], []),
  (3, [t48, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t77, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t109, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t145, t175, t213, t248], [460545]),
  (3, [t75, t101, t135, t175, t191, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t240, t248], []),
  (3, [t75, t101, t135, t189, t213, t248, t270], [460513])]

def fam38 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t213, t248, t258], [710488, 430375, 310262, 310165, 310084, 310003, 160425, 260426, 80254, 460395, 160302, 460316, 160350, 160462, 460189, 160398]),
  (2, [t75, t115, t135, t175, t213, t248], [460399, 540431]),
  (3, [t5, t75, t101, t135, t175, t213, t231], []),
  (3, [t12, t75, t101, t135, t175, t197, t248], []),
  (3, [t19, t75, t101, t135, t162, t213, t248], []),
  (3, [t27, t75, t101, t119, t175, t213, t248], []),
  (3, [t36, t70, t75, t135, t175, t213, t248], []),
  (3, [t43, t75, t101, t135, t175, t213, t248], []),
  (3, [t49, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t78, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t110, t135, t175, t213, t248], [180593]),
  (3, [t75, t101, t135, t146, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t192, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t241, t248], []),
  (3, [t75, t101, t135, t197, t213, t248, t270], [140529])]

def fam39 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t213, t248, t262], [890504, 610391, 490278, 490181, 490100, 490019, 120063, 500521, 80254, 340411, 340318, 940332, 740366, 140205, 540414]),
  (2, [t75, t118, t135, t175, t213, t248], []),
  (3, [t5, t75, t101, t135, t175, t213, t238], []),
  (3, [t12, t75, t101, t135, t175, t205, t248], []),
  (3, [t19, t75, t101, t135, t166, t213, t248], []),
  (3, [t27, t75, t101, t122, t175, t213, t248], []),
  (3, [t36, t75, t80, t135, t175, t213, t248], []),
  (3, [t44, t45, t101, t135, t175, t213, t248], []),
  (3, [t50, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t79, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t111, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t147, t175, t213, t248], []),
  (3, [t75, t101, t135, t175, t193, t213, t248], []),
  (3, [t75, t101, t135, t175, t213, t242, t248], []),
  (3, [t75, t101, t151, t175, t213, t238, t248], [460545])]

def fam40 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t75, t101, t135, t175, t213, t248, t266], [610520, 330407, 210294, 210197, 210116, 210035, 760654, 660537, 160302, 300442, 340318, 60478, 860348, 60382, 860221, 60430]),
  (2, [t75, t135, t154, t175, t213, t248], [300479, 620495]),
  (3, [t5, t75, t101, t135, t175, t213, t244], []),
  (3, [t12, t75, t101, t135, t175, t208, t248], []),
  (3, [t19, t75, t101, t135, t170, t213, t248], []),
  (3, [t27, t75, t101, t126, t175, t213, t248], []),
  (3, [t36, t75, t84, t135, t175, t213, t248], []),
  (3, [t44, t75, t101, t135, t175, t213, t248], []),
  (3, [t51, t75, t101, t135, t175, t213, t248], []),
  (3, [t75, t80, t101, t135, t175, t213, t248], []),
  (3, [t75, t101, t112, t135, t175, t213, t248], []),
  (3, [t75, t101, t135, t148, t175, t213, t248], [460561]),
  (3, [t75, t101, t135, t175, t194, t213, t248], [140529]),
  (3, [t75, t101, t135, t175, t213, t243, t248], []),
  (3, [t75, t101, t151, t175, t213, t248, t266], [460561])]

def chunk0 : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19]

def chunk1 : List (List (ℕ × List ℕ × List ℕ)) := [fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39]

def chunk2 : List (List (ℕ × List ℕ × List ℕ)) := [fam40]

def parts : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19,
  fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39,
  fam40]

set_option maxRecDepth 8000 in
theorem parts_eq : parts = chunk0 ++ chunk1 ++ chunk2 := rfl

set_option synthInstance.maxSize 4000 in
def okB (e : ℕ × List ℕ × List ℕ) : Bool := decide (OkEntry tab zs 4 parts perms e)

set_option synthInstance.maxSize 4000 in
theorem okB_ok (e : ℕ × List ℕ × List ℕ) (h : okB e = true) : OkEntry tab zs 4 parts perms e := by
  unfold okB at h
  exact of_decide_eq_true h

theorem ok0 : fam0.all okB = true := by decide +kernel

theorem ok1 : fam1.all okB = true := by decide +kernel

theorem ok2 : fam2.all okB = true := by decide +kernel

theorem ok3 : fam3.all okB = true := by decide +kernel

theorem ok4 : fam4.all okB = true := by decide +kernel

theorem ok5 : fam5.all okB = true := by decide +kernel

theorem ok6 : fam6.all okB = true := by decide +kernel

theorem ok7 : fam7.all okB = true := by decide +kernel

theorem ok8 : fam8.all okB = true := by decide +kernel

theorem ok9 : fam9.all okB = true := by decide +kernel

theorem ok10 : fam10.all okB = true := by decide +kernel

theorem ok11 : fam11.all okB = true := by decide +kernel

theorem ok12 : fam12.all okB = true := by decide +kernel

theorem ok13 : fam13.all okB = true := by decide +kernel

theorem ok14 : fam14.all okB = true := by decide +kernel

theorem ok15 : fam15.all okB = true := by decide +kernel

theorem ok16 : fam16.all okB = true := by decide +kernel

theorem ok17 : fam17.all okB = true := by decide +kernel

theorem ok18 : fam18.all okB = true := by decide +kernel

theorem ok19 : fam19.all okB = true := by decide +kernel

theorem ok20 : fam20.all okB = true := by decide +kernel

theorem ok21 : fam21.all okB = true := by decide +kernel

theorem ok22 : fam22.all okB = true := by decide +kernel

theorem ok23 : fam23.all okB = true := by decide +kernel

theorem ok24 : fam24.all okB = true := by decide +kernel

theorem ok25 : fam25.all okB = true := by decide +kernel

theorem ok26 : fam26.all okB = true := by decide +kernel

theorem ok27 : fam27.all okB = true := by decide +kernel

theorem ok28 : fam28.all okB = true := by decide +kernel

theorem ok29 : fam29.all okB = true := by decide +kernel

theorem ok30 : fam30.all okB = true := by decide +kernel

theorem ok31 : fam31.all okB = true := by decide +kernel

theorem ok32 : fam32.all okB = true := by decide +kernel

theorem ok33 : fam33.all okB = true := by decide +kernel

theorem ok34 : fam34.all okB = true := by decide +kernel

theorem ok35 : fam35.all okB = true := by decide +kernel

theorem ok36 : fam36.all okB = true := by decide +kernel

theorem ok37 : fam37.all okB = true := by decide +kernel

theorem ok38 : fam38.all okB = true := by decide +kernel

theorem ok39 : fam39.all okB = true := by decide +kernel

theorem ok40 : fam40.all okB = true := by decide +kernel

theorem okc0 : ∀ part ∈ chunk0, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok0 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok1 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok2 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok3 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok4 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok5 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok6 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok7 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok8 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok9 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok10 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok11 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok12 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok13 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok14 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok15 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok16 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok17 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok18 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok19 e he)

theorem okc1 : ∀ part ∈ chunk1, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk1, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok20 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok21 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok22 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok23 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok24 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok25 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok26 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok27 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok28 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok29 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok30 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok31 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok32 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok33 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok34 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok35 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok36 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok37 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok38 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok39 e he)

theorem okc2 : ∀ part ∈ chunk2, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk2, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact fun e he => okB_ok e (List.all_eq_true.mp ok40 e he)

set_option maxRecDepth 8000 in
theorem ok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  rw [parts_eq] at hp
  simp only [List.mem_append] at hp
  rcases hp with (h | h) | h
  · exact okc0 part h
  · exact okc1 part h
  · exact okc2 part h

theorem perms_ok : ∀ π ∈ perms, PermOk tab π := by decide +kernel

theorem tab_lt : tab < 2 ^ 64 := by decide +kernel

theorem tab_one : ∃ p : Fin 64, tab.testBit p = true := by decide +kernel

theorem tab_zero : ∃ q : Fin 64, tab.testBit q = false := by decide +kernel

theorem zs_ok : ∀ q ∈ zs, q < 64 ∧ tab.testBit q = false := by decide +kernel

theorem pool_eq : pool0 = base ++ [0, ALL] := by decide +kernel

theorem nec : ∀ a ∈ base, ¬ GoodL tab zs (base.filter (fun x => decide (x ≠ a))) := by
  decide +kernel

theorem base_mem : ∃ e ∈ parts.flatten, e.1 = 0 ∧ e.2.1 = base :=
  ⟨(0, base, [210096, 510192, 930080, 690176, 810064, 410160, 810048, 410144, 810032, 410128, 810016, 410112, 740208, 200352, 260224, 960416, 260240, 960480, 260256, 960544, 260272, 960608, 620288, 420432, 820304, 220496, 220320, 820560, 20336, 20624, 60368, 260512, 60384, 260576, 60400, 260640, 60448, 260592, 60464, 260001, 60528, 260017]), by decide +kernel, rfl, rfl⟩

theorem base_len : base.length = 6 := by decide +kernel

theorem base_nd : base.Nodup := by decide +kernel

theorem tab_eq : ∀ p : Fin 64, (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272615552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (fun i : Fin 6 => p.val.testBit i.val) =
    tab.testBit p.val := by
  decide +kernel

def upper : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩,
   ⟨GateOp.and, [1, 4]⟩,
   ⟨GateOp.and, [1, 6]⟩,
   ⟨GateOp.or, [4, 5]⟩,
   ⟨GateOp.and, [0, 9]⟩,
   ⟨GateOp.or, [3, 8]⟩,
   ⟨GateOp.or, [2, 7]⟩,
   ⟨GateOp.and, [11, 12]⟩,
   ⟨GateOp.or, [10, 13]⟩], 14⟩

theorem upper_mono : Monotone2 upper := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_size : upper.size = 9 := rfl

theorem upper_eval : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) =
    Nat.testBit (4277074666 * 2 ^ 32 + 4272615552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_16927

theorem PEqualNP.Outside.L_meta_16927 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4272615552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4272615552) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro t ⟨C, hC, hs, hev⟩
  have h := PEqualNP.Outside.L_meta_16927.lower PEqualNP.Outside.L_meta_16927.tab 6 4 PEqualNP.Outside.L_meta_16927.parts PEqualNP.Outside.L_meta_16927.perms PEqualNP.Outside.L_meta_16927.zs PEqualNP.Outside.L_meta_16927.base PEqualNP.Outside.L_meta_16927.tab_lt
    PEqualNP.Outside.L_meta_16927.tab_one PEqualNP.Outside.L_meta_16927.tab_zero PEqualNP.Outside.L_meta_16927.zs_ok PEqualNP.Outside.L_meta_16927.perms_ok PEqualNP.Outside.L_meta_16927.ok PEqualNP.Outside.L_meta_16927.pool_eq
    PEqualNP.Outside.L_meta_16927.nec PEqualNP.Outside.L_meta_16927.base_mem PEqualNP.Outside.L_meta_16927.base_len PEqualNP.Outside.L_meta_16927.base_nd
    C hC (fun p => (hev _).trans (PEqualNP.Outside.L_meta_16927.tab_eq p))
  have hs' : C.gates.length ≤ t := hs
  have hu : PEqualNP.Outside.L_meta_16927.upper.size = 9 := PEqualNP.Outside.L_meta_16927.upper_size
  exact ⟨PEqualNP.Outside.L_meta_16927.upper, PEqualNP.Outside.L_meta_16927.upper_mono, by omega, PEqualNP.Outside.L_meta_16927.upper_eval⟩
