import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16661
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
  (w % 10000) / 16 < parts.length ∧
    (w % 10000) % 16 < (parts.getD ((w % 10000) / 16) []).length ∧
    (w / 10000) % 10 < perms.length ∧ (ent parts (w % 10000)).1 ≤ lv ∧
    (if (w / 10000) % 10 = 0 then (ent parts (w % 10000)).2.1
      else ((ent parts (w % 10000)).2.1.map (app (perms.getD ((w / 10000) % 10) []))).insertionSort
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
  w / 100000 = (c + 3 * E.sum) % 100 ∧ hit2B parts perms lv E c w = true

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
    have hmem : ent parts (w % 10000) ∈ parts.flatten := by
      refine List.mem_flatten.mpr ⟨parts.getD ((w % 10000) / 16) [], ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hp1]
        exact List.getElem_mem hp1
      · unfold ent
        rw [List.getD_eq_getElem _ _ hp2]
        exact List.getElem_mem hp2
    by_cases h0 : (w / 10000) % 10 = 0
    · rw [if_pos h0] at heq
      refine ⟨ent parts (w % 10000), hmem, le_trans hlv' hle, fun x => x, sym_id T, ?_⟩
      rw [Finset.image_id', heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _),
        hcons]
    · rw [if_neg h0] at heq
      refine ⟨ent parts (w % 10000), hmem, le_trans hlv' hle,
        app (perms.getD ((w / 10000) % 10) []), sym_app T _ (hperm _ ?_), ?_⟩
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

def tab : ℕ := 18368754515636710624

def zs : List ℕ := [0, 1, 2, 3, 4, 8, 9, 12, 16, 17, 18, 19, 20, 24, 32, 33, 34, 36, 40, 41, 44, 48, 50, 52, 56]

def t0 : ℕ := 16711935
def t1 : ℕ := 252645135
def t2 : ℕ := 1431655765
def t3 : ℕ := 2863311530
def t4 : ℕ := 3435973836
def t5 : ℕ := 4042322160
def t6 : ℕ := 4278255360
def t7 : ℕ := 4294901760
def t8 : ℕ := 4294967295
def t9 : ℕ := 56294136361779
def t10 : ℕ := 56298431315967
def t11 : ℕ := 93823560602965
def t12 : ℕ := 187647121205930
def t13 : ℕ := 225176545447116
def t14 : ℕ := 264913582878960
def t15 : ℕ := 280375465148160
def t16 : ℕ := 281470681743360
def t17 : ℕ := 281470681808895
def t18 : ℕ := 4222189076152335
def t19 : ℕ := 23925738098196565
def t20 : ℕ := 23925738109337855
def t21 : ℕ := 23981959231255551
def t22 : ℕ := 47851476185251840
def t23 : ℕ := 47851476196393130
def t24 : ℕ := 57421771435671756
def t25 : ℕ := 67555025218437360
def t26 : ℕ := 71776119077928960
def t27 : ℕ := 71777214277877760
def t28 : ℕ := 71777214294589695
def t29 : ℕ := 71777218572845055
def t30 : ℕ := 71833289387619327
def t31 : ℕ := 72057589759737855
def t32 : ℕ := 361700864190383365
def t33 : ℕ := 723401728212336640
def t34 : ℕ := 723401728380766730
def t35 : ℕ := 868082074056920076
def t36 : ℕ := 1080880403494997760
def t37 : ℕ := 1085086035472220160
def t38 : ℕ := 1085102592318504960
def t39 : ℕ := 1085102592571150095
def t40 : ℕ := 1085102596613472255
def t41 : ℕ := 1085367506154029055
def t42 : ℕ := 1152657617789587455
def t43 : ℕ := 1229782938247303441
def t44 : ℕ := 2459565876494606882
def t45 : ℕ := 3472328296227680304
def t46 : ℕ := 3674993371882992384
def t47 : ℕ := 3689292520605548544
def t48 : ℕ := 3689348813882916864
def t49 : ℕ := 3689348814741910323
def t50 : ℕ := 3689348818177884159
def t51 : ℕ := 3689573991287357439
def t52 : ℕ := 3746770586177582079
def t53 : ℕ := 4557430888798830399
def t54 : ℕ := 4919131752989213764
def t55 : ℕ := 5787213827046133840
def t56 : ℕ := 6124988953138320640
def t57 : ℕ := 6124988955990490880
def t58 : ℕ := 6148820867675914240
def t59 : ℕ := 6148914689804861440
def t60 : ℕ := 6148914691236517205
def t61 : ℕ := 6148914694099828735
def t62 : ℕ := 6149102338357723135
def t63 : ℕ := 6196766167432910335
def t64 : ℕ := 6872316419617283935
def t65 : ℕ := 8608480567731124087
def t66 : ℕ := 9259542123273814144
def t67 : ℕ := 9799982325021313024
def t68 : ℕ := 9838113388281462784
def t69 : ℕ := 9838263503687778304
def t70 : ℕ := 9838263505978427528
def t71 : ℕ := 11529390970613309440
def t72 : ℕ := 11574251045037015040
def t73 : ℕ := 11574427651397386240
def t74 : ℕ := 11574427654092267680
def t75 : ℕ := 12153149036796881064
def t76 : ℕ := 12249790989299875840
def t77 : ℕ := 12249977903424471040
def t78 : ℕ := 12249977906276641280
def t79 : ℕ := 12288259087233755784
def t80 : ℕ := 12295014589755599520
def t81 : ℕ := 12297641732488560640
def t82 : ℕ := 12297641735351828480
def t83 : ℕ := 12297791850185490432
def t84 : ℕ := 12297791853048793224
def t85 : ℕ := 12297818344407081120
def t86 : ℕ := 12297827174859843752
def t87 : ℕ := 12297828652328593920
def t88 : ℕ := 12297829379609722880
def t89 : ℕ := 12297829381765628032
def t90 : ℕ := 12297829381891459072
def t91 : ℕ := 12297829381900372104
def t92 : ℕ := 12297829382294118400
def t93 : ℕ := 12297829382304563200
def t94 : ℕ := 12297829382304604320
def t95 : ℕ := 12297829382461849600
def t96 : ℕ := 12297829382461893120
def t97 : ℕ := 12297829382472379040
def t98 : ℕ := 12297829382472990720
def t99 : ℕ := 12297829382473034410
def t100 : ℕ := 12297829383904690175
def t101 : ℕ := 12297923206033637375
def t102 : ℕ := 12321755120571230975
def t103 : ℕ := 12659530246663417775
def t104 : ℕ := 13527612320720337851
def t105 : ℕ := 13835269164735971328
def t106 : ℕ := 13889101254044418048
def t107 : ℕ := 13889313181676863488
def t108 : ℕ := 13889313184910721216
def t109 : ℕ := 14468034567615334600
def t110 : ℕ := 14699749187159851008
def t111 : ℕ := 14699973484109365248
def t112 : ℕ := 14699973487531969536
def t113 : ℕ := 14738254668480171008
def t114 : ℕ := 14738254668489084040
def t115 : ℕ := 14754017507706719424
def t116 : ℕ := 14756269341880143040
def t117 : ℕ := 14757170078986272768
def t118 : ℕ := 14757170082422194176
def t119 : ℕ := 14757320200119158920
def t120 : ℕ := 14757382013288497344
def t121 : ℕ := 14757394382794312704
def t122 : ℕ := 14757395255531667456
def t123 : ℕ := 14757395257822316680
def t124 : ℕ := 14757395258765525184
def t125 : ℕ := 14757395258954271744
def t126 : ℕ := 14757395258966854848
def t127 : ℕ := 14757395258967588864
def t128 : ℕ := 14757395258967641292
def t129 : ℕ := 14757395259826634751
def t130 : ℕ := 14757451553104003071
def t131 : ℕ := 14771750701826559231
def t132 : ℕ := 14974415777481871311
def t133 : ℕ := 15987178197214944733
def t134 : ℕ := 16204198715729174752
def t135 : ℕ := 16927600440168677376
def t136 : ℕ := 16927600443402535104
def t137 : ℕ := 16927600444109941482
def t138 : ℕ := 17072280789247118540
def t139 : ℕ := 17072280789786094828
def t140 : ℕ := 17149969068787297792
def t141 : ℕ := 17197820540979511296
def t142 : ℕ := 17197820544402115584
def t143 : ℕ := 17197820544983690922
def t144 : ℕ := 17207390840222969548
def t145 : ℕ := 17215835218375274218
def t146 : ℕ := 17216698429492559872
def t147 : ℕ := 17216886076613765802
def t148 : ℕ := 17216923605465353420
def t149 : ℕ := 17216923606038006988
def t150 : ℕ := 17216958927849057516
def t151 : ℕ := 17216961131453612032
def t152 : ℕ := 17216961134316923562
def t153 : ℕ := 17216961134889585868
def t154 : ℕ := 17216961135462248174
def t155 : ℕ := 17293822573129236480
def t156 : ℕ := 17294086451893370880
def t157 : ℕ := 17294086455919964160
def t158 : ℕ := 17339123139388436480
def t159 : ℕ := 17339123139398922400
def t160 : ℕ := 17348130476094714048
def t161 : ℕ := 17361376563513262080
def t162 : ℕ := 17361376567555522560
def t163 : ℕ := 17361553176610775200
def t164 : ℕ := 17361588498421825728
def t165 : ℕ := 17361640450346250240
def t166 : ℕ := 17361641477096079360
def t167 : ℕ := 17361641479790960800
def t168 : ℕ := 17361641480329937088
def t169 : ℕ := 17361641481122672640
def t170 : ℕ := 17361641481138339840
def t171 : ℕ := 17361641481138401520
def t172 : ℕ := 17361641481391046655
def t173 : ℕ := 17361658038237331455
def t174 : ℕ := 17365863670214553855
def t175 : ℕ := 17578661999652631539
def t176 : ℕ := 17723342345328784885
def t177 : ℕ := 17940362863708270832
def t178 : ℕ := 17940362863843014904
def t179 : ℕ := 18014673391583296000
def t180 : ℕ := 18062249259728240640
def t181 : ℕ := 18062524863574179840
def t182 : ℕ := 18062524867600773120
def t183 : ℕ := 18062524867779689130
def t184 : ℕ := 18082228416801733360
def t185 : ℕ := 18084767257870336000
def t186 : ℕ := 18084954904991541930
def t187 : ℕ := 18085032171284787440
def t188 : ℕ := 18085032171453214960
def t189 : ℕ := 18085041001737548016
def t190 : ℕ := 18085043205308416000
def t191 : ℕ := 18085043208171727530
def t192 : ℕ := 18085043209350738160
def t193 : ℕ := 18085043209518512880
def t194 : ℕ := 18085043209519168250
def t195 : ℕ := 18158790778715962368
def t196 : ℕ := 18216212550151634124
def t197 : ℕ := 18226345803934399728
def t198 : ℕ := 18228597638107823344
def t199 : ℕ := 18229445395933298688
def t200 : ℕ := 18229670572478745804
def t201 : ℕ := 18229710309516177648
def t202 : ℕ := 18229723550950883328
def t203 : ℕ := 18229723554386857164
def t204 : ℕ := 18229723554993205488
def t205 : ℕ := 18229723555195321596
def t206 : ℕ := 18374403900871474942
def t207 : ℕ := 18374686479671623680
def t208 : ℕ := 18374686483949813760
def t209 : ℕ := 18374873400926579200
def t210 : ℕ := 18374910784321932288
def t211 : ℕ := 18374950366740541440
def t212 : ℕ := 18374966855136706560
def t213 : ℕ := 18374966857988876800
def t214 : ℕ := 18374966858559310848
def t215 : ℕ := 18374966859163299840
def t216 : ℕ := 18374966859414896640
def t217 : ℕ := 18374966859414961920
def t218 : ℕ := 18374966859431673855
def t219 : ℕ := 18374967954631622655
def t220 : ℕ := 18379189048491114255
def t221 : ℕ := 18389322302273879859
def t222 : ℕ := 18398892597513158485
def t223 : ℕ := 18413248040363163392
def t224 : ℕ := 18413248040372076424
def t225 : ℕ := 18420003542883434240
def t226 : ℕ := 18420003542893920160
def t227 : ℕ := 18422537229990625280
def t228 : ℕ := 18422537230001766400
def t229 : ℕ := 18422724872833597440
def t230 : ℕ := 18422724877111787520
def t231 : ℕ := 18422724877122972330
def t232 : ℕ := 18422762114478296064
def t233 : ℕ := 18422762114488781952
def t234 : ℕ := 18422762114489437320
def t235 : ℕ := 18422799643902528512
def t236 : ℕ := 18422817605455773440
def t237 : ℕ := 18422817605466914560
def t238 : ℕ := 18422818189571325696
def t239 : ℕ := 18422818331321958400
def t240 : ℕ := 18422818334185269930
def t241 : ℕ := 18422818335359037600
def t242 : ℕ := 18422818335600213760
def t243 : ℕ := 18422818335610699680
def t244 : ℕ := 18422818335611355050
def t245 : ℕ := 18429010879589711808
def t246 : ℕ := 18432107379212156928
def t247 : ℕ := 18432332555757604044
def t248 : ℕ := 18432387754677305088
def t249 : ℕ := 18432388626559008768
def t250 : ℕ := 18432388629994982604
def t251 : ℕ := 18432388630837264128
def t252 : ℕ := 18432388630850633676
def t253 : ℕ := 18441902704965766348
def t254 : ℕ := 18441958926087684044
def t255 : ℕ := 18441958926089912302
def t256 : ℕ := 18442240478376099840
def t257 : ℕ := 18442505391958978800
def t258 : ℕ := 18442520853841248000
def t259 : ℕ := 18442521880339415040
def t260 : ℕ := 18442521884381737200
def t261 : ℕ := 18442521884617670400
def t262 : ℕ := 18442521884633399280
def t263 : ℕ := 18445336677350178800
def t264 : ℕ := 18445336677350834170
def t265 : ℕ := 18445899635894321148
def t266 : ℕ := 18446462598732840960
def t267 : ℕ := 18446462601596108800
def t268 : ℕ := 18446462602168762368
def t269 : ℕ := 18446462602775101440
def t270 : ℕ := 18446462603011031040
def t271 : ℕ := 18446462603026759680
def t272 : ℕ := 18446462603027742720
def t273 : ℕ := 18446462603027808255
def t274 : ℕ := 18446463698244403455
def t275 : ℕ := 18446479160126672655
def t276 : ℕ := 18446518897164104499
def t277 : ℕ := 18446556426588345685
def t278 : ℕ := 18446612720724672512
def t279 : ℕ := 18446612720724707464
def t280 : ℕ := 18446639212082954240
def t281 : ℕ := 18446639212082995360
def t282 : ℕ := 18446649520004508160
def t283 : ℕ := 18446650245854003200
def t284 : ℕ := 18446650248717314730
def t285 : ℕ := 18446650250148904960
def t286 : ℕ := 18446650250148948650
def t287 : ℕ := 18446674533894045888
def t288 : ℕ := 18446686903399861248
def t289 : ℕ := 18446687487515413504
def t290 : ℕ := 18446687775278235648
def t291 : ℕ := 18446687778714209484
def t292 : ℕ := 18446687779320545472
def t293 : ℕ := 18446687779556477952
def t294 : ℕ := 18446687779569847500
def t295 : ℕ := 18446687779573137408
def t296 : ℕ := 18446687779573189632
def t297 : ℕ := 18446687779573189836
def t298 : ℕ := 18446725308997431022
def t299 : ℕ := 18446726485818470400
def t300 : ℕ := 18446727512315658240
def t301 : ℕ := 18446727516357980400
def t302 : ℕ := 18446727516610560000
def t303 : ℕ := 18446727516610621680
def t304 : ℕ := 18446738554676574970
def t305 : ℕ := 18446740757994799104
def t306 : ℕ := 18446740762037121264
def t307 : ℕ := 18446740762289765628
def t308 : ℕ := 18446742974197923840
def t309 : ℕ := 18446742978476179200
def t310 : ℕ := 18446742978492825600
def t311 : ℕ := 18446742978492890880
def t312 : ℕ := 18446743708637331200
def t313 : ℕ := 18446743708637331370
def t314 : ℕ := 18446743854649507584
def t315 : ℕ := 18446743854666219468
def t316 : ℕ := 18446744009285042160
def t317 : ℕ := 18446744069414584320
def t318 : ℕ := 18446744069414649855
def t319 : ℕ := 18446744069431296255
def t320 : ℕ := 18446744069667229455
def t321 : ℕ := 18446744070273577779
def t322 : ℕ := 18446744070846240085
def t323 : ℕ := 18446744071705233544
def t324 : ℕ := 18446744072109465760
def t325 : ℕ := 18446744072266754560
def t326 : ℕ := 18446744072277240480
def t327 : ℕ := 18446744072277852160
def t328 : ℕ := 18446744072277895850
def t329 : ℕ := 18446744072648442048
def t330 : ℕ := 18446744072837188608
def t331 : ℕ := 18446744072850505728
def t332 : ℕ := 18446744072850558156
def t333 : ℕ := 18446744073423220462
def t334 : ℕ := 18446744073441177600
def t335 : ℕ := 18446744073456844800
def t336 : ℕ := 18446744073456906480
def t337 : ℕ := 18446744073624681200
def t338 : ℕ := 18446744073625336570
def t339 : ℕ := 18446744073659022588
def t340 : ℕ := 18446744073692774400
def t341 : ℕ := 18446744073692826624
def t342 : ℕ := 18446744073692839680
def t343 : ℕ := 18446744073703325600
def t344 : ℕ := 18446744073703980970
def t345 : ℕ := 18446744073706209228
def t346 : ℕ := 18446744073708564720
def t347 : ℕ := 18446744073708568560
def t348 : ℕ := 18446744073709486080
def t349 : ℕ := 18446744073709529770
def t350 : ℕ := 18446744073709538508
def t351 : ℕ := 18446744073709547760
def t352 : ℕ := 18446744073709551360

def base : List ℕ := [t99, t128, t171, t217, t272, t317]

def perms : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]

def fam0 : List (ℕ × List ℕ × List ℕ) := [
  (0, [t99, t128, t171, t217, t272, t317], [2100096, 5100272, 9300080, 6900256, 8100064, 4100240, 8100048, 4100224, 8100032, 4100208, 8100016, 4100192, 7400288, 2000432, 2600304, 9600496, 2600320, 9600560, 2600336, 9600624, 6600112, 2600352, 9600688, 6200368, 4200512, 8200384, 2200576, 2200400, 2200160, 8200640, 200416, 200704, 600448, 2600592, 600464, 2600656, 600480, 6600128, 2600720, 600528, 2600672, 600544, 6600144, 2600736, 600608, 2600752]),
  (2, [t39, t60, t128, t217, t272, t317], [9100096, 5100064]),
  (2, [t99, t128, t171, t243, t272], [1000735, 4200559]),
  (3, [t17, t78, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t244, t272, t317], []),
  (3, [t44, t99, t128, t171, t217, t272, t317], [8200060]),
  (3, [t60, t118, t128, t171, t217, t272, t317], []),
  (3, [t82, t99, t128, t171, t217, t286, t317], []),
  (3, [t99, t118, t128, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t192, t217, t272, t317], [8600433, 6600128]),
  (3, [t99, t128, t171, t217, t266, t272, t336], []),
  (3, [t99, t128, t171, t217, t272, t332, t342], [9400689]),
  (3, [t43, t88, t128, t171, t217, t272], [7900127, 1900111]),
  (3, [t88, t99, t128, t197, t217, t272], []),
  (3, [t99, t128, t171, t217, t229, t272], [8600176]),
  (3, [t9, t99, t128, t171, t242], [])]

def fam1 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t8, t99, t128, t171, t217, t272], [600000, 9100192, 4600880, 7600354, 1800864, 9400338, 600848, 6600322, 600832, 6600306, 600816, 1600800, 100146, 4600450, 700178, 2200530, 3100210, 4100401, 2600610, 3100242, 4100497, 2600690, 3100274, 2600770, 9900370, 4500546, 5100386, 2100626, 5100402, 2100706, 5100418, 2100786, 8700466, 6700642, 700482, 4700722, 4700498, 4700896, 700802, 3100562, 5100738, 3100578, 5100818, 3100658, 5100834]),
  (2, [t39, t88, t99, t128, t217, t272], [8600112, 2601019, 9801003, 8600635, 5100971, 1101089, 7101147, 5101051, 9501067, 2701035]),
  (2, [t128, t154, t171, t242, t272], [1700127, 3300095, 7300047, 3000687, 9800050, 5800799, 7400719, 1800703]),
  (3, [t17, t82, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t252, t272, t317], []),
  (3, [t45, t49, t99, t171, t217, t272, t317], []),
  (3, [t60, t122, t128, t171, t217, t272, t317], []),
  (3, [t82, t99, t128, t171, t217, t297, t317], [600942, 5400732]),
  (3, [t99, t119, t128, t171, t217, t272, t317], [5000769]),
  (3, [t99, t128, t171, t194, t217, t272, t336], [2600397, 6600941, 4600449]),
  (3, [t99, t128, t171, t217, t266, t272, t342], []),
  (3, [t99, t128, t171, t217, t272, t336, t338], []),
  (3, [t43, t99, t171, t217, t297, t317], [3100111]),
  (3, [t88, t99, t138, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t230, t272], [8600176]),
  (3, [t20, t99, t128, t171, t297], [])]

def fam2 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t17, t99, t128, t171, t217, t317], [600000, 9100208, 4600976, 7601186, 1800960, 9401170, 600944, 6601154, 600928, 6601138, 600816, 100978, 4600067, 8701010, 5700369, 4200147, 3101042, 2600227, 3101074, 2600307, 3101106, 2600451, 9901202, 4500163, 5101218, 2100243, 5100003, 2100323, 9100992, 5100051, 2100467, 8700083, 6700259, 700099, 4700339, 2700131, 2700483, 3100179, 5100355, 3100211, 9101008, 5100499, 3100291, 9101024, 5100515]),
  (2, [t39, t99, t128, t217, t272, t336], [8600128, 7101184, 3101083, 7101163]),
  (2, [t99, t128, t171, t232], [9300863, 1700847, 2600066, 201039, 5601007]),
  (3, [t17, t88, t99, t128, t171, t217, t272], []),
  (3, [t28, t99, t128, t171, t262, t272, t317], [7100907]),
  (3, [t45, t99, t128, t171, t217, t272, t317], []),
  (3, [t60, t128, t133, t171, t217, t272, t317], []),
  (3, [t82, t99, t149, t171, t217, t272, t317], []),
  (3, [t99, t120, t128, t171, t217, t272, t317], [7400801]),
  (3, [t99, t128, t171, t194, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t266, t297, t317], []),
  (3, [t99, t128, t171, t217, t272, t336, t339], []),
  (3, [t44, t49, t88, t171, t217, t272], []),
  (3, [t88, t99, t139, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t234, t317], [1400751, 600479]),
  (3, [t20, t128, t154, t171, t272], [])]

def fam3 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t28, t99, t128, t171, t272, t317], [600000, 9100224, 4601104, 7600819, 1801088, 9400787, 601072, 6600755, 600928, 600832, 100579, 4600947, 2700611, 201027, 3100643, 2601107, 3100675, 2600068, 7101040, 3100723, 2600148, 9900851, 4501043, 5100867, 2101123, 5100899, 2100084, 9101120, 5100931, 2100164, 8700963, 6701139, 4700995, 4701168, 700100, 2701011, 2700180, 3101075, 5100116, 3101091, 9101136, 5100196, 3100052, 5100228]),
  (2, [t39, t99, t128, t217, t272, t342], [8600144, 4101211, 3101099, 2701195]),
  (2, [t154, t171, t242, t297], [8900895, 500879, 4600066, 5401071, 2601055]),
  (3, [t17, t88, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t266, t272, t317], []),
  (3, [t46, t49, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t154, t171, t217, t272, t317], []),
  (3, [t84, t99, t128, t171, t217, t272, t317], [5800993, 5000769, 1800780]),
  (3, [t99, t121, t128, t171, t217, t272, t317], [3400817]),
  (3, [t99, t128, t171, t194, t217, t297, t317], [1201198, 3400957]),
  (3, [t99, t128, t171, t217, t267, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t336, t342], [8600705, 4600753]),
  (3, [t44, t88, t128, t171, t217, t272], []),
  (3, [t88, t99, t148, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t239, t297], [200767, 3401217]),
  (3, [t39, t88, t154, t217, t297], [7500879])]

def fam4 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t39, t99, t128, t217, t272, t317], [600000, 9100240, 4600001, 7600500, 1801216, 9400468, 601072, 6600771, 600944, 600848, 100292, 4600628, 4700324, 8200708, 3100356, 2600900, 3100388, 2600980, 7101184, 3100436, 2601060, 9900532, 4500724, 5100564, 2100916, 5100580, 2100996, 9100017, 5100612, 2101076, 700660, 4700932, 4700676, 4700065, 701012, 2700692, 2701092, 3100868, 5101044, 3100884, 9100049, 5101124, 3100964, 5101140]),
  (2, [t39, t99, t128, t217, t297, t317], [5400160, 1701227, 3901035, 4701115, 3901195, 701179]),
  (2, [t154, t171, t232], []),
  (3, [t17, t99, t101, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t274, t317], []),
  (3, [t46, t99, t128, t171, t217, t272, t317], []),
  (3, [t60, t128, t157, t171, t217, t272, t317], []),
  (3, [t84, t99, t128, t171, t217, t297, t317], [600942, 6600796, 3400828, 8600812]),
  (3, [t99, t122, t128, t171, t217, t266, t272], [3400609]),
  (3, [t99, t128, t171, t195, t217, t272, t317], [1400961]),
  (3, [t99, t128, t171, t217, t268, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t336, t347], [3600525]),
  (3, [t47, t49, t88, t99, t171, t217], []),
  (3, [t88, t99, t149, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t241, t272], [600002]),
  (3, [t39, t99, t128, t242, t297], [4700879, 5500863])]

def fam5 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t49, t99, t171, t217, t272, t317], [6200000, 3100256, 1400113, 4400165, 7401216, 3400484, 7401088, 3400803, 7400960, 7400864, 2101220, 9000293, 4300021, 7800485, 2300053, 9800565, 2300081, 8300101, 3800645, 300133, 1800725, 1900213, 8900501, 1900229, 8900581, 1900245, 8900661, 5900129, 1900277, 8900741, 9900437, 1900613, 9900453, 1900693, 9900469, 5900145, 1900773, 9900533, 1900709, 9900549, 5900161, 1900789, 9900629, 1900805]),
  (2, [t47, t49, t99, t171, t217, t317], [3400097, 3100076]),
  (3, [t0, t99, t128, t171, t217, t272, t317], []),
  (3, [t17, t99, t108, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t286, t317], []),
  (3, [t47, t49, t99, t128, t171, t217, t317], [1500177]),
  (3, [t60, t128, t162, t171, t217, t272, t317], []),
  (3, [t85, t99, t128, t171, t217, t272, t317], [8600958, 4600785, 9600844]),
  (3, [t99, t122, t128, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t196, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t269, t272, t317], [8600721]),
  (3, [t99, t128, t171, t217, t272, t336, t348], [8600721]),
  (3, [t47, t88, t99, t128, t171, t217], []),
  (3, [t88, t99, t153, t171, t217, t297], [6200623, 4201137]),
  (3, [t99, t128, t171, t217, t242, t297], [8200783, 9000383]),
  (3, [t39, t128, t154, t242, t272], [2300879])]

def fam6 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t60, t128, t171, t217, t272, t317], [2600000, 4100272, 7800113, 5400181, 6600001, 2600516, 6601104, 2600835, 6600976, 6600880, 9500885, 6400038, 7100917, 1600118, 7100949, 1600198, 7100981, 1600278, 7101013, 5600209, 1600358, 4701205, 2700150, 6701221, 700230, 700006, 700257, 6700310, 8700022, 8700390, 9100070, 1100246, 9100086, 1100326, 9100102, 5100225, 1100406, 9100166, 1100342, 9100182, 5100241, 1100422, 9100262, 1100438]),
  (2, [t47, t99, t128, t171, t217, t317], [5700369, 6500081, 2200160, 3800092]),
  (3, [t0, t99, t128, t171, t217, t272, t342], []),
  (3, [t17, t99, t112, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t297, t317], []),
  (3, [t47, t49, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t166, t171, t217, t272, t317], []),
  (3, [t87, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t122, t128, t171, t217, t272, t342], [7400318, 3400653]),
  (3, [t99, t128, t171, t197, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t269, t272, t336], []),
  (3, [t99, t128, t171, t217, t272, t336, t351], []),
  (3, [t49, t60, t88, t171, t217, t272], []),
  (3, [t88, t99, t154, t171, t217, t297], [8000671]),
  (3, [t99, t128, t171, t217, t243, t272], [9601153]),
  (3, [t43, t88, t171, t217, t297], [5100895])]

def fam7 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t88, t99, t128, t171, t217, t272], [2100273, 6100454, 100193, 3101109, 7300129, 4900261, 6100017, 2100596, 6101120, 2100915, 6100992, 2100035, 3000598, 9400183, 6600758, 4600449, 8600263, 6600966, 8600176, 4600545, 2600305, 8600343, 6601126, 8600423, 5400630, 7000321, 199, 600790, 7600279, 600998, 7600359, 601158, 7600439, 4200119, 2200295, 6200135, 200375, 200151, 200289, 6200455, 8600215, 600391, 8600231, 600471, 8600311, 600487]),
  (2, [t49, t60, t171, t217, t272, t317], [4700096, 1900080]),
  (3, [t1, t99, t128, t171, t217, t272, t336], []),
  (3, [t17, t99, t118, t128, t171, t217, t317], [5700369]),
  (3, [t28, t99, t128, t171, t272, t303, t317], []),
  (3, [t47, t99, t128, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t176, t217, t272, t317], []),
  (3, [t88, t99, t108, t128, t171, t217, t272], [9000749, 3400573, 7800141, 7401196, 5401052]),
  (3, [t99, t122, t128, t171, t217, t295, t317], []),
  (3, [t99, t128, t171, t199, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t270, t272, t317], [8600737]),
  (3, [t99, t128, t171, t217, t272, t342, t344], []),
  (3, [t49, t88, t99, t171, t217, t297], [2700143]),
  (3, [t88, t128, t133, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t263, t272], [9601153]),
  (3, [t43, t128, t171, t242, t272], [9900895])]

def fam8 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t99, t128, t171, t217, t272, t336], [100225, 3101157, 7300145, 4900373, 6100033, 2100788, 6101136, 2101187, 6101008, 2100784, 6100114, 5400646, 536, 600822, 7600025, 601030, 7600825, 601206, 7600362, 600337, 4600663, 9600027, 4200871, 2200217, 6201063, 200985, 201207, 200865, 6200490, 1000184, 1400043, 8600632, 601145, 8600744, 600602, 8600313, 600714, 6600553, 4600753, 8600075, 6600106, 8600107]),
  (2, [t49, t88, t99, t171, t217, t272], [4200112, 9400108, 5401003, 5400651, 7100044, 300076, 7901105, 3900252, 1900140]),
  (3, [t2, t99, t128, t171, t217, t272, t317], [7100625]),
  (3, [t17, t99, t122, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t311, t317], []),
  (3, [t48, t49, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t194, t217, t272, t317], []),
  (3, [t88, t99, t112, t128, t171, t217, t272], [7000781, 9400589, 1800157, 9400013, 1401068]),
  (3, [t99, t122, t128, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t200, t217, t272, t317], [2200160]),
  (3, [t99, t128, t171, t217, t270, t272, t342], []),
  (3, [t99, t128, t171, t217, t272, t342, t345], []),
  (3, [t49, t88, t99, t171, t242, t272], []),
  (3, [t88, t128, t137, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t270, t347], []),
  (3, [t49, t99, t171, t242, t297], [])]

def fam9 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t99, t128, t171, t217, t272, t342], [100241, 3101173, 7300161, 4900389, 6100049, 2100804, 6101152, 2101203, 6101024, 2100768, 6100098, 5400662, 552, 600838, 7600041, 601046, 1600929, 7600841, 601222, 7600378, 600353, 4600695, 9600123, 4200887, 2200233, 6201079, 201001, 201223, 200881, 6200506, 7000216, 5400139, 8600648, 601161, 8600760, 600618, 6600952, 4600753, 8600155, 8600345, 600730, 600577, 6600138, 8600187]),
  (2, [t49, t99, t171, t217, t272, t336], [4200128, 9900172, 3900268]),
  (3, [t3, t8, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t130, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t317, t319], []),
  (3, [t48, t99, t128, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t205, t217, t272, t317], []),
  (3, [t88, t99, t118, t128, t171, t217, t272], [1400637, 9800173]),
  (3, [t99, t123, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t201, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t270, t317, t342], []),
  (3, [t99, t128, t171, t217, t272, t342, t347], [3600541, 9800701, 4600142]),
  (3, [t49, t88, t154, t171, t217, t272], []),
  (3, [t88, t128, t143, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t271, t347], []),
  (3, [t60, t128, t171, t242, t297], [])]

def fam10 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t99, t128, t171, t217, t297, t317], [6900257, 9901189, 4100177, 1700405, 2900065, 8900820, 2901168, 8901219, 6500912, 7300946, 2900896, 2200694, 9201009, 6800568, 7400870, 4400057, 7401062, 4400857, 1800071, 1600251, 1400289, 7400583, 4400331, 1000919, 9000249, 3001111, 7001017, 5000136, 5000347, 5400664, 7401193, 2200824, 2200283, 5400888, 1400865, 7400363, 2200481, 8200409, 6200315, 5400489, 1400881, 7400379, 8200833, 4200235, 200411]),
  (2, [t49, t99, t171, t217, t272, t342], [4200144, 900316, 9900188, 3900268]),
  (3, [t3, t99, t128, t171, t217, t272, t317], []),
  (3, [t17, t99, t128, t154, t171, t217, t317], [8300699]),
  (3, [t28, t99, t128, t171, t272, t317, t328], []),
  (3, [t49, t60, t99, t171, t217, t272, t317], [4400108]),
  (3, [t60, t128, t171, t208, t217, t272, t317], []),
  (3, [t88, t99, t122, t128, t171, t217, t272], [1800385, 5400669, 5800189, 7401084]),
  (3, [t99, t124, t128, t171, t217, t272, t317], [3400673]),
  (3, [t99, t128, t171, t202, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t273, t317], []),
  (3, [t99, t128, t171, t217, t272, t342, t348], [8600737]),
  (3, [t49, t94, t99, t171, t217, t272], []),
  (3, [t88, t128, t147, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t272, t326], [9601153]),
  (3, [t83, t99, t128, t171, t210], [8600959, 3000034, 9400911])]

def fam11 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t99, t128, t171, t242, t272], [8101121, 5301105, 2900204, 4101089, 8101073, 6100827, 4101057, 3400556, 5000018, 8000813, 8600604, 5601021, 2600461, 5600510, 8600748, 5600622, 2200573, 201037, 1400605, 5000542, 8200637, 8201217, 4200638, 8600845, 600574, 6600861, 8600654, 2601201, 8600462, 600686]),
  (2, [t49, t99, t171, t217, t297, t317], [1000160, 2300081, 700124, 1500220, 700300, 7500284]),
  (3, [t4, t8, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t157, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t317, t332], []),
  (3, [t49, t60, t128, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t212, t217, t272, t317], []),
  (3, [t88, t99, t128, t153, t171, t217, t272], [9000797, 7000321, 3000093]),
  (3, [t99, t124, t128, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t203, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t274, t317], []),
  (3, [t99, t128, t171, t217, t272, t342, t352], []),
  (3, [t49, t96, t99, t171, t217, t272], [7901105]),
  (3, [t88, t128, t152, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t272, t337], [9601153]),
  (3, [t83, t154, t171, t217, t297], [601199, 8601119, 6600911])]

def fam12 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t8, t99, t128, t171, t217, t272, t317], [7600162, 2100727, 8200194, 9700248, 600226, 100984, 600258, 100585, 600290, 100170, 5100434, 2100850, 2700514, 2700866, 3100594, 5100882, 3100674, 5100898, 3100754, 5100914]),
  (2, [t60, t88, t128, t171, t217, t272], [600112, 5800108, 4601019, 4600667, 5600209, 2900125, 7101121, 3100444, 1100364, 8700348]),
  (3, [t4, t99, t128, t171, t217, t272, t317], []),
  (3, [t17, t99, t128, t162, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t317, t336], []),
  (3, [t49, t70, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t222, t272, t317], []),
  (3, [t88, t99, t128, t154, t171, t217, t272], [800813, 4800109]),
  (3, [t99, t125, t128, t171, t217, t272, t317], [9400689]),
  (3, [t99, t128, t171, t204, t217, t272, t317], [6600128]),
  (3, [t99, t128, t171, t217, t272, t275, t317], []),
  (3, [t99, t128, t171, t217, t286, t297, t317], [5000769]),
  (3, [t49, t99, t128, t171, t242, t272], [7500143]),
  (3, [t88, t128, t154, t171, t217, t297], [2600719]),
  (3, [t99, t128, t171, t217, t272, t343], [9601153]),
  (3, [t84, t154, t171, t210, t317], [7800911])]

def fam13 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t99, t128, t171, t217, t272, t317], [7600994, 2100743, 6201026, 1700264, 601058, 101000, 601090, 100601, 601122, 100794, 5100019, 2100387, 5100035, 4700115, 700403, 3100195, 5100419, 3100275, 5100435, 3100371, 5100531]),
  (2, [t60, t128, t171, t217, t272, t322], [2100625]),
  (3, [t5, t8, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t166, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t317, t342], []),
  (3, [t49, t74, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t244, t272, t317], [4100492, 7100428]),
  (3, [t88, t99, t128, t157, t171, t217, t272], [600925, 6600829]),
  (3, [t99, t125, t128, t171, t217, t272, t342], [9800334, 9800685]),
  (3, [t99, t128, t171, t205, t217, t272, t336], []),
  (3, [t99, t128, t171, t217, t272, t276, t317], []),
  (3, [t99, t128, t171, t217, t286, t303, t317], [4600785]),
  (3, [t49, t99, t171, t210, t297, t317], []),
  (3, [t88, t128, t154, t171, t242, t272], [3800303]),
  (3, [t99, t128, t171, t217, t272, t346], []),
  (3, [t85, t128, t171, t242, t272], [])]

def fam14 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t99, t128, t171, t217, t272, t317], [600835, 7800803, 6600771, 6601138, 6600306, 7600595, 2100759, 200627, 7700280, 600659, 101016, 600691, 100186, 4601056, 600739, 3100707, 100810, 5100883, 2100004, 5100915, 700979, 4700020, 701219, 3101059, 5100036, 5101187, 3101155, 5100132, 3101171, 9101152, 5100212, 5101203]),
  (2, [t60, t128, t171, t217, t272, t336], [600128]),
  (3, [t5, t99, t128, t171, t217, t272, t317], [6600128]),
  (3, [t17, t99, t128, t171, t173, t217, t317], []),
  (3, [t28, t99, t128, t171, t272, t317, t348], []),
  (3, [t49, t78, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t252, t272, t317], []),
  (3, [t88, t99, t128, t162, t171, t217, t272], [6600861]),
  (3, [t99, t127, t128, t171, t217, t272, t317], [9400849]),
  (3, [t99, t128, t171, t205, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t272, t277, t317], []),
  (3, [t99, t128, t171, t217, t290, t297, t317], [5801117]),
  (3, [t49, t99, t171, t217, t239, t272], [7901105]),
  (3, [t88, t154, t171, t205, t217, t272], []),
  (3, [t99, t128, t171, t217, t279, t342], []),
  (3, [t85, t128, t192, t217, t272], [])]

def fam15 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t39, t99, t128, t171, t217, t272, t317], [600516, 7800484, 6600755, 6601154, 6600322, 7600308, 2100775, 2200340, 5700296, 600372, 100617, 600404, 100202, 4601200, 600452, 3100420, 100826, 5100548, 2100836, 5100596, 8700644, 6700852, 700820, 3100740, 5100948, 3100756, 5101028, 3100772, 9100033, 5101108, 5100788, 5100804]),
  (2, [t60, t128, t171, t217, t272, t342], [600144, 8700476]),
  (3, [t6, t8, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t194, t217, t317], []),
  (3, [t29, t99, t128, t171, t217, t272, t317], [4601056]),
  (3, [t49, t82, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t262, t272, t317], []),
  (3, [t88, t99, t128, t166, t171, t217, t272], [8600433, 6600877]),
  (3, [t99, t128, t129, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t205, t217, t297, t317], []),
  (3, [t99, t128, t171, t217, t272, t279, t317], []),
  (3, [t99, t128, t171, t217, t297, t298, t317], []),
  (3, [t49, t99, t171, t217, t242, t272], []),
  (3, [t88, t154, t171, t217, t272, t297], [1000799]),
  (3, [t99, t128, t171, t217, t292, t297], []),
  (3, [t88, t99, t128, t171, t232], [5000991, 6600927])]

def fam16 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t49, t99, t128, t171, t217, t272, t317], [9000181, 5000468, 5000787, 5001170, 5000338, 2800005, 9700791, 5000037, 8501032, 3000069, 500633, 3000097, 9000117, 9900085, 4500218, 1000149, 2500842, 6700197, 1300421, 3500261, 5500309, 3500517, 7500325, 1500597, 1500341, 1500177, 7500677, 9100405, 9500357, 9500757, 3500373, 3500389]),
  (2, [t60, t128, t171, t217, t297, t317], [7400160, 700412, 9900476, 6700460]),
  (3, [t6, t99, t128, t171, t217, t272, t317], [6600144]),
  (3, [t17, t99, t128, t171, t205, t217, t317], []),
  (3, [t31, t99, t128, t171, t217, t272, t317], []),
  (3, [t49, t88, t99, t128, t171, t217, t272], [7800060, 1000092, 5500204, 6300156, 9500124]),
  (3, [t60, t128, t171, t217, t266, t272, t317], []),
  (3, [t88, t99, t128, t171, t192, t217, t272], [6600989]),
  (3, [t99, t128, t130, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t206, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t281, t317], []),
  (3, [t99, t128, t171, t217, t297, t303, t317], [7400801]),
  (3, [t49, t99, t171, t217, t272, t347], []),
  (3, [t88, t154, t171, t217, t297, t317], [1000815]),
  (3, [t99, t128, t171, t217, t293, t297], []),
  (3, [t88, t150, t171, t217, t272], [])]

def fam17 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t60, t99, t128, t171, t217, t272, t317], [800165, 9600500, 9600819, 9601186, 9600354, 1000901, 7900312, 8600933, 3101048, 8600965, 3100649, 8600997, 3100234, 8601029, 7100625, 3100858, 8601141, 5901045, 500054, 1101061, 8100134, 1101077, 8100214, 1101093, 8100294, 5100193, 1101125, 8101109, 8100374, 3701189, 8101157, 8101173]),
  (2, [t61, t99, t128, t171, t217, t272], [6600112, 2600859, 1600800, 3500524, 6700508]),
  (3, [t7, t8, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t208, t217, t317], []),
  (3, [t32, t99, t128, t171, t217, t272, t317], []),
  (3, [t49, t88, t99, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t272, t277, t317], []),
  (3, [t88, t99, t128, t171, t194, t217, t272], [3601021, 6600892]),
  (3, [t99, t128, t131, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t207, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t282, t317], []),
  (3, [t99, t128, t171, t217, t297, t307, t317], [1600860, 9801181, 3800350]),
  (3, [t49, t99, t171, t217, t290, t297], []),
  (3, [t89, t99, t128, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t293, t342], []),
  (3, [t88, t154, t171, t210, t297], [201103, 7800911])]

def fam18 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t70, t99, t128, t171, t217, t272, t317], [3300534, 501045, 7700197, 6500532, 6500851, 6501202, 6500370, 9000550, 5001064, 7000566, 7000665, 3000582, 5000769, 1000250, 3400678, 5000614, 9000874, 2800710, 5000630, 600694, 5000646, 5000662]),
  (2, [t88, t99, t128, t171, t217, t297], [6900508, 4900348, 2100124, 901035, 900875, 4500587, 6600093, 9400973, 3401217, 9400094, 7401180, 6600796, 4201137, 1800205, 7200109, 200924]),
  (3, [t7, t99, t128, t171, t217, t272, t317], []),
  (3, [t17, t99, t128, t171, t212, t217, t317], []),
  (3, [t34, t39, t99, t128, t217, t272, t317], [5100971]),
  (3, [t49, t99, t104, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t272, t286, t317], []),
  (3, [t88, t99, t128, t171, t205, t217, t272], [7400862, 7401037, 8200237]),
  (3, [t99, t128, t132, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t208, t217, t266, t317], [2600561]),
  (3, [t99, t128, t171, t217, t272, t283, t286], []),
  (3, [t99, t128, t171, t217, t297, t311, t317], [3400817]),
  (3, [t49, t99, t171, t217, t297, t342], []),
  (3, [t90, t99, t128, t171, t217, t272], [8600176]),
  (3, [t99, t128, t171, t217, t294, t342], [7801185]),
  (3, [t88, t154, t171, t242, t297], [8600927])]

def fam19 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t74, t99, t128, t171, t217, t272, t317], [8100518, 6101061, 3300213, 2100548, 2100867, 2101218, 2100386, 9000550, 9800977, 7400360, 3800902, 8600726, 4600897, 600681, 8600886, 8600742, 4600785, 600266, 8600854, 8600774, 4600641, 600890, 8600806, 600918, 600790, 6200870, 600822, 600838]),
  (2, [t88, t99, t128, t171, t242, t272], [2100364, 9300140, 8101051, 2100811, 8100683, 1000540, 7400797, 4600572, 6600989, 4600700, 6600606, 9000221, 2201180, 6601148]),
  (3, [t8, t28, t99, t128, t171, t217, t272], [2100768]),
  (3, [t17, t99, t128, t171, t217, t219, t317], []),
  (3, [t34, t99, t128, t171, t217, t272, t317], [2600987]),
  (3, [t49, t99, t108, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t272, t297, t317], []),
  (3, [t88, t99, t128, t171, t208, t217, t272], [600030, 6601069]),
  (3, [t99, t128, t133, t171, t217, t272, t317], [3500125]),
  (3, [t99, t128, t171, t208, t217, t272, t336], [600222]),
  (3, [t99, t128, t171, t217, t272, t283, t317], []),
  (3, [t99, t128, t171, t217, t297, t315, t317], []),
  (3, [t49, t99, t171, t244, t272, t342], [7901105]),
  (3, [t92, t99, t128, t171, t217, t272], [8600176]),
  (3, [t99, t128, t171, t217, t295, t342], []),
  (3, [t94, t154, t171, t217, t297], [7001167])]

def fam20 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t78, t99, t128, t171, t217, t272, t317], [8100502, 6101077, 3300229, 2100564, 2100883, 2100003, 2100402, 7000566, 9400408, 8600726, 601112, 8600950, 600282, 8600982, 4600657, 600906, 8601014, 7601078, 600998, 6201062, 601030, 601046]),
  (2, [t88, t128, t154, t171, t217, t272], [1300524, 6500156, 3700012, 5301067, 5300891, 5300699, 3801118, 7800018, 3801150, 1800221, 3800237, 1801137, 7800253, 9400205]),
  (3, [t8, t39, t99, t128, t171, t217, t272], [2100784]),
  (3, [t17, t99, t128, t171, t217, t244, t317], [8100795, 1100747]),
  (3, [t35, t39, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t112, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t272, t303, t317], []),
  (3, [t88, t99, t128, t171, t212, t217, t272], [8600529, 6601197]),
  (3, [t99, t128, t134, t171, t217, t272, t317], [9801025, 9800977]),
  (3, [t99, t128, t171, t208, t217, t272, t340], []),
  (3, [t99, t128, t171, t217, t272, t284, t317], [8600593]),
  (3, [t99, t128, t171, t217, t297, t317, t328], []),
  (3, [t57, t88, t99, t128, t171, t272], [8600176]),
  (3, [t93, t99, t128, t171, t217, t272], []),
  (3, [t99, t128, t171, t217, t296, t342], [7801185]),
  (3, [t96, t154, t171, t217, t297], [5000050])]

def fam21 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t82, t99, t128, t171, t217, t272, t317], [8100486, 6101093, 3300245, 2100580, 2100899, 2100019, 2100418, 3000582, 5800993, 3400456, 9800039, 8600742, 601176, 8600950, 600745, 8601142, 600922, 7600007, 601158, 6200023, 8601174, 601206, 8601190, 601222]),
  (2, [t94, t99, t128, t171, t217, t272], [2100380, 9300172, 8101083, 8100715, 4600449, 600002, 6600110, 6600365, 9000381, 6600397, 9600652, 9600716, 2200349]),
  (3, [t8, t49, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t252, t317], []),
  (3, [t35, t99, t128, t171, t217, t272, t317], []),
  (3, [t49, t99, t118, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t272, t311, t317], []),
  (3, [t88, t99, t128, t171, t217, t242, t272], [4600636, 4600940]),
  (3, [t99, t128, t137, t171, t217, t272, t317], [8200141, 6200733]),
  (3, [t99, t128, t171, t208, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t272, t285, t317], [8600593]),
  (3, [t99, t128, t171, t217, t297, t317, t332], []),
  (3, [t60, t88, t128, t171, t217, t297], [1900159]),
  (3, [t94, t99, t128, t171, t217, t297], [5400559, 6200319]),
  (3, [t99, t128, t171, t217, t297, t305], []),
  (3, [t99, t113, t128, t171, t227], [9801023, 9000975, 3000034])]

def fam22 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t88, t99, t128, t171, t217, t272, t317], [8100470, 6101125, 3300277, 2100612, 2100931, 2100051, 2100434, 5000614, 1400520, 8600774, 600009, 8600982, 4600913, 600809, 8600599, 8601142, 600346, 3000615, 7600503, 6200583, 8200167, 8200519, 8600247, 600535, 8600327, 600551, 8600407, 600567]),
  (2, [t96, t99, t128, t171, t217, t272], [2100396, 9300188, 8101099, 8100731, 6601005, 8600176, 4600545, 4600461, 9000477, 9600588, 2200445]),
  (3, [t8, t60, t99, t128, t171, t217, t272], [2100273]),
  (3, [t17, t99, t128, t171, t217, t262, t317], [7100779]),
  (3, [t36, t39, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t122, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t272, t317, t322], []),
  (3, [t88, t99, t128, t171, t217, t244, t272], [3600510, 6600956]),
  (3, [t99, t128, t139, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t208, t217, t297, t317], [3400398, 5401053]),
  (3, [t99, t128, t171, t217, t272, t286, t336], []),
  (3, [t99, t128, t171, t217, t297, t317, t336], []),
  (3, [t60, t88, t128, t171, t242, t272], []),
  (3, [t94, t99, t128, t171, t243, t272], []),
  (3, [t99, t128, t171, t217, t297, t306], []),
  (3, [t99, t116, t171, t242, t272], [])]

def fam23 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t108, t128, t171, t217, t272, t317], [6901205, 4500869, 4100309, 2900644, 2900963, 2900083, 2900466, 9000550, 9801025, 4600523, 2800344, 1400119, 7400807, 9400945, 5400873, 4200935, 9400823, 7400801, 3400394, 2200903, 3400839, 3400673, 9400938, 8200855, 1400967, 3000951, 7000919, 1400871, 1400887]),
  (2, [t99, t128, t130, t171, t217, t317], [3000097, 1900876]),
  (3, [t8, t70, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t266, t317], []),
  (3, [t36, t99, t128, t171, t217, t272, t317], []),
  (3, [t49, t99, t128, t171, t217, t272, t336], []),
  (3, [t60, t128, t171, t217, t272, t317, t328], []),
  (3, [t88, t99, t128, t171, t217, t252, t272], [1400526]),
  (3, [t99, t128, t140, t171, t217, t272, t317], [3801041]),
  (3, [t99, t128, t171, t209, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t286, t342], []),
  (3, [t99, t128, t171, t217, t297, t317, t342], []),
  (3, [t60, t94, t128, t171, t217, t272], []),
  (3, [t94, t128, t154, t171, t217, t272], [9800735, 3800319]),
  (3, [t99, t128, t171, t217, t297, t314], [7801185]),
  (3, [t99, t128, t171, t217, t232], [])]

def fam24 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t112, t128, t171, t217, t272, t317], [2901221, 2500853, 100325, 8900660, 8900979, 8900099, 8900482, 7000566, 3801041, 4600539, 6800392, 7400135, 7400807, 1400961, 7400105, 2201143, 5400999, 3400817, 9400410, 4201095, 9401015, 9400689, 5400954, 201047, 7001127, 3001111, 7401063, 5401031, 7401079]),
  (2, [t99, t128, t151, t171, t217, t272], [6600112]),
  (3, [t8, t74, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t286, t317], []),
  (3, [t37, t39, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t128, t171, t217, t272, t342], [9500300]),
  (3, [t60, t128, t171, t217, t272, t317, t332], []),
  (3, [t88, t99, t128, t171, t217, t262, t272], [2600558, 8600126, 1600684]),
  (3, [t99, t128, t143, t171, t217, t272, t317], [200157, 8200765]),
  (3, [t99, t128, t171, t210, t217, t272, t317], [3400817]),
  (3, [t99, t128, t171, t217, t272, t287, t317], []),
  (3, [t99, t128, t171, t217, t297, t317, t348], [9400849]),
  (3, [t60, t96, t128, t171, t217, t272], [7101121]),
  (3, [t94, t128, t171, t194, t217, t272], []),
  (3, [t99, t128, t171, t217, t297, t340], []),
  (3, [t99, t128, t171, t227, t263], [])]

def fam25 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t118, t128, t171, t217, t272, t317], [4900006, 8500837, 2100341, 900676, 900995, 900115, 900498, 3000582, 4800440, 9400151, 9400823, 9400153, 5400999, 3400921, 1401191, 7400970, 5000008, 9401207, 9401223]),
  (2, [t99, t128, t171, t172, t217, t272], [4601200]),
  (3, [t8, t78, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t297, t317], []),
  (3, [t37, t99, t128, t171, t217, t272, t317], []),
  (3, [t49, t99, t128, t171, t217, t297, t317], [3000097]),
  (3, [t60, t128, t171, t217, t272, t317, t336], []),
  (3, [t88, t99, t128, t171, t217, t266, t272], [6600590, 8600593]),
  (3, [t99, t128, t144, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t210, t217, t297, t317], [5800414, 1801165, 3801085]),
  (3, [t99, t128, t171, t217, t272, t288, t317], [7400465]),
  (3, [t99, t128, t171, t217, t297, t317, t350], []),
  (3, [t60, t128, t171, t210, t297, t317], []),
  (3, [t95, t99, t128, t171, t217, t272], [8600176]),
  (3, [t99, t128, t171, t217, t297, t341], [7801185]),
  (3, [t99, t128, t171, t232, t242], [601055])]

def fam26 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t122, t128, t171, t217, t272, t317], [8900022, 500821, 6100357, 4900692, 4901011, 4900131, 4900514, 5000614, 800504, 3400167, 3400839, 3400201, 9401015, 7400969, 1401191, 9400849, 5400474, 6200120, 9000136, 3400088, 3400104, 1400072]),
  (2, [t99, t128, t171, t185, t217, t317], [600892, 600941]),
  (3, [t8, t82, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t303, t317], []),
  (3, [t38, t39, t99, t128, t171, t217, t272], [9100033]),
  (3, [t49, t99, t154, t171, t217, t272, t317], [5100156]),
  (3, [t60, t128, t171, t217, t272, t317, t342], []),
  (3, [t88, t99, t128, t171, t217, t272, t285], [6600606]),
  (3, [t99, t128, t146, t171, t217, t272, t317], [5800993]),
  (3, [t99, t128, t171, t210, t272, t297, t317], []),
  (3, [t99, t128, t171, t217, t272, t290, t297], []),
  (3, [t99, t128, t171, t244, t262, t272, t317], [4600897, 3600830]),
  (3, [t60, t128, t171, t217, t239, t272], [7101121]),
  (3, [t96, t99, t128, t171, t217, t270], []),
  (3, [t99, t128, t171, t217, t297, t347], []),
  (3, [t99, t128, t171, t232, t272], [])]

def fam27 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t154, t171, t217, t272, t317], [4300054, 1500421, 8701204, 300724, 301043, 300163, 300546, 2000710, 8800555, 8800571, 5800321, 1800615, 8800199, 8800491, 6801009, 2800507, 4400568, 9800328, 8800265, 3800376, 4801033, 1800424, 6800522, 1800385, 7800488, 4000472, 800986, 8800536, 8800552]),
  (2, [t99, t128, t171, t190, t217, t272], [3001102, 6600112, 6200957, 4600449]),
  (3, [t8, t88, t99, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t311, t317], []),
  (3, [t38, t39, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t157, t171, t217, t272, t317], []),
  (3, [t60, t128, t171, t217, t272, t317, t348], []),
  (3, [t88, t99, t128, t171, t217, t272, t286], [3600622]),
  (3, [t99, t128, t147, t171, t217, t272, t317], [4200173]),
  (3, [t99, t128, t171, t211, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t290, t317], [9400849]),
  (3, [t99, t128, t171, t244, t272, t317, t342], [4600913]),
  (3, [t60, t128, t171, t217, t242, t272], []),
  (3, [t96, t99, t128, t171, t217, t297], [3401217, 6200335]),
  (3, [t99, t128, t171, t226, t272, t343], []),
  (3, [t99, t128, t171, t232, t297], [3401071])]

def fam28 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t157, t171, t217, t272, t317], [100070, 7300437, 101188, 6100740, 6101059, 6100179, 6100562, 8600726, 7601096, 4600215, 7400807, 7000089, 200664, 2600584, 4600538, 2600600, 8600705, 4601002, 6600616, 4600632, 4600648]),
  (2, [t99, t128, t171, t192, t217, t272], [1001118, 8600620, 600337, 200862, 4200973, 8600878, 8600126]),
  (3, [t8, t99, t100, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t317, t318], []),
  (3, [t38, t99, t128, t171, t217, t272, t317], []),
  (3, [t49, t99, t162, t171, t217, t272, t317], []),
  (3, [t61, t88, t99, t128, t171, t217, t272], [4600332]),
  (3, [t88, t99, t128, t171, t217, t272, t297], [9400638, 1800780, 200253, 5400908]),
  (3, [t99, t128, t149, t171, t217, t272, t317], [1000942, 2200160]),
  (3, [t99, t128, t171, t212, t217, t272, t336], []),
  (3, [t99, t128, t171, t217, t272, t291, t317], [2200160, 3400609]),
  (3, [t99, t128, t171, t252, t262, t272, t317], [9400945]),
  (3, [t60, t128, t171, t217, t290, t297], []),
  (3, [t96, t99, t128, t171, t242, t272], []),
  (3, [t99, t128, t171, t227, t242, t272], []),
  (3, [t99, t128, t171, t232, t317], [])]

def fam29 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t162, t171, t217, t272, t317], [100086, 7300453, 101172, 6100756, 6101075, 6100195, 6100578, 8600742, 7601160, 4601174, 4600231, 9400823, 5000137, 200776, 2600584, 4601081, 2600712, 8600721, 4601018, 6600728, 4600744, 4600760]),
  (2, [t99, t128, t171, t210, t272, t317], [7000732, 7000908, 2600481]),
  (3, [t8, t99, t108, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t317, t328], []),
  (3, [t39, t49, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t166, t171, t217, t272, t317], []),
  (3, [t61, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t272, t303], [2600878, 2600654, 1600844]),
  (3, [t99, t128, t151, t154, t171, t217, t272], [5800321, 400974]),
  (3, [t99, t128, t171, t212, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t272, t295, t317], [3400609]),
  (3, [t99, t128, t205, t217, t262, t272, t317], [1400961]),
  (3, [t60, t128, t171, t217, t297, t342], []),
  (3, [t96, t128, t154, t171, t217, t272], [7800018, 3800335]),
  (3, [t99, t128, t171, t228, t244, t342], []),
  (3, [t99, t128, t171, t234, t342], [3401087, 3000034])]

def fam30 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t166, t171, t217, t272, t317], [100102, 7300469, 101156, 6100772, 6101091, 6100211, 6100594, 8600774, 7601224, 4600247, 3400839, 1000185, 200888, 2600600, 4601129, 2600712, 4600586, 4600856, 4600872]),
  (2, [t99, t128, t171, t210, t297, t317], [7300412, 4500220, 3301115, 6100955, 9600990, 1400812, 1800924, 1801181, 1801133, 6201149, 7801169, 3801117, 8601101]),
  (3, [t8, t99, t112, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t317, t332], []),
  (3, [t39, t49, t99, t171, t217, t272, t317], []),
  (3, [t49, t99, t171, t175, t217, t272, t317], []),
  (3, [t62, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t272, t311], [2600670]),
  (3, [t99, t128, t151, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t212, t217, t297, t317], []),
  (3, [t99, t128, t171, t217, t272, t297, t336], []),
  (3, [t99, t154, t171, t205, t217, t272, t317], [7000237, 9800977]),
  (3, [t60, t128, t171, t244, t272, t342], [7101121]),
  (3, [t97, t99, t128, t171, t217, t272], [600002]),
  (3, [t99, t128, t171, t239, t242, t272], []),
  (3, [t99, t128, t171, t235, t297], [7801103, 3000034])]

def fam31 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t194, t217, t272, t317], [7100134, 4300501, 3100836, 1100276, 3101123, 3100243, 3100626, 4000555, 4600918, 1600279, 4600983, 8800265, 7200057, 1600025, 4601080, 1601209, 8600417, 4601144, 3601128, 1600634, 8600433, 4601208, 3601192, 1601034, 1600041]),
  (2, [t99, t128, t171, t217, t218, t272], [4601056]),
  (3, [t8, t99, t118, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t317, t336], []),
  (3, [t39, t60, t99, t128, t217, t272, t317], [7601019]),
  (3, [t49, t99, t171, t194, t217, t272, t317], []),
  (3, [t63, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t272, t328], [3600702]),
  (3, [t99, t128, t152, t171, t217, t272, t317], [2200189, 1800385]),
  (3, [t99, t128, t171, t213, t217, t272, t317], [4600657]),
  (3, [t99, t128, t171, t217, t272, t297, t342], []),
  (3, [t99, t154, t171, t217, t272, t297, t317], [9000253, 5800993]),
  (3, [t61, t99, t128, t171, t217, t297], []),
  (3, [t97, t128, t171, t217, t262, t272], []),
  (3, [t99, t128, t171, t242, t244, t272], []),
  (3, [t99, t128, t171, t238, t297], [3001119, 3000034])]

def fam32 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t205, t217, t272, t317], [900150, 8100517, 6900852, 6901139, 6900259, 6900642, 3200491, 1000934, 8800265, 5400295, 7400967, 9000951, 1000249, 5400475, 5400217, 1400073, 9401225, 3400121, 7400650, 7400169, 3401050, 5400233]),
  (2, [t99, t128, t171, t217, t228, t317], [600956]),
  (3, [t8, t99, t122, t128, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t317, t342], []),
  (3, [t39, t60, t128, t171, t217, t272, t317], []),
  (3, [t49, t99, t171, t205, t217, t272, t317], []),
  (3, [t64, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t272, t332], [5400718]),
  (3, [t99, t128, t153, t171, t217, t272, t317], [1800385]),
  (3, [t99, t128, t171, t214, t217, t272, t317], [9400689]),
  (3, [t99, t128, t171, t217, t272, t298, t317], []),
  (3, [t108, t128, t137, t171, t217, t272, t317], []),
  (3, [t61, t128, t154, t171, t217, t272], []),
  (3, [t97, t128, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t242, t252, t272], []),
  (3, [t99, t128, t171, t242, t253], [5801135, 3000034])]

def fam33 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t208, t217, t272, t317], [100166, 7300533, 6100868, 100260, 6101155, 6100275, 6100658, 8600950, 7600729, 4601190, 4600311, 5400999, 9000905, 201031, 200361, 2600584, 4601065, 4600313, 2600281, 8600737, 4601066, 6600329, 4600345, 2600297]),
  (2, [t99, t128, t171, t217, t239, t272], [6100428, 3300236, 2101131, 2100747, 3001134, 6600112, 6200062, 8600176, 8600494, 4600545]),
  (3, [t8, t99, t128, t129, t171, t217, t272], []),
  (3, [t17, t99, t128, t171, t217, t317, t348], []),
  (3, [t39, t70, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t208, t217, t272, t317], []),
  (3, [t65, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t272, t336], [2600734]),
  (3, [t99, t128, t154, t171, t217, t272, t336], [9800381, 4801022]),
  (3, [t99, t128, t171, t215, t217, t272, t317], [8600705]),
  (3, [t99, t128, t171, t217, t272, t299, t317], []),
  (3, [t112, t128, t143, t171, t217, t272, t317], []),
  (3, [t69, t99, t128, t171, t242, t272], []),
  (3, [t97, t128, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t242, t254, t272], []),
  (3, [t99, t128, t171, t242, t289], [2601151, 3000034])]

def fam34 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t212, t217, t272, t317], [100182, 7300549, 6100884, 100244, 6101171, 6100291, 6100674, 8600982, 7600793, 4600327, 9401015, 5000953, 200489, 2600600, 4601113, 4600457, 2600281, 4600698, 4600473]),
  (2, [t99, t128, t171, t217, t242, t272], [4100444, 1300252, 101147, 100763, 1001150, 8600668, 5600510, 600353, 4200589, 8200526, 4200094, 6600829, 8600558, 8600126, 6601069, 8600670, 8601213]),
  (3, [t8, t99, t128, t154, t171, t217, t272], []),
  (3, [t18, t99, t128, t171, t217, t272, t317], []),
  (3, [t39, t74, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t212, t217, t272, t317], []),
  (3, [t66, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t272, t342], [2600750, 600972]),
  (3, [t99, t128, t154, t171, t217, t272, t342], [801182, 9800477, 4801038]),
  (3, [t99, t128, t171, t215, t217, t272, t336], []),
  (3, [t99, t128, t171, t217, t272, t300, t317], []),
  (3, [t128, t154, t171, t194, t217, t272, t317], [8801198, 9801025, 7801102]),
  (3, [t70, t99, t128, t171, t242, t272], []),
  (3, [t97, t128, t171, t217, t272, t347], []),
  (3, [t99, t128, t171, t242, t262, t272], []),
  (3, [t99, t128, t171, t243, t297], [8201167, 1800943])]

def fam35 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t244, t272, t317], [7100214, 4300581, 3100916, 3100004, 1100563, 3100323, 3100706, 4000571, 1601078, 1600359, 8601159, 4801033, 7200857, 1600427, 4600680, 1601209, 1600825, 5600929, 1600443, 1600841, 8600513, 4600713, 3600697, 1600746, 8600529, 4600777, 3600761, 1601082]),
  (2, [t99, t128, t171, t217, t270, t317], [2600972, 200653, 2600577]),
  (3, [t8, t99, t128, t157, t171, t217, t272], []),
  (3, [t19, t99, t128, t171, t217, t272, t317], []),
  (3, [t39, t78, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t221, t272, t317], []),
  (3, [t67, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t272, t348], [2600766]),
  (3, [t99, t128, t154, t171, t217, t297, t317], [600205]),
  (3, [t99, t128, t171, t216, t217, t272, t317], [8600737]),
  (3, [t99, t128, t171, t217, t272, t301, t317], [6600128]),
  (3, [t128, t154, t171, t217, t244, t272, t317], [8801214, 3801041, 4801182, 7801134]),
  (3, [t73, t99, t128, t171, t242, t272], []),
  (3, [t99, t108, t128, t171, t242, t272], []),
  (3, [t99, t128, t171, t242, t263, t272], [7000367, 4600399]),
  (3, [t99, t128, t171, t244, t293], [4001183, 3000034])]

def fam36 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t252, t272, t317], [4900230, 2100597, 900932, 900020, 900339, 900722, 3001094, 4801033, 9400375, 5001127, 5001017, 9400459, 9400696, 9401225, 9400985, 9401001, 7400889, 1400762, 1400937, 7401098]),
  (2, [t99, t128, t171, t217, t270, t342], [7600814, 6600429, 6600302, 9000685, 600142]),
  (3, [t8, t99, t128, t162, t171, t217, t272], []),
  (3, [t23, t28, t99, t128, t171, t272, t317], []),
  (3, [t39, t82, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t244, t272, t317], [4900316, 7900236]),
  (3, [t68, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t99, t128, t171, t217, t297, t317], [9400782, 200269]),
  (3, [t99, t128, t155, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t218, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t302, t317], []),
  (3, [t9, t88, t99, t128, t171, t217], [6300015, 7101230]),
  (3, [t74, t96, t128, t171, t217, t272], [9601153]),
  (3, [t99, t112, t128, t171, t242, t272], []),
  (3, [t99, t128, t171, t242, t266, t272], []),
  (3, [t99, t128, t189, t217, t297], [9001199, 4200959])]

def fam37 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t262, t272, t317], [6100246, 3300613, 2100948, 2100036, 8100547, 2100355, 2100738, 7600427, 6601110, 1601209, 600391, 2200475, 200459, 7001175, 9401225, 6201193, 601145, 601161, 8601049, 600778, 8601097, 4600753, 601114, 8601177]),
  (2, [t99, t128, t171, t217, t272, t283], [6600112]),
  (3, [t8, t99, t128, t166, t171, t217, t272], [4100401]),
  (3, [t23, t99, t128, t171, t217, t272, t317], [2600843]),
  (3, [t39, t88, t99, t128, t171, t217, t272], [2600987]),
  (3, [t49, t99, t171, t217, t252, t272, t317], []),
  (3, [t69, t88, t99, t128, t171, t217, t272], [9801212, 5801100, 7800988, 9800540]),
  (3, [t88, t99, t128, t171, t242, t272, t317], []),
  (3, [t99, t128, t156, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t219, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t303, t336], []),
  (3, [t9, t99, t154, t171, t217, t317], [5901230]),
  (3, [t74, t99, t128, t171, t242, t272], [600002]),
  (3, [t99, t113, t128, t171, t242, t272], [9800687, 9000607, 5000543, 7000351]),
  (3, [t99, t128, t171, t242, t272, t285], []),
  (3, [t99, t128, t198, t242, t272], [4601215, 1800975])]

def fam38 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t266, t272, t317], [100262, 7300629, 6100964, 6100052, 6100371, 6100754, 8601142, 7600330, 4600407, 1401191, 3000458, 200042, 2200072, 2600712, 4600570, 4600010, 2600281, 4600682, 2600297, 4600026]),
  (2, [t99, t128, t171, t217, t272, t290], [1800780, 600833, 3001053]),
  (3, [t8, t99, t128, t171, t172, t217, t272], []),
  (3, [t24, t28, t99, t128, t171, t272, t317], []),
  (3, [t39, t88, t99, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t262, t272, t317], [3900268]),
  (3, [t69, t99, t128, t171, t217, t272, t317], []),
  (3, [t88, t128, t154, t171, t217, t272, t317], [3801166, 7800269]),
  (3, [t99, t128, t157, t171, t217, t272, t334], []),
  (3, [t99, t128, t171, t217, t220, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t303, t342], []),
  (3, [t10, t99, t128, t171, t217, t297], []),
  (3, [t74, t99, t128, t192, t217, t272], []),
  (3, [t99, t115, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t242, t272, t286], []),
  (3, [t99, t153, t171, t242, t297], [2200050, 5800991])]

def fam39 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t286, t317], [7100294, 4300661, 3100996, 3100084, 3100387, 1100962, 3100786, 1600007, 1600439, 7200203, 6600024, 6800522, 1600219, 4600792, 1600634, 1600362, 4600377, 1600746, 1600378, 8600593, 4600314, 3600298, 1601130]),
  (2, [t99, t128, t171, t217, t272, t322], [1600209, 1600800, 6600112]),
  (3, [t8, t99, t128, t171, t194, t217, t272], []),
  (3, [t24, t99, t128, t171, t217, t272, t317], []),
  (3, [t39, t99, t103, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t266, t272, t317], []),
  (3, [t70, t88, t99, t128, t171, t217, t272], [3001004, 7000556]),
  (3, [t91, t99, t128, t171, t217, t272, t317], [6600112]),
  (3, [t99, t128, t157, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t217, t221, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t304, t317], []),
  (3, [t17, t39, t88, t99, t128, t217], []),
  (3, [t77, t99, t128, t171, t242, t272], []),
  (3, [t99, t118, t128, t171, t242, t272], []),
  (3, [t99, t128, t171, t242, t272, t297], [8200799, 9000431]),
  (3, [t99, t154, t171, t210, t290], [7800911])]

def fam40 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t297, t317], [2900310, 100677, 8901012, 8900100, 8900403, 2500930, 8900802, 5200507, 7400023, 4400203, 7000055, 6800522, 7400455, 7000008, 5400776, 7400267, 7400808, 7400650, 7400490, 5400361, 7400299, 7400465, 8200425, 3400393, 1400762, 7400506, 5400042, 7400395, 3400609, 9400442, 4200426, 5401146]),
  (2, [t99, t128, t171, t217, t272, t324], [600337, 6600128, 8600206]),
  (3, [t8, t99, t128, t171, t205, t217, t272], []),
  (3, [t25, t28, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t108, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t276, t317], []),
  (3, [t70, t99, t128, t171, t217, t272, t336], []),
  (3, [t94, t99, t128, t171, t217, t272, t317], [6600112, 4600641]),
  (3, [t99, t128, t157, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t222, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t307, t317], []),
  (3, [t17, t49, t88, t99, t171, t217], []),
  (3, [t78, t94, t128, t171, t217, t272], [9601153]),
  (3, [t99, t122, t128, t171, t217, t270], []),
  (3, [t99, t128, t171, t242, t272, t303], [9600223]),
  (3, [t99, t154, t171, t217, t293], [8801183])]

def fam41 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t303, t317], [6100326, 3300693, 2101028, 2100116, 2100419, 2100818, 7600219, 6600087, 1600634, 600471, 6200267, 9000040, 7400650, 600602, 8600441, 600778, 600618, 8600554, 601162]),
  (2, [t99, t128, t171, t217, t272, t325], [600353, 8600190, 6600144]),
  (3, [t8, t99, t128, t171, t208, t217, t272], []),
  (3, [t25, t99, t128, t171, t217, t272, t317], []),
  (3, [t39, t99, t112, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t286, t317], []),
  (3, [t70, t99, t128, t171, t217, t272, t342], [3000238]),
  (3, [t94, t99, t128, t171, t217, t272, t336], [4600798]),
  (3, [t99, t128, t157, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t217, t224, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t308, t317], []),
  (3, [t17, t60, t88, t128, t171, t217], []),
  (3, [t78, t99, t128, t171, t242, t272], []),
  (3, [t99, t122, t128, t171, t242, t272], []),
  (3, [t99, t128, t171, t242, t272, t311], []),
  (3, [t99, t154, t171, t242, t297], [7601007])]

def fam42 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t311, t317], [6100342, 3300709, 2101044, 2100132, 2100435, 2100834, 6600103, 1600746, 600487, 6200299, 5000056, 1400762, 8600840, 600778, 600714, 600730, 8600666, 601178]),
  (2, [t99, t128, t171, t217, t272, t329], [1800285, 6600128]),
  (3, [t8, t99, t128, t171, t212, t217, t272], [4100497]),
  (3, [t26, t28, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t118, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t297, t317], []),
  (3, [t70, t99, t128, t171, t217, t279, t317], []),
  (3, [t96, t99, t128, t171, t217, t272, t317], [4600913, 6600112, 4600657]),
  (3, [t99, t128, t159, t171, t217, t272, t317], [4600897]),
  (3, [t99, t128, t171, t217, t226, t272, t317], [8600206]),
  (3, [t99, t128, t171, t217, t272, t309, t317], [2600561, 6600144]),
  (3, [t17, t88, t99, t128, t171, t242], []),
  (3, [t80, t88, t128, t171, t217, t272], [9601153]),
  (3, [t99, t125, t128, t171, t217, t270], [7801185]),
  (3, [t99, t128, t171, t242, t272, t312], []),
  (3, [t113, t154, t171, t242, t272], [601215, 6601151, 8601023])]

def fam43 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t317, t328], [7100374, 4300741, 3101076, 3100164, 3100467, 3100850, 1100130, 1600503, 7200331, 2600152, 800986, 1601194, 4600904, 1601034, 1601210, 4600505, 1601082, 4600058, 1601130]),
  (2, [t99, t128, t171, t217, t272, t330], [5800301, 6600144]),
  (3, [t8, t99, t128, t171, t217, t218, t272], []),
  (3, [t26, t99, t128, t171, t217, t272, t317], []),
  (3, [t39, t99, t122, t128, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t303, t317], []),
  (3, [t70, t99, t128, t171, t217, t297, t317], []),
  (3, [t96, t99, t128, t171, t217, t272, t342], [2600750, 2600429]),
  (3, [t99, t128, t160, t171, t217, t272, t317], [9400945]),
  (3, [t99, t128, t171, t217, t228, t244, t317], [9600478, 2601229]),
  (3, [t99, t128, t171, t217, t272, t310, t317], []),
  (3, [t17, t88, t128, t154, t171, t217], []),
  (3, [t81, t99, t128, t171, t242, t272], []),
  (3, [t99, t126, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t242, t272, t328], []),
  (3, [t128, t154, t171, t227, t242], [1001135, 3001023])]

def fam44 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t317, t332], [8900390, 6100757, 4901092, 4900180, 4900483, 4900866, 3400519, 5000631, 800986, 9000347, 3401226, 3400920, 3401050, 3400011, 9400521, 7401098, 1400074, 5401146]),
  (2, [t99, t128, t171, t217, t272, t334], [8600317, 6600128, 6600144]),
  (3, [t8, t99, t128, t171, t217, t244, t272], []),
  (3, [t27, t28, t99, t128, t171, t217, t272], [9101152]),
  (3, [t39, t99, t128, t132, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t311, t317], []),
  (3, [t70, t99, t154, t171, t217, t272, t317], []),
  (3, [t98, t99, t128, t171, t217, t272, t317], [6600112]),
  (3, [t99, t128, t161, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t228, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t311, t336], []),
  (3, [t17, t94, t99, t128, t171, t217], []),
  (3, [t82, t94, t128, t171, t217, t272], []),
  (3, [t99, t126, t171, t217, t272, t347], []),
  (3, [t99, t128, t171, t242, t272, t332], []),
  (3, [t128, t154, t171, t242, t297], [2201039])]

def fam45 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t317, t336], [6100406, 3300773, 2101108, 2100196, 2100499, 2100882, 600535, 7601194, 6600647, 1601034, 6200363, 8200088, 8201226, 3000168, 3401050, 8600856, 8600457, 600059, 8600537, 601114, 8600010, 600091, 8600090, 601162]),
  (2, [t99, t128, t171, t217, t272, t335], [8600333, 6600128]),
  (3, [t8, t99, t128, t171, t217, t252, t272], []),
  (3, [t27, t28, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t154, t217, t272, t317], [8301067, 9301227]),
  (3, [t49, t99, t171, t217, t272, t317, t321], []),
  (3, [t71, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t100, t128, t171, t217, t272, t317], [6600112]),
  (3, [t99, t128, t162, t171, t217, t272, t335], []),
  (3, [t99, t128, t171, t217, t231, t272, t317], [2600764, 8600513, 2600014]),
  (3, [t99, t128, t171, t217, t272, t311, t342], []),
  (3, [t17, t96, t99, t128, t171, t217], [1101057]),
  (3, [t82, t99, t128, t171, t210, t317], []),
  (3, [t99, t128, t135, t171, t217, t272], []),
  (3, [t99, t128, t171, t242, t272, t336], []),
  (3, [t128, t154, t171, t243, t272], [5801167])]

def fam46 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t317, t342], [6100422, 3300789, 2101124, 2100212, 2100515, 2100898, 8100082, 7600443, 600551, 7601210, 6600679, 1601082, 6200379, 8200104, 8200011, 9000200, 7401098, 8600872, 600059, 8600936, 601114, 8600473, 8600026, 600171, 2600561, 6600154, 8600122, 601178]),
  (2, [t99, t128, t171, t217, t272, t340], [8600413, 6200398, 600222, 6600144]),
  (3, [t8, t99, t128, t171, t217, t262, t272], []),
  (3, [t27, t99, t128, t171, t217, t272, t317], []),
  (3, [t39, t99, t128, t157, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t317, t328], []),
  (3, [t72, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t101, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t162, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t217, t237, t272, t317], [8600513]),
  (3, [t99, t128, t171, t217, t272, t313, t317], []),
  (3, [t17, t99, t128, t171, t217, t239], [1101057]),
  (3, [t82, t99, t128, t171, t242, t272], []),
  (3, [t99, t128, t136, t171, t217, t272], []),
  (3, [t99, t128, t171, t242, t272, t342], []),
  (3, [t154, t171, t217, t234, t317], [2201087])]

def fam47 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t99, t128, t171, t217, t272, t317, t348], [6100438, 3300805, 2101140, 2100228, 2100531, 2100914, 600567, 6600711, 1601130, 6200395, 1000232, 5401146, 600091, 8600968, 601162, 600171, 8600569, 601178]),
  (2, [t99, t128, t171, t217, t272, t347], [1300268, 101163, 100907, 100779, 5600830, 9601153, 7600557, 2600493, 4200430, 3800717, 8600158]),
  (3, [t8, t99, t128, t171, t217, t266, t272], []),
  (3, [t28, t39, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t162, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t317, t332], []),
  (3, [t73, t88, t99, t128, t171, t217, t272], [9000029, 601116, 601020, 600572]),
  (3, [t99, t102, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t162, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t239, t244, t272], [3600510, 2601229]),
  (3, [t99, t128, t171, t217, t272, t315, t317], []),
  (3, [t17, t99, t128, t171, t217, t242], []),
  (3, [t82, t128, t171, t217, t231, t317], []),
  (3, [t99, t128, t141, t171, t217, t272], [8600176]),
  (3, [t99, t128, t171, t242, t272, t348], []),
  (3, [t154, t171, t217, t239, t297], [5000050])]

def fam48 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t0, t99, t128, t171, t217, t272], [6600144, 4100497]),
  (2, [t99, t128, t171, t217, t279, t317], [9801004, 2200160, 9800238]),
  (3, [t8, t99, t128, t171, t217, t272, t273], []),
  (3, [t28, t39, t99, t128, t217, t272, t317], []),
  (3, [t39, t99, t128, t166, t217, t272, t317], []),
  (3, [t49, t99, t171, t217, t272, t317, t336], []),
  (3, [t73, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t103, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t162, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t217, t239, t272, t317], [4600913]),
  (3, [t99, t128, t171, t217, t272, t316, t317], []),
  (3, [t17, t99, t128, t171, t217, t347], []),
  (3, [t83, t99, t128, t171, t217, t272], []),
  (3, [t99, t128, t142, t171, t217, t272], [8600176]),
  (3, [t99, t128, t171, t242, t297, t317], [8200815, 9000463]),
  (3, [t154, t171, t217, t242, t297], [])]

def fam49 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t1, t99, t128, t171, t217, t272], [6600128, 4100401]),
  (2, [t99, t128, t171, t217, t281, t317], [8601036]),
  (3, [t8, t99, t128, t171, t217, t272, t286], []),
  (3, [t28, t49, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t171, t217, t272, t336], [4601200]),
  (3, [t49, t99, t171, t217, t272, t317, t342], []),
  (3, [t74, t88, t99, t128, t171, t217, t272], [600337, 7800045, 2601132, 2601036, 2600620, 2600604]),
  (3, [t99, t104, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t163, t171, t217, t272, t317], [4600785]),
  (3, [t99, t128, t171, t217, t240, t272, t317], [8600529]),
  (3, [t99, t128, t171, t217, t272, t317, t318], []),
  (3, [t17, t99, t128, t171, t244, t342], [1101057]),
  (3, [t83, t99, t128, t171, t217, t297], [9000591, 7000511, 9800191, 5000175]),
  (3, [t99, t128, t153, t171, t242, t272], [5000018, 1000623]),
  (3, [t99, t128, t171, t243, t272, t336], []),
  (3, [t154, t171, t242, t272, t297], [])]

def fam50 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t3, t99, t128, t171, t217, t272], [7100625]),
  (2, [t99, t128, t171, t217, t287, t317], [7001052, 2200160]),
  (3, [t8, t99, t128, t171, t217, t272, t297], []),
  (3, [t28, t49, t99, t171, t217, t272, t317], []),
  (3, [t39, t99, t128, t171, t217, t272, t342], [7101163]),
  (3, [t49, t99, t171, t217, t272, t317, t348], []),
  (3, [t74, t99, t128, t171, t217, t272, t324], []),
  (3, [t99, t105, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t164, t171, t217, t272, t317], [7400801]),
  (3, [t99, t128, t171, t217, t242, t272, t317], [6601197, 8600750, 8600529, 6600144]),
  (3, [t99, t128, t171, t217, t272, t317, t319], []),
  (3, [t20, t88, t99, t128, t171, t272], []),
  (3, [t84, t99, t128, t171, t210, t317], [6200175, 3000207]),
  (3, [t99, t128, t154, t171, t242, t272], [2800671]),
  (3, [t99, t128, t171, t244, t270, t342], []),
  (3, [t154, t171, t242, t297, t317], [])]

def fam51 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t8, t17, t99, t128, t171, t217], [3100032, 3100016]),
  (2, [t99, t128, t171, t217, t288, t317], [5001068, 2200160]),
  (3, [t8, t99, t128, t171, t217, t272, t303], []),
  (3, [t28, t60, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t171, t217, t297, t317], []),
  (3, [t50, t99, t128, t171, t217, t272, t317], []),
  (3, [t74, t99, t128, t171, t217, t272, t336], []),
  (3, [t99, t106, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t164, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t217, t244, t272, t336], [3600830, 8600078]),
  (3, [t99, t128, t171, t217, t272, t317, t320], []),
  (3, [t20, t99, t128, t171, t242, t272], []),
  (3, [t84, t154, t171, t217, t297, t317], [8200191, 200207]),
  (3, [t99, t128, t157, t171, t242, t272], []),
  (3, [t99, t128, t171, t244, t272, t347], [600002]),
  (3, [t154, t171, t244, t297, t342], [4201087, 5000050, 8401183])]

def fam52 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t8, t28, t99, t128, t171, t272], [3100048, 3100016]),
  (2, [t99, t128, t171, t217, t290, t297], [5300460, 2500284, 1301179, 100619, 7601006, 6600796, 9800366, 1800382, 9801169, 601101, 5801085]),
  (3, [t8, t99, t128, t171, t217, t272, t311], []),
  (3, [t28, t60, t128, t171, t217, t272, t317], []),
  (3, [t39, t99, t128, t194, t217, t272, t317], []),
  (3, [t51, t99, t128, t171, t217, t272, t317], [3000097]),
  (3, [t74, t99, t128, t171, t217, t272, t342], [7800894, 8600206, 1600588]),
  (3, [t99, t107, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t165, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t244, t272, t342], [4600545]),
  (3, [t99, t128, t171, t217, t272, t317, t321], []),
  (3, [t22, t99, t128, t171, t217, t272], [8600176]),
  (3, [t85, t88, t128, t171, t217, t272], [3600271, 1600239, 1600223]),
  (3, [t99, t128, t158, t171, t242, t272], []),
  (3, [t99, t128, t171, t244, t297, t342], [3200831, 2600479, 3401217, 6800575]),
  (3, [t21, t99, t128, t171], [])]

def fam53 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t8, t39, t99, t128, t217, t272], [3100064, 3100016]),
  (2, [t99, t128, t171, t217, t295, t317], [3001084, 2200160, 3000318]),
  (3, [t8, t99, t128, t171, t217, t272, t328], [1600800]),
  (3, [t28, t70, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t205, t217, t272, t317], []),
  (3, [t52, t99, t128, t171, t217, t272, t317], []),
  (3, [t74, t99, t128, t171, t217, t281, t317], []),
  (3, [t99, t108, t128, t171, t217, t272, t329], []),
  (3, [t99, t128, t166, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t217, t244, t297, t317], [1201214, 400846, 600046, 3400062]),
  (3, [t99, t128, t171, t217, t272, t317, t322], []),
  (3, [t28, t61, t99, t128, t171, t272], [8101073]),
  (3, [t86, t128, t171, t217, t297, t317], []),
  (3, [t99, t128, t162, t171, t242, t272], []),
  (3, [t99, t128, t192, t205, t217, t272], []),
  (3, [t39, t99, t128, t232], [])]

def fam54 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t8, t49, t99, t171, t217, t272], [9900080, 8700016]),
  (2, [t99, t128, t171, t217, t297, t336], [7201022, 5400349, 201133, 9400430, 600254]),
  (3, [t8, t99, t128, t171, t217, t272, t332], []),
  (3, [t28, t74, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t208, t217, t272, t317], []),
  (3, [t53, t99, t128, t171, t217, t272, t317], []),
  (3, [t74, t99, t128, t171, t217, t297, t317], []),
  (3, [t99, t108, t128, t171, t217, t272, t336], []),
  (3, [t99, t128, t166, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t245, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t323], []),
  (3, [t28, t88, t99, t128, t171, t297], []),
  (3, [t88, t99, t128, t130, t171, t217], []),
  (3, [t99, t128, t166, t171, t242, t272], []),
  (3, [t99, t128, t192, t217, t272, t303], [9600239]),
  (3, [t39, t154, t242, t297], [])]

def fam55 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t8, t60, t128, t171, t217, t272], [9100096, 5100016]),
  (2, [t99, t128, t171, t217, t297, t342], [4900476, 2100300, 901195, 900923, 7201038, 6400846, 5400445, 9400430, 201165, 7801185, 1800286, 8600270]),
  (3, [t8, t99, t128, t171, t217, t272, t336], []),
  (3, [t28, t78, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t212, t217, t272, t317], []),
  (3, [t54, t60, t128, t171, t217, t272, t317], []),
  (3, [t74, t99, t128, t171, t226, t272, t317], []),
  (3, [t99, t108, t128, t171, t217, t272, t342], []),
  (3, [t99, t128, t166, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t217, t246, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t324], []),
  (3, [t28, t88, t128, t154, t171, t272], []),
  (3, [t88, t99, t128, t171, t185, t217], []),
  (3, [t99, t128, t171, t180, t217, t317], []),
  (3, [t99, t139, t171, t217, t272, t342], []),
  (3, [t43, t171, t242, t297], [])]

def fam56 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t8, t99, t128, t171, t217, t297], [5400160]),
  (2, [t99, t128, t171, t226, t272, t317], [8601132, 600446]),
  (3, [t8, t99, t128, t171, t217, t272, t342], []),
  (3, [t28, t82, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t220, t272, t317], []),
  (3, [t54, t99, t128, t171, t217, t272, t317], []),
  (3, [t74, t99, t139, t171, t217, t272, t317], []),
  (3, [t99, t108, t128, t171, t217, t287, t317], []),
  (3, [t99, t128, t167, t171, t217, t272, t317], [4600641]),
  (3, [t99, t128, t171, t217, t247, t272, t317], [7400465, 2200160]),
  (3, [t99, t128, t171, t217, t272, t317, t325], []),
  (3, [t28, t99, t128, t171, t272, t347], []),
  (3, [t88, t99, t128, t171, t210, t272], []),
  (3, [t99, t128, t171, t181, t217, t272], [8600176]),
  (3, [t99, t149, t171, t208, t217, t317], []),
  (3, [t83, t154, t171, t210], [4600066])]

def fam57 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t9, t99, t128, t171, t217, t317], [2200160, 5700369, 2100603, 4300587]),
  (2, [t99, t128, t171, t242, t272, t317], [1001166, 8600305, 5600702, 4200782, 6200669, 6200718, 6600877, 8600734, 600494, 8600750, 6600590, 8600766]),
  (3, [t8, t99, t128, t171, t217, t272, t348], []),
  (3, [t28, t88, t99, t128, t171, t217, t272], [2600843]),
  (3, [t39, t99, t128, t217, t244, t272, t317], [8101211, 1101131]),
  (3, [t55, t60, t128, t171, t217, t272, t317], []),
  (3, [t74, t128, t171, t194, t217, t272, t317], []),
  (3, [t99, t108, t128, t171, t217, t297, t317], []),
  (3, [t99, t128, t168, t171, t217, t272, t317], [3400673]),
  (3, [t99, t128, t171, t217, t248, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t327], []),
  (3, [t28, t99, t128, t171, t297, t342], []),
  (3, [t88, t99, t128, t171, t210, t297], [8600495, 6200175, 4600287]),
  (3, [t99, t128, t171, t182, t217, t272], [8600176]),
  (3, [t99, t149, t171, t217, t272, t336], []),
  (3, [t88, t154, t171, t232], [])]

def fam58 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t28, t99, t128, t171, t317], [3100048, 3100032]),
  (2, [t99, t128, t171, t244, t272, t342], [9100492, 6300316, 5101211, 5100795, 6001182, 9200846, 3600830, 5600478, 8600176, 2600750, 3600510, 9600814]),
  (3, [t9, t99, t128, t171, t217, t272, t317], []),
  (3, [t28, t88, t99, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t252, t272, t317], []),
  (3, [t55, t99, t128, t171, t217, t272, t317], []),
  (3, [t75, t99, t128, t171, t217, t272, t317], [9800977]),
  (3, [t99, t108, t128, t171, t245, t272, t317], []),
  (3, [t99, t128, t169, t171, t217, t272, t317], [8600705]),
  (3, [t99, t128, t171, t217, t249, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t329], []),
  (3, [t28, t99, t154, t171, t297, t317], []),
  (3, [t88, t99, t128, t171, t217, t227], [6601201]),
  (3, [t99, t128, t171, t185, t217, t336], []),
  (3, [t99, t149, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t233], [])]

def fam59 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t39, t99, t128, t217, t317], [3100064, 3100032, 1600635]),
  (2, [t99, t128, t171, t245, t272, t317], [3001196]),
  (3, [t9, t99, t128, t171, t217, t297, t317], []),
  (3, [t28, t99, t102, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t262, t272, t317], [7101163]),
  (3, [t56, t60, t128, t171, t217, t272, t317], []),
  (3, [t76, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t108, t128, t205, t217, t272, t317], []),
  (3, [t99, t128, t169, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t217, t250, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t330], []),
  (3, [t30, t99, t128, t171, t297, t317], []),
  (3, [t88, t99, t128, t171, t217, t228], []),
  (3, [t99, t128, t171, t190, t217, t297], []),
  (3, [t99, t150, t171, t217, t272, t317], [800271]),
  (3, [t99, t128, t189, t210], [])]

def fam60 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t49, t99, t171, t217, t317], [9900080, 8700032, 8400651]),
  (2, [t99, t128, t197, t217, t272, t317], [9000013]),
  (3, [t11, t99, t128, t171, t217, t272, t317], []),
  (3, [t28, t99, t108, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t266, t272, t317], []),
  (3, [t56, t99, t128, t171, t217, t272, t317], []),
  (3, [t77, t88, t99, t128, t171, t217, t272], [600636]),
  (3, [t99, t108, t171, t205, t217, t272, t317], []),
  (3, [t99, t128, t170, t171, t217, t272, t317], [8600721]),
  (3, [t99, t128, t171, t217, t251, t272, t317], [6600144]),
  (3, [t99, t128, t171, t217, t272, t317, t331], []),
  (3, [t33, t39, t99, t128, t217, t272], []),
  (3, [t88, t99, t128, t171, t217, t270], []),
  (3, [t99, t128, t171, t192, t217, t297], []),
  (3, [t99, t151, t154, t171, t217, t297], [3001137]),
  (3, [t99, t128, t198, t227], [])]

def fam61 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t60, t128, t171, t217, t317], [9100096, 5100032]),
  (2, [t99, t139, t171, t217, t272, t317], [7400045, 7400894]),
  (3, [t12, t17, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t112, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t275, t317], []),
  (3, [t58, t60, t128, t171, t217, t272, t317], []),
  (3, [t77, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t109, t128, t171, t217, t272, t317], [9801025]),
  (3, [t99, t128, t171, t172, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t252, t272, t336], []),
  (3, [t99, t128, t171, t217, t272, t317, t333], []),
  (3, [t33, t99, t128, t171, t217, t272], []),
  (3, [t88, t99, t128, t171, t217, t278], []),
  (3, [t99, t128, t171, t192, t242, t272], []),
  (3, [t99, t154, t171, t210, t297, t317], [3000207, 3400287, 2400639]),
  (3, [t99, t153, t171, t232], [2600066])]

def fam62 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t88, t99, t128, t171, t217], [8600112, 2600667, 9800651, 8600635, 3700876, 1101057, 7100763, 5100683, 9500699]),
  (2, [t99, t149, t171, t217, t272, t317], [5400077, 1000942, 5400926, 3400910]),
  (3, [t12, t99, t128, t171, t217, t272, t317], []),
  (3, [t28, t99, t118, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t286, t317], []),
  (3, [t58, t99, t128, t171, t217, t272, t317], []),
  (3, [t78, t88, t99, t128, t171, t217, t272], [600353, 2600668]),
  (3, [t99, t110, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t173, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t252, t272, t342], []),
  (3, [t99, t128, t171, t217, t272, t317, t334], []),
  (3, [t39, t49, t88, t99, t217, t272], []),
  (3, [t88, t99, t128, t171, t217, t279], []),
  (3, [t99, t128, t171, t193, t217, t272], [9601153]),
  (3, [t99, t154, t171, t217, t290, t297], [8200191, 4400639]),
  (3, [t99, t154, t171, t232], [])]

def fam63 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t99, t128, t171, t217, t336], [8600128, 3100715, 7100779]),
  (2, [t99, t154, t171, t217, t297, t317], [5900028, 7501227, 7500939, 1100603, 6001198, 6001214, 3400828, 3001137, 9000269, 6000109, 600942, 1200974, 6001022, 6800990, 6001038, 2801006]),
  (3, [t13, t17, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t122, t128, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t297, t317], []),
  (3, [t59, t60, t128, t171, t217, t272, t317], []),
  (3, [t78, t99, t128, t171, t217, t272, t325], []),
  (3, [t99, t111, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t174, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t252, t297, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t335], []),
  (3, [t39, t60, t88, t128, t217, t272], []),
  (3, [t88, t99, t128, t171, t217, t280], []),
  (3, [t99, t128, t171, t194, t242, t272], []),
  (3, [t99, t154, t171, t217, t297, t336], [7000319]),
  (3, [t113, t154, t171, t227], [4600066])]

def fam64 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t17, t99, t128, t171, t217, t342], [8600144, 4100795, 3100731, 7100779]),
  (2, [t128, t137, t171, t217, t272, t317], [7801054]),
  (3, [t13, t99, t128, t171, t217, t272, t317], [2200160]),
  (3, [t28, t99, t128, t131, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t303, t317], []),
  (3, [t59, t99, t128, t171, t217, t272, t317], []),
  (3, [t78, t99, t128, t171, t217, t272, t336], [8600190, 1600652]),
  (3, [t99, t112, t128, t171, t208, t272, t317], [7400465]),
  (3, [t99, t128, t171, t175, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t255, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t338], []),
  (3, [t39, t88, t99, t128, t217, t297], [5900079, 6700063]),
  (3, [t88, t99, t128, t171, t217, t281], []),
  (3, [t99, t128, t171, t205, t242, t272], []),
  (3, [t99, t154, t171, t217, t297, t342], [8000831, 7000335, 2400655]),
  (3, [t128, t154, t171, t232], [])]

def fam65 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t27, t28, t99, t128, t171, t272], [2601056]),
  (2, [t128, t143, t171, t217, t272, t317], [1801070]),
  (3, [t14, t17, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t154, t171, t272, t317], [8300891, 9300939]),
  (3, [t39, t99, t128, t217, t272, t311, t317], []),
  (3, [t60, t70, t128, t171, t217, t272, t317], []),
  (3, [t78, t99, t128, t171, t217, t272, t342], []),
  (3, [t99, t112, t128, t171, t217, t272, t330], []),
  (3, [t99, t128, t171, t176, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t256, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t339], []),
  (3, [t39, t88, t99, t128, t242, t272], []),
  (3, [t88, t99, t128, t171, t217, t287], []),
  (3, [t99, t128, t171, t208, t217, t290], []),
  (3, [t128, t135, t137, t171, t217, t272], []),
  (3, [t154, t171, t232, t242], [])]

def fam66 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t27, t99, t128, t171, t217, t272], [4100497, 101040, 2600843, 6600144]),
  (2, [t17, t99, t128, t171, t242], [6600176]),
  (3, [t14, t99, t128, t171, t217, t272, t317], []),
  (3, [t28, t99, t128, t157, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t317, t320], []),
  (3, [t60, t74, t128, t171, t217, t272, t317], []),
  (3, [t78, t99, t128, t171, t217, t297, t317], []),
  (3, [t99, t112, t128, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t178, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t257, t272, t317], [600222]),
  (3, [t99, t128, t171, t217, t272, t317, t340], [2600561]),
  (3, [t39, t88, t128, t154, t217, t272], [300095, 4300063]),
  (3, [t88, t99, t128, t171, t217, t288], []),
  (3, [t99, t128, t171, t208, t242, t272], []),
  (3, [t128, t141, t143, t171, t217, t272], []),
  (3, [t154, t171, t232, t297], [])]

def fam67 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t39, t99, t128, t272, t317], [3100064, 3100048]),
  (2, [t20, t99, t128, t171, t272], [8600176, 3500047, 6700031]),
  (3, [t15, t17, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t162, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t317, t328], []),
  (3, [t60, t78, t128, t171, t217, t272, t317], []),
  (3, [t78, t99, t128, t171, t244, t272, t317], []),
  (3, [t99, t112, t128, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t179, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t258, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t344], []),
  (3, [t39, t94, t99, t128, t217, t272], []),
  (3, [t88, t99, t128, t171, t217, t295], []),
  (3, [t99, t128, t171, t210, t217, t290], [7801185]),
  (3, [t128, t145, t171, t217, t272, t317], []),
  (3, [t154, t171, t234, t342], [4600066])]

def fam68 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t49, t99, t171, t272, t317], [9900080, 8700048]),
  (2, [t39, t99, t128, t242, t272], [6600176, 7500095, 700079]),
  (3, [t15, t99, t128, t171, t217, t272, t317], []),
  (3, [t28, t99, t128, t166, t171, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t317, t332], []),
  (3, [t60, t82, t128, t171, t217, t272, t317], []),
  (3, [t79, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t112, t128, t171, t217, t288, t317], []),
  (3, [t99, t128, t171, t183, t217, t272, t317], [2600893, 2600909]),
  (3, [t99, t128, t171, t217, t259, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t317, t345], []),
  (3, [t39, t96, t99, t128, t217, t272], [1101089]),
  (3, [t88, t99, t128, t171, t223, t272], [8600176]),
  (3, [t99, t128, t171, t210, t290, t297], []),
  (3, [t128, t154, t171, t190, t217, t272], []),
  (3, [t154, t171, t235, t297], [4600066])]

def fam69 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t60, t128, t171, t272, t317], [9100096, 5100048]),
  (2, [t49, t99, t171, t242, t272], [2200176]),
  (3, [t16, t17, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t174, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t317, t336], []),
  (3, [t60, t88, t99, t128, t171, t217, t272], [7100625]),
  (3, [t80, t99, t128, t171, t217, t272, t317], [4600897, 6600174, 9600684]),
  (3, [t99, t112, t128, t171, t217, t297, t317], []),
  (3, [t99, t128, t171, t184, t217, t272, t317], [8600190]),
  (3, [t99, t128, t171, t217, t260, t272, t317], [6600128]),
  (3, [t99, t128, t171, t217, t272, t317, t347], []),
  (3, [t39, t99, t128, t210, t297, t317], []),
  (3, [t88, t99, t128, t171, t225, t272], [8600176]),
  (3, [t99, t128, t171, t210, t290, t317], []),
  (3, [t128, t154, t171, t192, t217, t272], []),
  (3, [t154, t171, t238, t297], [4600066])]

def fam70 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t88, t99, t128, t171, t272], [8600112, 4600859, 9500891, 2700875]),
  (2, [t60, t128, t171, t242, t272], [8600176, 6700159]),
  (3, [t16, t99, t128, t171, t217, t272, t317], []),
  (3, [t28, t99, t128, t171, t194, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t317, t342], []),
  (3, [t60, t88, t128, t171, t217, t272, t317], []),
  (3, [t81, t88, t99, t128, t171, t217, t272], [7000061, 601228, 601164, 600700]),
  (3, [t99, t112, t128, t171, t252, t272, t317], []),
  (3, [t99, t128, t171, t185, t194, t217, t317], []),
  (3, [t99, t128, t171, t217, t261, t272, t317], [6600144]),
  (3, [t99, t128, t171, t217, t272, t317, t349], []),
  (3, [t39, t99, t128, t217, t239, t272], [1101089]),
  (3, [t88, t99, t128, t171, t226, t272], [600002]),
  (3, [t99, t128, t171, t210, t297, t336], []),
  (3, [t128, t154, t171, t217, t239, t272], [7800767, 7800018]),
  (3, [t154, t171, t242, t253], [4600066])]

def fam71 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t99, t128, t171, t272, t336], [8600128]),
  (2, [t88, t154, t171, t217, t297], [900111, 2500063, 6101230, 5000050, 1000783, 9000303, 8200191, 1800287]),
  (3, [t17, t28, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t205, t272, t317], []),
  (3, [t39, t99, t128, t217, t272, t317, t348], []),
  (3, [t60, t99, t128, t171, t217, t272, t322], [5100193]),
  (3, [t81, t99, t128, t171, t217, t272, t317], []),
  (3, [t99, t112, t128, t197, t217, t272, t317], []),
  (3, [t99, t128, t171, t185, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t262, t272, t336], [4600753]),
  (3, [t99, t128, t171, t217, t272, t317, t350], []),
  (3, [t39, t99, t128, t217, t242, t272], []),
  (3, [t88, t99, t128, t171, t227, t242], []),
  (3, [t99, t128, t171, t210, t297, t341], []),
  (3, [t128, t154, t171, t217, t242, t272], [5800783]),
  (3, [t154, t171, t242, t289], [4600066])]

def fam72 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t99, t128, t171, t272, t342], [8600144, 7101040, 2700923, 7100907]),
  (2, [t97, t128, t171, t217, t272], []),
  (3, [t17, t39, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t208, t272, t317], []),
  (3, [t40, t99, t128, t171, t217, t272, t317], [4601200]),
  (3, [t60, t99, t128, t171, t217, t272, t336], [9100380]),
  (3, [t82, t88, t99, t128, t171, t217, t272], [3800077, 2600748]),
  (3, [t99, t114, t128, t171, t217, t272, t317], [3801041]),
  (3, [t99, t128, t171, t186, t217, t272, t317], [8600417]),
  (3, [t99, t128, t171, t217, t262, t272, t342], [4600753]),
  (3, [t99, t128, t171, t217, t272, t317, t351], []),
  (3, [t39, t99, t128, t217, t272, t347], []),
  (3, [t88, t99, t128, t171, t236, t272], [8600176]),
  (3, [t99, t128, t171, t210, t297, t342], []),
  (3, [t128, t154, t171, t242, t272, t317], [5800815]),
  (3, [t154, t171, t243, t297], [])]

def fam73 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t28, t99, t128, t171, t297, t317], [5400160, 1700939, 3900875]),
  (2, [t99, t128, t171, t210, t290], [7200639, 6200175]),
  (3, [t17, t49, t99, t128, t171, t217, t317], [6500912]),
  (3, [t28, t99, t128, t171, t212, t272, t317], []),
  (3, [t41, t99, t128, t171, t217, t272, t317], []),
  (3, [t60, t99, t128, t171, t217, t272, t342], [100492, 9100396]),
  (3, [t82, t99, t128, t162, t171, t217, t317], [8600417]),
  (3, [t99, t115, t128, t171, t217, t272, t317], [3401086, 1400961, 9400945, 1800621]),
  (3, [t99, t128, t171, t188, t217, t272, t317], [8600417]),
  (3, [t99, t128, t171, t217, t262, t272, t347], [3600509]),
  (3, [t99, t128, t171, t217, t272, t317, t352], []),
  (3, [t39, t99, t128, t217, t290, t297], []),
  (3, [t88, t99, t128, t171, t242, t297], [4600623, 6200303, 7000255]),
  (3, [t99, t128, t171, t210, t307, t317], []),
  (3, [t128, t154, t171, t244, t272, t342], [800831, 7800018]),
  (3, [t154, t171, t244, t293], [4600066])]

def fam74 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t38, t39, t99, t128, t217, t272], [2601200, 5100971]),
  (2, [t99, t128, t171, t217, t293], [8000655, 7200575]),
  (3, [t17, t60, t99, t128, t171, t217, t317], [7600667]),
  (3, [t28, t99, t128, t171, t217, t272, t336], [7100907]),
  (3, [t42, t99, t128, t171, t217, t272, t317], []),
  (3, [t60, t99, t128, t171, t217, t297, t317], [9900348]),
  (3, [t82, t99, t128, t171, t208, t217, t317], [7800910, 8600513, 2600764]),
  (3, [t99, t117, t128, t171, t217, t272, t317], []),
  (3, [t99, t128, t171, t190, t194, t217, t272], []),
  (3, [t99, t128, t171, t217, t262, t297, t317], [4200621, 9400430]),
  (3, [t99, t128, t171, t217, t272, t328, t336], [4600641]),
  (3, [t39, t99, t128, t217, t297, t342], []),
  (3, [t88, t99, t128, t171, t245, t272], []),
  (3, [t99, t128, t171, t212, t242, t272], []),
  (3, [t154, t171, t194, t217, t297, t317], []),
  (3, [t154, t189, t217, t297], [])]

def fam75 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t38, t99, t128, t171, t217, t272], [4100401, 101184, 2600987, 6600128]),
  (2, [t99, t128, t171, t227, t242], [3000703, 9400527, 1400351, 600399]),
  (3, [t17, t70, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t217, t272, t342], [4601056]),
  (3, [t43, t99, t128, t171, t217, t272, t317], [5900012, 6900028]),
  (3, [t60, t108, t128, t171, t217, t272, t317], []),
  (3, [t82, t99, t128, t171, t217, t272, t336], [3800926, 1600716]),
  (3, [t99, t118, t128, t171, t217, t272, t336], []),
  (3, [t99, t128, t171, t190, t217, t272, t317], []),
  (3, [t99, t128, t171, t217, t264, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t328, t342], [4600657]),
  (3, [t39, t99, t128, t244, t272, t342], [1101089]),
  (3, [t88, t99, t128, t177, t217, t272], []),
  (3, [t99, t128, t171, t217, t227, t242], []),
  (3, [t154, t171, t217, t244, t297, t317], [2000831, 2200751, 5000767]),
  (3, [t154, t198, t242, t272], [])]

def fam76 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t39, t49, t99, t217, t272, t317], [9900080, 8700064, 8401003]),
  (2, [t99, t128, t171, t242, t297], [2900159, 100143, 8900079, 2900031, 2500015, 2200050, 9800719, 5200671, 3000034, 3800447, 1000415]),
  (3, [t17, t74, t99, t128, t171, t217, t317], []),
  (3, [t28, t99, t128, t171, t217, t297, t317], [3900923]),
  (3, [t44, t49, t99, t171, t217, t272, t317], [7500044]),
  (3, [t60, t112, t128, t171, t217, t272, t317], []),
  (3, [t82, t99, t128, t171, t217, t272, t342], []),
  (3, [t99, t118, t128, t171, t217, t272, t342], []),
  (3, [t99, t128, t171, t191, t217, t272, t317], [8600433]),
  (3, [t99, t128, t171, t217, t265, t272, t317], []),
  (3, [t99, t128, t171, t217, t272, t332, t336], [3400673]),
  (3, [t39, t99, t154, t217, t297, t317], [5500063]),
  (3, [t88, t99, t128, t187, t217, t272], []),
  (3, [t99, t128, t171, t217, t228, t239], []),
  (3, [t9, t88, t154, t171, t217], [])]

def chunk0 : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19]

def chunk1 : List (List (ℕ × List ℕ × List ℕ)) := [fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39]

def chunk2 : List (List (ℕ × List ℕ × List ℕ)) := [fam40, fam41, fam42, fam43, fam44, fam45, fam46, fam47, fam48, fam49, fam50, fam51, fam52, fam53, fam54, fam55, fam56, fam57, fam58, fam59]

def chunk3 : List (List (ℕ × List ℕ × List ℕ)) := [fam60, fam61, fam62, fam63, fam64, fam65, fam66, fam67, fam68, fam69, fam70, fam71, fam72, fam73, fam74, fam75, fam76]

def parts : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19,
  fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39,
  fam40, fam41, fam42, fam43, fam44, fam45, fam46, fam47, fam48, fam49, fam50, fam51, fam52, fam53, fam54, fam55, fam56, fam57, fam58, fam59,
  fam60, fam61, fam62, fam63, fam64, fam65, fam66, fam67, fam68, fam69, fam70, fam71, fam72, fam73, fam74, fam75, fam76]

set_option maxRecDepth 8000 in
theorem parts_eq : parts = chunk0 ++ chunk1 ++ chunk2 ++ chunk3 := rfl

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

theorem ok41 : fam41.all okB = true := by decide +kernel

theorem ok42 : fam42.all okB = true := by decide +kernel

theorem ok43 : fam43.all okB = true := by decide +kernel

theorem ok44 : fam44.all okB = true := by decide +kernel

theorem ok45 : fam45.all okB = true := by decide +kernel

theorem ok46 : fam46.all okB = true := by decide +kernel

theorem ok47 : fam47.all okB = true := by decide +kernel

theorem ok48 : fam48.all okB = true := by decide +kernel

theorem ok49 : fam49.all okB = true := by decide +kernel

theorem ok50 : fam50.all okB = true := by decide +kernel

theorem ok51 : fam51.all okB = true := by decide +kernel

theorem ok52 : fam52.all okB = true := by decide +kernel

theorem ok53 : fam53.all okB = true := by decide +kernel

theorem ok54 : fam54.all okB = true := by decide +kernel

theorem ok55 : fam55.all okB = true := by decide +kernel

theorem ok56 : fam56.all okB = true := by decide +kernel

theorem ok57 : fam57.all okB = true := by decide +kernel

theorem ok58 : fam58.all okB = true := by decide +kernel

theorem ok59 : fam59.all okB = true := by decide +kernel

theorem ok60 : fam60.all okB = true := by decide +kernel

theorem ok61 : fam61.all okB = true := by decide +kernel

theorem ok62 : fam62.all okB = true := by decide +kernel

theorem ok63 : fam63.all okB = true := by decide +kernel

theorem ok64 : fam64.all okB = true := by decide +kernel

theorem ok65 : fam65.all okB = true := by decide +kernel

theorem ok66 : fam66.all okB = true := by decide +kernel

theorem ok67 : fam67.all okB = true := by decide +kernel

theorem ok68 : fam68.all okB = true := by decide +kernel

theorem ok69 : fam69.all okB = true := by decide +kernel

theorem ok70 : fam70.all okB = true := by decide +kernel

theorem ok71 : fam71.all okB = true := by decide +kernel

theorem ok72 : fam72.all okB = true := by decide +kernel

theorem ok73 : fam73.all okB = true := by decide +kernel

theorem ok74 : fam74.all okB = true := by decide +kernel

theorem ok75 : fam75.all okB = true := by decide +kernel

theorem ok76 : fam76.all okB = true := by decide +kernel

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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok40 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok41 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok42 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok43 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok44 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok45 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok46 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok47 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok48 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok49 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok50 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok51 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok52 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok53 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok54 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok55 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok56 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok57 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok58 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok59 e he)

theorem okc3 : ∀ part ∈ chunk3, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk3, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok60 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok61 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok62 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok63 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok64 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok65 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok66 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok67 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok68 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok69 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok70 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok71 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok72 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok73 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok74 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok75 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok76 e he)

set_option maxRecDepth 8000 in
theorem ok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  rw [parts_eq] at hp
  simp only [List.mem_append] at hp
  rcases hp with ((h | h) | h) | h
  · exact okc0 part h
  · exact okc1 part h
  · exact okc2 part h
  · exact okc3 part h

theorem perms_ok : ∀ π ∈ perms, PermOk tab π := by decide +kernel

theorem tab_lt : tab < 2 ^ 64 := by decide +kernel

theorem tab_one : ∃ p : Fin 64, tab.testBit p = true := by decide +kernel

theorem tab_zero : ∃ q : Fin 64, tab.testBit q = false := by decide +kernel

theorem zs_ok : ∀ q ∈ zs, q < 64 ∧ tab.testBit q = false := by decide +kernel

theorem pool_eq : pool0 = base ++ [0, ALL] := by decide +kernel

theorem nec : ∀ a ∈ base, ¬ GoodL tab zs (base.filter (fun x => decide (x ≠ a))) := by
  decide +kernel

theorem base_mem : ∃ e ∈ parts.flatten, e.1 = 0 ∧ e.2.1 = base :=
  ⟨(0, base, [2100096, 5100272, 9300080, 6900256, 8100064, 4100240, 8100048, 4100224, 8100032, 4100208, 8100016, 4100192, 7400288, 2000432, 2600304, 9600496, 2600320, 9600560, 2600336, 9600624, 6600112, 2600352, 9600688, 6200368, 4200512, 8200384, 2200576, 2200400, 2200160, 8200640, 200416, 200704, 600448, 2600592, 600464, 2600656, 600480, 6600128, 2600720, 600528, 2600672, 600544, 6600144, 2600736, 600608, 2600752]), by decide +kernel, rfl, rfl⟩

theorem base_len : base.length = 6 := by decide +kernel

theorem base_nd : base.Nodup := by decide +kernel

theorem tab_eq : ∀ p : Fin 64, (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (fun i : Fin 6 => p.val.testBit i.val) =
    tab.testBit p.val := by
  decide +kernel

def upper : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩,
   ⟨GateOp.or, [2, 6]⟩,
   ⟨GateOp.and, [0, 5]⟩,
   ⟨GateOp.or, [3, 8]⟩,
   ⟨GateOp.or, [1, 4]⟩,
   ⟨GateOp.and, [7, 10]⟩,
   ⟨GateOp.and, [2, 6]⟩,
   ⟨GateOp.and, [9, 11]⟩,
   ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem upper_mono : Monotone2 upper := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_size : upper.size = 9 := rfl

theorem upper_eval : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) =
    Nat.testBit (4276808936 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_16661

theorem PEqualNP.Outside.L_meta_16661 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276153568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro t ⟨C, hC, hs, hev⟩
  have h := PEqualNP.Outside.L_meta_16661.lower PEqualNP.Outside.L_meta_16661.tab 6 4 PEqualNP.Outside.L_meta_16661.parts PEqualNP.Outside.L_meta_16661.perms PEqualNP.Outside.L_meta_16661.zs PEqualNP.Outside.L_meta_16661.base PEqualNP.Outside.L_meta_16661.tab_lt
    PEqualNP.Outside.L_meta_16661.tab_one PEqualNP.Outside.L_meta_16661.tab_zero PEqualNP.Outside.L_meta_16661.zs_ok PEqualNP.Outside.L_meta_16661.perms_ok PEqualNP.Outside.L_meta_16661.ok PEqualNP.Outside.L_meta_16661.pool_eq
    PEqualNP.Outside.L_meta_16661.nec PEqualNP.Outside.L_meta_16661.base_mem PEqualNP.Outside.L_meta_16661.base_len PEqualNP.Outside.L_meta_16661.base_nd
    C hC (fun p => (hev _).trans (PEqualNP.Outside.L_meta_16661.tab_eq p))
  have hs' : C.gates.length ≤ t := hs
  have hu : PEqualNP.Outside.L_meta_16661.upper.size = 9 := PEqualNP.Outside.L_meta_16661.upper_size
  exact ⟨PEqualNP.Outside.L_meta_16661.upper, PEqualNP.Outside.L_meta_16661.upper_mono, by omega, PEqualNP.Outside.L_meta_16661.upper_eval⟩
