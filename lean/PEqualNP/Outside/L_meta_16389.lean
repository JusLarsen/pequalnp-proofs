import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16389
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

def tab : ℕ := 17215830545381517824

def zs : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 17, 18, 20, 21, 24, 26, 28, 32, 34, 36, 38, 40, 42, 44, 48, 50, 52, 56, 60]

def t0 : ℕ := 858993459
def t1 : ℕ := 2863311530
def t2 : ℕ := 3435973836
def t3 : ℕ := 4042322160
def t4 : ℕ := 4278255360
def t5 : ℕ := 4294901760
def t6 : ℕ := 4294967295
def t7 : ℕ := 1095216660735
def t8 : ℕ := 16557098929935
def t9 : ℕ := 56294136361779
def t10 : ℕ := 93823560602965
def t11 : ℕ := 187647121205930
def t12 : ℕ := 225176545447116
def t13 : ℕ := 264913582878960
def t14 : ℕ := 280375465148160
def t15 : ℕ := 281470681743360
def t16 : ℕ := 281470681808895
def t17 : ℕ := 14355442858917939
def t18 : ℕ := 23925738098196565
def t19 : ℕ := 47851476196393130
def t20 : ℕ := 57421771435671756
def t21 : ℕ := 67555025218437360
def t22 : ℕ := 71776119077928960
def t23 : ℕ := 71777214277877760
def t24 : ℕ := 71777214294589695
def t25 : ℕ := 217020518514230019
def t26 : ℕ := 361700864190383365
def t27 : ℕ := 723401728380766730
def t28 : ℕ := 868082074056920076
def t29 : ℕ := 1080880403494997760
def t30 : ℕ := 1085086035472220160
def t31 : ℕ := 1085102592318504960
def t32 : ℕ := 1085102592571150095
def t33 : ℕ := 1152657617789587455
def t34 : ℕ := 1229782938247303441
def t35 : ℕ := 1296775004922253823
def t36 : ℕ := 1519143629599610133
def t37 : ℕ := 2242545357980376863
def t38 : ℕ := 2459565876494606882
def t39 : ℕ := 3472328296227680304
def t40 : ℕ := 3674993371882992384
def t41 : ℕ := 3689292520605548544
def t42 : ℕ := 3689348813882916864
def t43 : ℕ := 3689348814741910323
def t44 : ℕ := 3689573991287357439
def t45 : ℕ := 3746770586177582079
def t46 : ℕ := 3978709506094217015
def t47 : ℕ := 4557430888798830399
def t48 : ℕ := 4629771061636907072
def t49 : ℕ := 4919131752989213764
def t50 : ℕ := 5787213827046133840
def t51 : ℕ := 6124988953138320640
def t52 : ℕ := 6148820867675914240
def t53 : ℕ := 6148914689804861440
def t54 : ℕ := 6148914691236517205
def t55 : ℕ := 6148914694099828735
def t56 : ℕ := 6149102338357723135
def t57 : ℕ := 6196766167432910335
def t58 : ℕ := 6872316419617283935
def t59 : ℕ := 8608480567731124087
def t60 : ℕ := 9259542123273814144
def t61 : ℕ := 9799982325021313024
def t62 : ℕ := 9838113388281462784
def t63 : ℕ := 9838263503687778304
def t64 : ℕ := 9838263505978427528
def t65 : ℕ := 11529390970613309440
def t66 : ℕ := 11574251045037015040
def t67 : ℕ := 11574427651397386240
def t68 : ℕ := 11574427654092267680
def t69 : ℕ := 12153149036796881064
def t70 : ℕ := 12249790989299875840
def t71 : ℕ := 12249977903424471040
def t72 : ℕ := 12249977906276641280
def t73 : ℕ := 12288259087233755784
def t74 : ℕ := 12295014589755599520
def t75 : ℕ := 12297641732488560640
def t76 : ℕ := 12297641735351828480
def t77 : ℕ := 12297791853048793224
def t78 : ℕ := 12297818344407081120
def t79 : ℕ := 12297828652328593920
def t80 : ℕ := 12297829379609722880
def t81 : ℕ := 12297829381900372104
def t82 : ℕ := 12297829382304604320
def t83 : ℕ := 12297829382461893120
def t84 : ℕ := 12297829382472990720
def t85 : ℕ := 12297829382473034410
def t86 : ℕ := 12297829383904690175
def t87 : ℕ := 12297923206033637375
def t88 : ℕ := 12321755120571230975
def t89 : ℕ := 12659530246663417775
def t90 : ℕ := 13527612320720337851
def t91 : ℕ := 13816973012072644543
def t92 : ℕ := 13835269164735971328
def t93 : ℕ := 13889101254044418048
def t94 : ℕ := 13889312360277000192
def t95 : ℕ := 13889313181676863488
def t96 : ℕ := 13889313184910721216
def t97 : ℕ := 13902824189954408688
def t98 : ℕ := 14465782733441386688
def t99 : ℕ := 14468025737162571968
def t100 : ℕ := 14468034567480590528
def t101 : ℕ := 14468034567615334600
def t102 : ℕ := 14699749187159851008
def t103 : ℕ := 14699973484109365248
def t104 : ℕ := 14699973487531969536
def t105 : ℕ := 14738254668489084040
def t106 : ℕ := 14754017507706719424
def t107 : ℕ := 14757170078986272768
def t108 : ℕ := 14757170082422194176
def t109 : ℕ := 14757319616003606528
def t110 : ℕ := 14757320200119123968
def t111 : ℕ := 14757320200119158920
def t112 : ℕ := 14757381188654776320
def t113 : ℕ := 14757382013288497344
def t114 : ℕ := 14757394382794312704
def t115 : ℕ := 14757395255531667456
def t116 : ℕ := 14757395257822316680
def t117 : ℕ := 14757395258765525184
def t118 : ℕ := 14757395258954271744
def t119 : ℕ := 14757395258967588864
def t120 : ℕ := 14757395258967641292
def t121 : ℕ := 14757395259826634751
def t122 : ℕ := 14757451553104003071
def t123 : ℕ := 14771750701826559231
def t124 : ℕ := 14974415777481871311
def t125 : ℕ := 15987178197214944733
def t126 : ℕ := 16195191379033383104
def t127 : ℕ := 16204163393918124224
def t128 : ℕ := 16204198715190198464
def t129 : ℕ := 16204198715729174752
def t130 : ℕ := 16909585770718358186
def t131 : ℕ := 16915778314696714944
def t132 : ℕ := 16927529800487840426
def t133 : ℕ := 16927554084232937664
def t134 : ℕ := 16927600169232034474
def t135 : ℕ := 16927600443402535104
def t136 : ℕ := 16927600444109941482
def t137 : ℕ := 17072280789786094828
def t138 : ℕ := 17149969068787297792
def t139 : ℕ := 17197820544983690922
def t140 : ℕ := 17207128280282169344
def t141 : ℕ := 17207315197258934784
def t142 : ℕ := 17207390840222969548
def t143 : ℕ := 17216698428919906304
def t144 : ℕ := 17216698429492559872
def t145 : ℕ := 17216886072605147136
def t146 : ℕ := 17216886076041068544
def t147 : ℕ := 17216886076613765802
def t148 : ℕ := 17216923606038006988
def t149 : ℕ := 17216961131453612032
def t150 : ℕ := 17216961134316923562
def t151 : ℕ := 17216961134889585868
def t152 : ℕ := 17216961135462248174
def t153 : ℕ := 17293822573129236480
def t154 : ℕ := 17294086451893370880
def t155 : ℕ := 17294086455919964160
def t156 : ℕ := 17339123139398922400
def t157 : ℕ := 17348129651460993024
def t158 : ℕ := 17348130476094714048
def t159 : ℕ := 17361376563513262080
def t160 : ℕ := 17361376567555522560
def t161 : ℕ := 17361553176610775200
def t162 : ℕ := 17361588498421825728
def t163 : ℕ := 17361640450346250240
def t164 : ℕ := 17361641477096079360
def t165 : ℕ := 17361641479790960800
def t166 : ℕ := 17361641480329937088
def t167 : ℕ := 17361641481122672640
def t168 : ℕ := 17361641481138339840
def t169 : ℕ := 17361641481138401520
def t170 : ℕ := 17361641481391046655
def t171 : ℕ := 17361658038237331455
def t172 : ℕ := 17365863670214553855
def t173 : ℕ := 17578661999652631539
def t174 : ℕ := 17723342345328784885
def t175 : ℕ := 17940354033390252272
def t176 : ℕ := 17940362863843014904
def t177 : ℕ := 18014673391583296000
def t178 : ℕ := 18062524867779689130
def t179 : ℕ := 18082228416801733360
def t180 : ℕ := 18084767257870336000
def t181 : ℕ := 18084954904991541930
def t182 : ℕ := 18085032171453214960
def t183 : ℕ := 18085043205308416000
def t184 : ℕ := 18085043208171727530
def t185 : ℕ := 18085043209350738160
def t186 : ℕ := 18085043209519168250
def t187 : ℕ := 18158790778715962368
def t188 : ℕ := 18216198479838769152
def t189 : ℕ := 18216212550151634124
def t190 : ℕ := 18226345803934399728
def t191 : ℕ := 18229445395933298688
def t192 : ℕ := 18229670572478745804
def t193 : ℕ := 18229710309516177648
def t194 : ℕ := 18229723550950883328
def t195 : ℕ := 18229723554386857164
def t196 : ℕ := 18229723554993205488
def t197 : ℕ := 18229723555195321596
def t198 : ℕ := 18374403900871474942
def t199 : ℕ := 18374686479671623680
def t200 : ℕ := 18374686483949813760
def t201 : ℕ := 18374873400926579200
def t202 : ℕ := 18374910784321932288
def t203 : ℕ := 18374950366740541440
def t204 : ℕ := 18374966855136706560
def t205 : ℕ := 18374966857988876800
def t206 : ℕ := 18374966858559310848
def t207 : ℕ := 18374966859163299840
def t208 : ℕ := 18374966859414896640
def t209 : ℕ := 18374966859414961920
def t210 : ℕ := 18374966859431673855
def t211 : ℕ := 18374967954631622655
def t212 : ℕ := 18379189048491114255
def t213 : ℕ := 18389322302273879859
def t214 : ℕ := 18398892597513158485
def t215 : ℕ := 18413247456256524032
def t216 : ℕ := 18413248040372076424
def t217 : ℕ := 18420003542893920160
def t218 : ℕ := 18422537230001766400
def t219 : ℕ := 18422724877122972330
def t220 : ℕ := 18422817605466914560
def t221 : ℕ := 18422818331321958400
def t222 : ℕ := 18422818334185269930
def t223 : ℕ := 18422818335600213760
def t224 : ℕ := 18422818335611355050
def t225 : ℕ := 18429010054955990784
def t226 : ℕ := 18429010879589711808
def t227 : ℕ := 18432107379212156928
def t228 : ℕ := 18432332555757604044
def t229 : ℕ := 18432387754677305088
def t230 : ℕ := 18432388626559008768
def t231 : ℕ := 18432388629994982604
def t232 : ℕ := 18432388630837264128
def t233 : ℕ := 18432388630850633676
def t234 : ℕ := 18441958926089912302
def t235 : ℕ := 18442240478376099840
def t236 : ℕ := 18442505391958978800
def t237 : ℕ := 18442520853841248000
def t238 : ℕ := 18442521880339415040
def t239 : ℕ := 18442521884381737200
def t240 : ℕ := 18442521884617670400
def t241 : ℕ := 18442521884633399280
def t242 : ℕ := 18445336677350834170
def t243 : ℕ := 18445899635894321148
def t244 : ℕ := 18446462598732840960
def t245 : ℕ := 18446462601596108800
def t246 : ℕ := 18446462602168762368
def t247 : ℕ := 18446462602775101440
def t248 : ℕ := 18446462603011031040
def t249 : ℕ := 18446462603027742720
def t250 : ℕ := 18446462603027808255
def t251 : ℕ := 18446463698244403455
def t252 : ℕ := 18446479160126672655
def t253 : ℕ := 18446518897164104499
def t254 : ℕ := 18446556426588345685
def t255 : ℕ := 18446612720724707464
def t256 : ℕ := 18446639212082995360
def t257 : ℕ := 18446649520004508160
def t258 : ℕ := 18446650245854003200
def t259 : ℕ := 18446650248717314730
def t260 : ℕ := 18446650250148904960
def t261 : ℕ := 18446650250148948650
def t262 : ℕ := 18446673709260324864
def t263 : ℕ := 18446674533894045888
def t264 : ℕ := 18446686903399861248
def t265 : ℕ := 18446687775278235648
def t266 : ℕ := 18446687778714209484
def t267 : ℕ := 18446687779573137408
def t268 : ℕ := 18446687779573189836
def t269 : ℕ := 18446725308997431022
def t270 : ℕ := 18446726485818470400
def t271 : ℕ := 18446727512315658240
def t272 : ℕ := 18446727516357980400
def t273 : ℕ := 18446727516610560000
def t274 : ℕ := 18446727516610621680
def t275 : ℕ := 18446737480934750720
def t276 : ℕ := 18446738554676574970
def t277 : ℕ := 18446740762289765628
def t278 : ℕ := 18446742974197923840
def t279 : ℕ := 18446742978476179200
def t280 : ℕ := 18446742978492825600
def t281 : ℕ := 18446742978492890880
def t282 : ℕ := 18446743708637331370
def t283 : ℕ := 18446743854666219468
def t284 : ℕ := 18446744009285042160
def t285 : ℕ := 18446744069414584320
def t286 : ℕ := 18446744069414649855
def t287 : ℕ := 18446744069431296255
def t288 : ℕ := 18446744069667229455
def t289 : ℕ := 18446744070273577779
def t290 : ℕ := 18446744070846240085
def t291 : ℕ := 18446744071705198592
def t292 : ℕ := 18446744071705233544
def t293 : ℕ := 18446744072109465760
def t294 : ℕ := 18446744072266754560
def t295 : ℕ := 18446744072277852160
def t296 : ℕ := 18446744072277895850
def t297 : ℕ := 18446744072635858944
def t298 : ℕ := 18446744072648392704
def t299 : ℕ := 18446744072648442048
def t300 : ℕ := 18446744072837188608
def t301 : ℕ := 18446744072850505728
def t302 : ℕ := 18446744072850558156
def t303 : ℕ := 18446744073423220462
def t304 : ℕ := 18446744073441177600
def t305 : ℕ := 18446744073456844800
def t306 : ℕ := 18446744073456906480
def t307 : ℕ := 18446744073625336570
def t308 : ℕ := 18446744073659022588
def t309 : ℕ := 18446744073692774400
def t310 : ℕ := 18446744073692839680
def t311 : ℕ := 18446744073703980970
def t312 : ℕ := 18446744073706209228
def t313 : ℕ := 18446744073708568560
def t314 : ℕ := 18446744073709486080
def t315 : ℕ := 18446744073709529770
def t316 : ℕ := 18446744073709538508
def t317 : ℕ := 18446744073709547760
def t318 : ℕ := 18446744073709551360

def base : List ℕ := [t85, t120, t169, t209, t249, t285]

def perms : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]]

def fam0 : List (ℕ × List ℕ × List ℕ) := [
  (0, [t85, t120, t169, t209, t249, t285], [2100096, 5100256, 9300080, 6900240, 8100064, 4100224, 8100048, 4100208, 8100032, 4100192, 8100016, 4100176, 7400272, 2000416, 2600288, 3600144, 9600480, 2600304, 9600544, 2600320, 9600608, 2600336, 9600672, 200112, 6200352, 4200496, 8200368, 2200560, 6200128, 2200384, 8200624, 200400, 200688, 600432, 2600576, 600448, 2600640, 600464, 2600704, 600512, 2600656, 600528, 2600720, 600592, 2600736]),
  (2, [t24, t85, t120, t186, t249, t285], [9600144, 1100412, 7700428]),
  (3, [t0, t85, t120, t169, t209, t249, t285], []),
  (3, [t16, t68, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t186, t249, t285], []),
  (3, [t32, t85, t120, t209, t249, t285, t310], []),
  (3, [t51, t85, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t96, t120, t209, t249, t285], [3000191, 600078, 3401037, 3400957, 1400045]),
  (3, [t85, t96, t120, t209, t249, t263, t285], [3800589, 200781]),
  (3, [t85, t120, t124, t169, t209, t249, t285], [1900782, 200112]),
  (3, [t85, t120, t169, t196, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t271, t285], []),
  (3, [t6, t24, t85, t96, t120, t249], []),
  (3, [t64, t85, t96, t108, t209, t285], [7800993]),
  (3, [t85, t96, t120, t209, t270, t285], []),
  (3, [t85, t112, t155, t169, t209, t285], [])]

def fam1 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t6, t85, t120, t169, t209, t249], [600000, 9100176, 4600816, 7600194, 1800800, 9400178, 600784, 600768, 600752, 100018, 4600290, 700050, 2200402, 3100082, 2600482, 3100114, 2600562, 3100146, 2600642, 9900210, 4500418, 5100226, 6100864, 2100498, 5100242, 2100578, 5100258, 2100658, 2700832, 8700306, 6700514, 700338, 4700594, 8700848, 4700354, 700674, 3100434, 5100610, 3100450, 5100690, 3100530, 5100706]),
  (2, [t26, t85, t120, t209, t249, t285], [3600144, 6100305]),
  (3, [t1, t6, t85, t120, t169, t209, t249], []),
  (3, [t16, t72, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t197, t249, t285], []),
  (3, [t32, t85, t120, t209, t249, t285, t314], []),
  (3, [t52, t54, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t104, t120, t169, t249, t285], [7800497, 9400286, 7400061]),
  (3, [t85, t96, t120, t209, t249, t268, t285], [8200605]),
  (3, [t85, t120, t125, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t198, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t272, t285], []),
  (3, [t6, t24, t85, t108, t120, t169], []),
  (3, [t68, t85, t96, t108, t209, t285], [3001009]),
  (3, [t85, t96, t120, t223, t249, t285], [5800975, 9400831]),
  (3, [t85, t112, t169, t209, t270, t285], [])]

def fam2 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t16, t85, t120, t169, t209, t285], [600000, 9100192, 4600944, 7601042, 1800928, 9401026, 600912, 600896, 600752, 100866, 4600067, 200880, 8700898, 4200163, 3100930, 2600243, 3100962, 2600323, 3100994, 2600467, 9901058, 4500179, 5100003, 6100976, 2100259, 5100019, 2100339, 5100051, 2100483, 2700960, 8700083, 6700275, 700115, 4700355, 2700147, 2700499, 3100195, 5100371, 3100227, 5100515, 3100307, 5100531]),
  (2, [t28, t85, t120, t209, t249, t285], [2500801]),
  (3, [t1, t85, t120, t169, t209, t249, t285], []),
  (3, [t16, t76, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t200, t249, t285], []),
  (3, [t33, t85, t120, t169, t209, t249, t285], []),
  (3, [t52, t85, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t108, t120, t169, t209, t285], [7000303, 8600958, 1400718, 1400574, 3400045, 5400061]),
  (3, [t85, t96, t120, t209, t249, t274, t285], [1400621, 200781]),
  (3, [t85, t120, t129, t152, t209, t249, t285], [400798, 7400143, 5400159, 1400175]),
  (3, [t85, t120, t169, t199, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t273, t285], []),
  (3, [t6, t44, t85, t120, t169, t209], []),
  (3, [t72, t85, t96, t108, t209, t285], []),
  (3, [t85, t96, t120, t225, t249, t285], []),
  (3, [t85, t113, t169, t209, t281, t285], [3001057])]

def fam3 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t24, t85, t120, t169, t249, t285], [600000, 9100208, 4601024, 7600771, 1801008, 9400755, 600992, 600896, 600768, 100595, 4600867, 2700627, 200979, 3100659, 2601059, 3100691, 2600132, 3100723, 2600212, 9900787, 4500995, 5100803, 6100001, 2100004, 5100835, 2100148, 5100851, 2100228, 2701040, 8700883, 6700020, 8701056, 4700947, 700164, 2700963, 2700244, 3101027, 5100180, 3101043, 5100260, 3100116, 5100292]),
  (2, [t32, t43, t85, t209, t249, t285], [9900080, 8700064]),
  (3, [t2, t6, t85, t120, t169, t209, t249], []),
  (3, [t16, t80, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t204, t249, t285], []),
  (3, [t34, t85, t120, t169, t209, t249, t285], []),
  (3, [t53, t54, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t120, t169, t209, t249, t294], []),
  (3, [t85, t96, t120, t209, t249, t281, t285], [7800205, 1400637, 6200797]),
  (3, [t85, t120, t129, t169, t209, t249, t285], [4200814]),
  (3, [t85, t120, t169, t200, t209, t281, t285], []),
  (3, [t85, t120, t169, t209, t249, t276, t285], []),
  (3, [t6, t47, t85, t120, t209, t249], []),
  (3, [t72, t85, t104, t108, t169, t285], [7001041]),
  (3, [t85, t96, t122, t209, t249, t285], [7400160]),
  (3, [t85, t114, t169, t209, t261, t285], [])]

def fam4 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t32, t85, t120, t209, t249, t285], [600000, 9100224, 4600065, 7600516, 1800049, 9400500, 600992, 600912, 600784, 100340, 6100305, 4600612, 6200033, 4700372, 8200708, 3100404, 2600852, 3100436, 2600932, 3100468, 2601012, 9900532, 4500724, 5100564, 2100868, 5100580, 2100948, 5100596, 2101028, 700644, 4700884, 8700081, 4700676, 700964, 2700692, 2701044, 3100820, 5100996, 3100836, 5100005, 3100916, 5100021]),
  (2, [t32, t54, t120, t209, t249, t285], [9100096, 5100064]),
  (3, [t2, t85, t120, t169, t209, t249, t285], []),
  (3, [t16, t85, t87, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t224, t249, t285], []),
  (3, [t38, t43, t85, t169, t209, t249, t285], []),
  (3, [t53, t85, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t120, t169, t209, t257, t285], []),
  (3, [t85, t96, t120, t209, t249, t285, t296], [2400653]),
  (3, [t85, t120, t136, t169, t209, t249, t285], [3200846, 3800465, 3600144]),
  (3, [t85, t120, t169, t201, t209, t249, t285], [4600737, 600415]),
  (3, [t85, t120, t169, t209, t249, t277, t285], []),
  (3, [t6, t54, t96, t120, t209, t249], []),
  (3, [t76, t85, t96, t108, t209, t285], []),
  (3, [t85, t96, t142, t209, t249, t285], []),
  (3, [t85, t114, t169, t209, t274, t285], [3001057])]

def fam5 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t43, t85, t169, t209, t249, t285], [6200000, 3100240, 1400097, 4400229, 7400049, 7401008, 7400928, 7400800, 2100069, 9000341, 4300101, 1800161, 7800565, 2300133, 9800645, 8300165, 7800145, 3800725, 300197, 1800805, 1900277, 2900177, 8900581, 1900293, 8900661, 1900309, 8900741, 1900325, 8900821, 9900517, 1900693, 9900533, 1900773, 9900549, 1900853, 9900613, 1900789, 9900629, 1900869, 9900709, 1900885]),
  (2, [t32, t85, t108, t120, t209, t285], [7400128, 8600524, 3700540]),
  (3, [t3, t6, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t96, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t233, t249, t285], []),
  (3, [t38, t85, t120, t169, t209, t249, t285], []),
  (3, [t54, t64, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t120, t169, t224, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t285, t299], [1800669]),
  (3, [t85, t120, t137, t169, t209, t249, t285], [7000878, 3800465]),
  (3, [t85, t120, t169, t202, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t278, t285], []),
  (3, [t6, t54, t108, t120, t169, t209], []),
  (3, [t80, t85, t96, t108, t209, t285], [4200847, 2600831, 7000735]),
  (3, [t85, t96, t151, t209, t249, t285], []),
  (3, [t85, t120, t126, t209, t249, t285], [])]

def fam6 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t54, t120, t169, t209, t249, t285], [2600000, 4100256, 7800097, 5400245, 6600065, 6601024, 6600944, 6600816, 9500981, 6400278, 1100225, 7101029, 1600358, 7101061, 1600438, 7100022, 1600518, 7100054, 1600598, 8700257, 4700214, 2700390, 6700230, 700470, 4700273, 700246, 6700550, 8700262, 8700630, 9100310, 1100486, 9100326, 1100566, 9100342, 1100646, 9100406, 1100582, 9100422, 1100662, 9100502, 1100678]),
  (2, [t43, t54, t169, t209, t249, t285], [4700096, 1900080]),
  (3, [t3, t85, t120, t169, t209, t249, t285], []),
  (3, [t16, t85, t96, t120, t209, t249, t285], [2900062]),
  (3, [t24, t85, t120, t169, t241, t249, t285], []),
  (3, [t39, t43, t85, t169, t209, t249, t285], []),
  (3, [t54, t68, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t120, t179, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t285, t302], [4200701, 4200925]),
  (3, [t85, t120, t138, t152, t169, t249, t285], [2400894, 5400143, 7400239, 3400255]),
  (3, [t85, t120, t169, t203, t209, t249, t285], [8600769]),
  (3, [t85, t120, t169, t209, t249, t279, t285], []),
  (3, [t6, t85, t96, t108, t120, t209], []),
  (3, [t80, t120, t136, t209, t249, t285], [200975, 8200735]),
  (3, [t85, t97, t120, t209, t249, t285], []),
  (3, [t85, t120, t127, t209, t249, t285], [])]

def fam7 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t85, t96, t120, t209, t249, t285], [900257, 3900166, 8500209, 3300949, 8100113, 5700357, 6901040, 2900899, 6900960, 2900099, 6900832, 2900322, 7800774, 6800481, 1600839, 6200870, 800855, 1400007, 8400983, 1400199, 8401063, 1400311, 8400072, 6200647, 4200999, 8200679, 2200008, 2200727, 8200088, 7000759, 1001015, 7400160, 3400353, 5000321, 1000791, 7000024, 9000823, 9000104, 9400951, 1400056, 9400967, 1400136, 9401047, 1400152]),
  (2, [t43, t85, t96, t209, t249, t285], [5000112, 6200268, 1800161]),
  (3, [t4, t6, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t104, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t244, t249, t285], []),
  (3, [t39, t85, t120, t169, t209, t249, t285], []),
  (3, [t54, t72, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t120, t186, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t285, t306], [1400717]),
  (3, [t85, t120, t138, t169, t209, t249, t285], [1800881, 6200910]),
  (3, [t85, t120, t169, t205, t209, t249, t285], [4600689]),
  (3, [t85, t120, t169, t209, t249, t280, t285], []),
  (3, [t6, t85, t96, t108, t169, t209], []),
  (3, [t85, t91, t120, t209, t249, t285], []),
  (3, [t85, t98, t120, t209, t249, t285], []),
  (3, [t85, t120, t128, t209, t249, t285], [])]

def fam8 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t85, t108, t120, t169, t209, t285], [8900273, 1900182, 2500193, 5300901, 6100129, 3700405, 4900081, 900660, 4901056, 900931, 4900848, 900370, 9800822, 1600424, 4200886, 1200417, 8800440, 9400998, 400401, 6400504, 9400039, 6400584, 9400327, 6400728, 6200695, 6200520, 2200216, 200600, 8200376, 4200744, 9400160, 5400337, 7000321, 3000775, 1000536, 7400385, 5000264, 9000616, 7000408, 7000760, 7400456, 9400632, 7400488, 9400776, 7400568, 9400792]),
  (2, [t43, t85, t108, t169, t209, t285], [3000128, 4200524, 7800145]),
  (3, [t4, t85, t120, t169, t209, t249, t285], []),
  (3, [t16, t85, t108, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t251, t285], []),
  (3, [t40, t43, t85, t169, t209, t249, t285], []),
  (3, [t54, t76, t120, t169, t209, t249, t285], []),
  (3, [t72, t85, t142, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t285, t310], [1400733]),
  (3, [t85, t120, t139, t169, t209, t249, t285], [7200719, 5200942, 7800497]),
  (3, [t85, t120, t169, t206, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t282, t285], []),
  (3, [t6, t85, t96, t108, t209, t249], []),
  (3, [t85, t92, t96, t108, t209, t285], []),
  (3, [t85, t99, t120, t209, t249, t285], []),
  (3, [t85, t120, t129, t138, t249, t285], [])]

def fam9 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t85, t120, t186, t209, t249, t285], [1100289, 4100198, 8300177, 5900485, 5100017, 100324, 7100001, 7100976, 7100864, 6400918, 1000297, 1600119, 8600795, 1600247, 8600875, 1600471, 8600955, 8600369, 3600200, 7800747, 7200312, 1200811, 5200401, 1200824, 7200891, 9200952, 9200971, 3600683, 600843, 3600699, 600923, 3600715, 601003, 9600763, 1600939, 9600779, 1601019, 9600859, 1601035]),
  (2, [t43, t85, t169, t209, t253, t285], [9900721]),
  (3, [t5, t6, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t115, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t261, t285], []),
  (3, [t40, t85, t120, t169, t209, t249, t285], []),
  (3, [t54, t80, t120, t169, t209, t249, t285], []),
  (3, [t73, t85, t120, t169, t209, t249, t285], [1800881]),
  (3, [t85, t96, t120, t209, t249, t285, t314], [1400749, 2200813]),
  (3, [t85, t120, t142, t169, t209, t249, t285], [7000078, 3000958, 9000095, 7800497, 3000287]),
  (3, [t85, t120, t169, t207, t209, t249, t285], [8600705]),
  (3, [t85, t120, t169, t209, t249, t283, t285], []),
  (3, [t6, t85, t101, t120, t209, t249], []),
  (3, [t85, t92, t108, t169, t209, t285], [3001057]),
  (3, [t85, t100, t120, t209, t249, t285], []),
  (3, [t85, t120, t129, t144, t209, t285], [8201009])]

def fam10 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t85, t96, t108, t209, t285], [100977, 3100876, 7700961, 3700945, 6100929, 6100913, 7001052, 6001025, 800317, 1001068, 2800333, 600045, 7600477, 600093, 7600653, 7400173, 7000285, 5400141, 3400493, 1400221, 7400669, 3400237, 1400509, 9400269, 5400685, 8600461, 600733]),
  (2, [t43, t85, t173, t209, t249, t285], [1900801]),
  (3, [t5, t85, t120, t169, t209, t249, t285], []),
  (3, [t16, t85, t120, t122, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t268, t285], []),
  (3, [t41, t43, t85, t169, t209, t249, t285], []),
  (3, [t54, t85, t96, t120, t209, t249, t285], [5800796, 5301004, 8900876]),
  (3, [t74, t85, t120, t169, t209, t249, t285], [4600833]),
  (3, [t85, t96, t169, t197, t209, t249, t285], []),
  (3, [t85, t120, t144, t152, t169, t209, t285], [800417, 9400159, 3400239]),
  (3, [t85, t120, t169, t208, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t284, t285], []),
  (3, [t6, t85, t108, t120, t186, t209], []),
  (3, [t85, t93, t96, t108, t209, t285], []),
  (3, [t85, t101, t108, t120, t209, t285], []),
  (3, [t85, t120, t129, t149, t209, t249], [])]

def fam11 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t85, t120, t169, t209, t249, t285], [7600034, 2100567, 8200066, 9701032, 600098, 100697, 600130, 100186, 600162, 100778, 5100274, 2100722, 8700322, 4700370, 2700386, 2700738, 3100466, 5100754, 3100546, 5100770, 3100626, 5100786]),
  (2, [t43, t85, t186, t209, t249, t285], [5200144]),
  (3, [t6, t43, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t152, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t274, t285], []),
  (3, [t41, t85, t120, t169, t209, t249, t285], []),
  (3, [t54, t85, t108, t120, t169, t209, t285], [200828, 9400860, 9700972, 8900956, 900876]),
  (3, [t75, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t101, t120, t169, t209, t249, t285], [200112, 9000817, 8600190]),
  (3, [t85, t120, t144, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t210, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t286], []),
  (3, [t6, t85, t108, t152, t169, t209], []),
  (3, [t85, t94, t114, t209, t249, t285], [6600911, 200751]),
  (3, [t85, t101, t108, t169, t209, t285], [9400160]),
  (3, [t85, t120, t131, t209, t249, t285], [])]

def fam12 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t85, t120, t169, t209, t249, t285], [7600882, 2100583, 6200914, 1701048, 600946, 100713, 600978, 100202, 601010, 100187, 5100035, 2100403, 8700099, 4700131, 700419, 3100211, 5100435, 3100291, 5100451, 3100387, 5100547]),
  (2, [t44, t85, t120, t169, t209, t285], [6200128, 7800636, 3800284, 3800044, 200880, 100700, 9300684, 8300945, 4300668, 5900652]),
  (3, [t6, t54, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t155, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t281, t285], []),
  (3, [t42, t43, t85, t169, t209, t249, t285], []),
  (3, [t54, t85, t120, t186, t209, t249, t285], [2600241]),
  (3, [t76, t85, t96, t120, t209, t249, t285], [5000207, 1400077]),
  (3, [t85, t101, t120, t186, t209, t249, t285], [7600206]),
  (3, [t85, t120, t147, t169, t209, t249, t285], [5800513]),
  (3, [t85, t120, t169, t209, t211, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t287], []),
  (3, [t6, t85, t120, t129, t209, t249], []),
  (3, [t85, t94, t120, t209, t249, t285], [3000927, 200751]),
  (3, [t85, t101, t108, t186, t209, t285], []),
  (3, [t85, t120, t133, t209, t249, t285], [])]

def fam13 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t24, t85, t120, t169, t209, t249, t285], [7600611, 2100599, 200643, 7701064, 600675, 100729, 600707, 100794, 600739, 100203, 5100819, 2100068, 8700899, 700915, 4700084, 4700931, 3101011, 5100100, 3100036, 5100196, 3100052, 5100276]),
  (2, [t47, t85, t120, t209, t249, t285], [200112, 5800732, 1800300, 1800060, 2900125, 6200033, 2300961, 8300764, 9900748]),
  (3, [t6, t64, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t160, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t285, t287], []),
  (3, [t42, t85, t120, t169, t209, t249, t285], []),
  (3, [t54, t96, t120, t169, t209, t249, t285], [1900908]),
  (3, [t76, t85, t108, t120, t169, t209, t285], [5800513, 2600974, 1400734, 3400077]),
  (3, [t85, t102, t108, t120, t169, t209, t285], [3800254, 1800237]),
  (3, [t85, t120, t148, t169, t209, t249, t285], [5000974, 1000111, 5800513]),
  (3, [t85, t120, t169, t209, t212, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t288], []),
  (3, [t6, t85, t120, t136, t209, t249], []),
  (3, [t85, t95, t96, t108, t209, t285], []),
  (3, [t85, t101, t108, t209, t249, t285], []),
  (3, [t85, t120, t135, t209, t249, t285], [])]

def fam14 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t32, t85, t120, t169, t209, t249, t285], [7600356, 2100615, 2200388, 5700009, 600420, 100218, 600452, 100810, 600484, 100219, 5100548, 2100788, 8700628, 6700804, 4700660, 3100740, 5100900, 3100756, 5100980, 3100772, 5101060]),
  (2, [t50, t54, t120, t209, t249, t285], [8600241, 4300780, 700844]),
  (3, [t6, t68, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t164, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t285, t296], []),
  (3, [t43, t54, t85, t169, t209, t249, t285], []),
  (3, [t54, t104, t120, t169, t209, t249, t285], []),
  (3, [t76, t85, t120, t182, t209, t249, t285], []),
  (3, [t85, t102, t120, t169, t209, t249, t285], []),
  (3, [t85, t120, t149, t152, t169, t209, t249], [4400990, 7400175, 1400255]),
  (3, [t85, t120, t169, t209, t213, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t289], []),
  (3, [t6, t85, t120, t138, t169, t249], []),
  (3, [t85, t96, t102, t108, t209, t285], []),
  (3, [t85, t101, t152, t209, t249, t285], []),
  (3, [t85, t120, t138, t144, t169, t285], [201041])]

def fam15 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t43, t85, t120, t169, t209, t249, t285], [9000245, 5000500, 5000755, 5001026, 5000178, 2800085, 9700631, 5000117, 2500801, 8500745, 9400469, 3000149, 500234, 9000181, 8500721, 4500826, 5400453, 1000213, 2500235, 6700261, 1300501, 500485, 9500113, 5500373, 7100357, 3500597, 7500389, 1500677, 5500129, 1500421, 3100405, 7500757, 9500437, 9500837]),
  (2, [t50, t85, t120, t209, t249, t285], [6100305, 8100225, 3600144, 5800796, 2200860]),
  (3, [t6, t72, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t171, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t285, t302], []),
  (3, [t43, t54, t120, t169, t209, t249, t285], []),
  (3, [t54, t108, t120, t169, t209, t249, t285], [3900924]),
  (3, [t76, t85, t120, t186, t209, t249, t285], []),
  (3, [t85, t103, t120, t169, t209, t249, t285], []),
  (3, [t85, t120, t149, t169, t209, t249, t285], [3800897]),
  (3, [t85, t120, t169, t209, t214, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t290], []),
  (3, [t6, t85, t120, t169, t209, t270], []),
  (3, [t85, t96, t104, t108, t209, t285], []),
  (3, [t85, t102, t120, t169, t229, t285], []),
  (3, [t85, t120, t138, t149, t169, t249], [])]

def fam16 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t54, t85, t120, t169, t209, t249, t285], [800229, 9600516, 9600771, 9601042, 9600194, 1000997, 7900025, 2600241, 8601045, 4101013, 3100761, 8600006, 3100250, 8600038, 3100842, 8600070, 3100251, 5900086, 500294, 1100102, 2100289, 8100374, 5100198, 1100118, 8100454, 1100134, 8100534, 1100150, 8100614, 1700166, 7700182]),
  (2, [t54, t96, t120, t209, t249, t285], [1400112, 7000732, 5400316, 5400076, 4300780, 5900977, 1900924, 3500892]),
  (3, [t6, t76, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t186, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t285, t306], []),
  (3, [t43, t64, t85, t169, t209, t249, t285], []),
  (3, [t54, t115, t120, t169, t209, t249, t285], []),
  (3, [t77, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t104, t108, t120, t169, t209, t285], [200253]),
  (3, [t85, t120, t150, t169, t209, t249, t285], [1800529]),
  (3, [t85, t120, t169, t209, t216, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t292], []),
  (3, [t16, t43, t85, t96, t209, t285], [3700945]),
  (3, [t85, t96, t107, t108, t209, t285], []),
  (3, [t85, t104, t108, t186, t209, t285], []),
  (3, [t85, t120, t138, t186, t249, t285], [])]

def fam17 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t64, t85, t120, t169, t209, t249, t285], [3300758, 500086, 7700261, 6500532, 6500787, 6501058, 6500210, 9000790, 9000817, 5000777, 7400902, 7000806, 7000266, 3000838, 1000858, 5000854, 9000267, 2000918, 8600870, 4600886]),
  (2, [t54, t108, t120, t169, t209, t285], [9400128, 1000636, 3400332, 3400092, 8700812, 7900844, 7900977, 3900908, 5500892]),
  (3, [t6, t80, t85, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t197, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t285, t310], []),
  (3, [t43, t68, t85, t169, t209, t249, t285], []),
  (3, [t54, t120, t125, t169, t209, t249, t285], []),
  (3, [t78, t85, t120, t169, t209, t249, t285], [4600849]),
  (3, [t85, t104, t108, t169, t209, t249, t285], [7400449]),
  (3, [t85, t120, t151, t169, t209, t249, t285], [3000094, 9001006, 5000127, 9000319, 1800529]),
  (3, [t85, t120, t169, t209, t217, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t293], []),
  (3, [t24, t44, t85, t120, t169, t285], []),
  (3, [t85, t96, t108, t113, t209, t285], []),
  (3, [t85, t104, t120, t169, t249, t294], []),
  (3, [t85, t120, t140, t169, t209, t285], [])]

def fam18 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t68, t85, t120, t169, t209, t249, t285], [8100742, 6100102, 3300277, 2100548, 2100803, 2100003, 2100226, 9000790, 7400089, 8600934, 600282, 8600950, 600874, 8600966, 600283, 7601014, 4200982, 200998]),
  (2, [t54, t120, t186, t209, t249, t285], [1600144, 1100225, 7100940, 3700956]),
  (3, [t6, t85, t86, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t200, t209, t285], []),
  (3, [t24, t85, t120, t169, t249, t285, t314], []),
  (3, [t43, t72, t85, t169, t209, t249, t285], []),
  (3, [t54, t120, t152, t169, t209, t249, t285], [9300972, 2300988, 6301020]),
  (3, [t79, t85, t120, t169, t209, t249, t285], [4600737]),
  (3, [t85, t104, t120, t169, t249, t285, t310], []),
  (3, [t85, t120, t152, t186, t209, t249, t285], [3200238, 9801022, 6800481, 6800271, 4800335, 800367]),
  (3, [t85, t120, t169, t209, t218, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t294], []),
  (3, [t24, t47, t85, t120, t249, t285], []),
  (3, [t85, t96, t108, t115, t209, t285], []),
  (3, [t85, t106, t108, t169, t209, t285], [9400160]),
  (3, [t85, t120, t141, t169, t209, t285], [])]

def fam19 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t72, t85, t120, t169, t209, t249, t285], [8100726, 6100118, 3300293, 2100564, 2100819, 2100019, 2100242, 7000806, 1800881, 9400153, 5800135, 8600934, 4600833, 600825, 8600103, 8601046, 4600737, 600890, 8600071, 8601062, 4600689, 600299, 8600055, 7600119, 7600087, 4200007, 6200023, 200039]),
  (2, [t85, t89, t120, t209, t249, t285], [2600241]),
  (3, [t6, t85, t96, t120, t169, t209, t249], [5900124]),
  (3, [t16, t85, t120, t169, t204, t209, t285], []),
  (3, [t25, t85, t120, t169, t209, t249, t285], [2500801]),
  (3, [t43, t76, t85, t169, t209, t249, t285], []),
  (3, [t54, t120, t155, t169, t209, t249, t285], [7101036]),
  (3, [t80, t85, t96, t120, t209, t249, t285], [9000223, 2600094, 3400030, 3401053, 7800109, 1400093]),
  (3, [t85, t104, t120, t186, t209, t249, t285], [2800719, 8400270]),
  (3, [t85, t120, t153, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t219, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t295], []),
  (3, [t24, t54, t96, t120, t249, t285], []),
  (3, [t85, t96, t108, t136, t209, t285], []),
  (3, [t85, t108, t113, t169, t209, t285], [9400160]),
  (3, [t85, t120, t143, t169, t209, t285], [])]

def fam20 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t76, t85, t120, t169, t209, t249, t285], [8100710, 6100134, 3300309, 2100580, 2100835, 2100035, 2100258, 3000838, 3400217, 8600950, 4600849, 600873, 8600231, 8601046, 600330, 8600183, 600315, 7600247, 4200199, 200215]),
  (2, [t85, t96, t108, t120, t209, t285], [7700892, 5300748, 1300652, 3700348, 3700108, 3600382, 5400013, 349, 6200253, 200525, 8200301, 8200701]),
  (3, [t6, t85, t96, t120, t209, t249, t285], []),
  (3, [t16, t85, t120, t169, t209, t211, t285], []),
  (3, [t26, t85, t120, t186, t209, t249, t285], []),
  (3, [t43, t80, t85, t169, t209, t249, t285], []),
  (3, [t54, t120, t160, t169, t209, t249, t285], []),
  (3, [t80, t85, t108, t120, t169, t209, t285], [3000351, 601006, 1400750, 1400638, 3400093]),
  (3, [t85, t104, t169, t209, t233, t249, t285], []),
  (3, [t85, t120, t154, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t220, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t299], [7400593]),
  (3, [t24, t54, t108, t120, t169, t285], []),
  (3, [t85, t96, t108, t147, t209, t285], [3600863, 200783]),
  (3, [t85, t108, t114, t169, t209, t285], [7000751]),
  (3, [t85, t120, t144, t186, t209, t285], [])]

def fam21 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t80, t85, t120, t169, t209, t249, t285], [8100694, 6100150, 3300325, 2100596, 2100851, 2100051, 2100274, 5000854, 3800897, 1400281, 7800487, 8600966, 4600865, 600921, 8600455, 8601062, 4600785, 600394, 8600439, 8600183, 4600753, 600954, 8600423, 7600471, 7600391, 4200311, 200327, 8200343, 600407, 8600359, 8600375]),
  (2, [t85, t96, t108, t169, t209, t285], [6100908, 9700668, 2100364, 2100124, 2000846, 600029, 7600397, 8200318, 6600157, 7400173, 7400413, 8600365, 600541, 8600381, 600717]),
  (3, [t6, t85, t104, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t224, t285], []),
  (3, [t27, t32, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t90, t169, t209, t249, t285], []),
  (3, [t54, t120, t164, t169, t209, t249, t285], []),
  (3, [t80, t85, t115, t120, t169, t209, t249], [1800529]),
  (3, [t85, t105, t120, t169, t209, t249, t285], []),
  (3, [t85, t120, t155, t160, t209, t249, t285], [2600577]),
  (3, [t85, t120, t169, t209, t221, t224, t249], []),
  (3, [t85, t120, t169, t209, t249, t285, t300], []),
  (3, [t24, t85, t96, t108, t120, t285], []),
  (3, [t85, t96, t108, t152, t209, t285], []),
  (3, [t85, t108, t117, t169, t209, t285], [9400160]),
  (3, [t85, t120, t146, t169, t209, t285], [9800847])]

def fam22 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t96, t120, t169, t209, t249, t285], [6900214, 4500965, 4100373, 2900628, 2900883, 2900083, 2900306, 9000790, 2800073, 1400982, 8400919, 7400663, 5400410, 9400711, 3400970, 3400743, 9400331, 1400168, 3000935, 3400337, 9400807, 1000775, 9400871, 1401031, 9400887, 1400040, 9400903, 1400120]),
  (2, [t85, t96, t108, t209, t249, t285], [6100924, 3700764, 2100380, 2100140, 2000862, 600077, 7600573, 200781, 7400173, 1400589, 8600445, 600637, 8600557, 600749]),
  (3, [t6, t85, t108, t120, t169, t209, t249], [7900140]),
  (3, [t16, t85, t120, t169, t209, t233, t285], []),
  (3, [t27, t85, t120, t169, t209, t249, t285], [3600144]),
  (3, [t43, t85, t96, t120, t209, t249, t285], [2500801, 7301021]),
  (3, [t54, t120, t169, t174, t209, t249, t285], []),
  (3, [t80, t85, t120, t169, t204, t209, t249], [8600625]),
  (3, [t85, t106, t120, t169, t209, t249, t285], [200112, 5800302]),
  (3, [t85, t120, t155, t169, t209, t249, t304], [2600463]),
  (3, [t85, t120, t169, t209, t221, t249, t285], [4600785]),
  (3, [t85, t120, t169, t209, t249, t285, t301], [5400657]),
  (3, [t24, t85, t96, t108, t169, t285], []),
  (3, [t85, t96, t108, t155, t209, t285], []),
  (3, [t85, t108, t120, t129, t209, t285], [9400160]),
  (3, [t85, t120, t149, t186, t209, t249], [])]

def fam23 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t104, t120, t169, t209, t249, t285], [2900230, 2500933, 100389, 8900644, 8900915, 8900115, 8900338, 7000806, 6800137, 4400312, 7400023, 7400663, 7400969, 5400232, 9400986, 9400248, 5400347, 1000759, 5400328, 9400385, 5400280, 7000264, 7400296]),
  (2, [t85, t101, t120, t209, t249, t285], [6100940, 100716, 2100412, 2100156, 6800481, 8400238, 2600993, 8600222, 200174]),
  (3, [t6, t85, t108, t120, t169, t209, t285], []),
  (3, [t16, t85, t120, t169, t209, t241, t285], []),
  (3, [t28, t32, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t96, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t186, t209, t249, t285], []),
  (3, [t80, t85, t120, t169, t209, t244, t249], [8600673]),
  (3, [t85, t107, t108, t120, t169, t209, t285], [9800269]),
  (3, [t85, t120, t155, t169, t209, t270, t285], [1000015, 2600463]),
  (3, [t85, t120, t169, t209, t222, t249, t285], [8600625]),
  (3, [t85, t120, t169, t209, t249, t285, t303], []),
  (3, [t24, t85, t96, t108, t249, t285], []),
  (3, [t85, t96, t108, t164, t209, t285], []),
  (3, [t85, t108, t120, t136, t209, t285], [7800993]),
  (3, [t85, t120, t163, t209, t270, t285], [])]

def fam24 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t108, t120, t169, t209, t249, t285], [4900246, 8500917, 2100421, 900676, 900947, 900131, 900354, 3000838, 4800201, 7200840, 6400824, 9400215, 6400664, 9400711, 9401033, 5400232, 3400474, 1400392, 7400363, 5400353, 1400807, 3000791, 3400280, 3400856, 5000680, 7400472, 9400696, 7400552, 9400712, 7400648, 9400808]),
  (2, [t85, t104, t108, t169, t209, t285], [6000942, 3600270, 6600061, 4200334, 6600157]),
  (3, [t6, t85, t115, t120, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t244, t285], []),
  (3, [t28, t85, t120, t169, t209, t249, t285], []),
  (3, [t43, t85, t104, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t197, t209, t249, t285], []),
  (3, [t80, t85, t120, t169, t209, t249, t296], []),
  (3, [t85, t107, t120, t169, t209, t249, t285], []),
  (3, [t85, t120, t155, t186, t209, t249, t285], [7600495]),
  (3, [t85, t120, t169, t209, t223, t249, t285], [8600625]),
  (3, [t85, t120, t169, t209, t249, t285, t304], []),
  (3, [t24, t85, t97, t120, t249, t285], []),
  (3, [t85, t96, t108, t186, t209, t285], []),
  (3, [t85, t108, t120, t138, t169, t285], []),
  (3, [t85, t120, t169, t188, t209, t285], [3001057])]

def fam25 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t115, t120, t169, t209, t249, t285], [8900262, 6100437, 4900692, 4900963, 4900147, 4900386, 5000854, 800265, 400952, 3400343, 3400743, 3400010, 9400248, 7400522, 1400392, 5401034, 7000823, 3000408]),
  (2, [t85, t108, t120, t186, t209, t285], [7900956, 1500684, 3900428, 3900172, 7600655, 201022, 7800993, 2800206, 5400174, 6400270]),
  (3, [t6, t85, t120, t121, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t261, t285], []),
  (3, [t29, t32, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t108, t120, t169, t209, t285], [8500721, 9300670]),
  (3, [t54, t120, t169, t200, t209, t249, t285], []),
  (3, [t80, t85, t120, t169, t209, t249, t306], []),
  (3, [t85, t108, t115, t120, t169, t209, t285], [6200301]),
  (3, [t85, t120, t156, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t226, t249, t285], [3400545]),
  (3, [t85, t120, t169, t209, t249, t285, t305], []),
  (3, [t24, t85, t101, t120, t249, t285], []),
  (3, [t85, t96, t108, t193, t209, t285], []),
  (3, [t85, t108, t120, t145, t169, t209], [4200783]),
  (3, [t85, t120, t169, t201, t281, t285], [])]

def fam26 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t152, t169, t209, t249, t285], [4300294, 1500501, 8700053, 300724, 300995, 300179, 300418, 5800297, 2400855, 6801051, 800417, 6800840, 8400440, 4801067, 3800465, 9800057, 6000041, 8800026, 7800497, 3800121, 105, 4800538, 5800513, 1800185, 8000169, 6801050, 1800529, 7800249, 4000233, 800379]),
  (2, [t85, t108, t152, t169, t209, t285], [3500972, 7100700, 9500540, 9500460, 9500188, 5001022, 3001009, 9000814, 5200798, 7001041, 3000910, 9200894, 3200990]),
  (3, [t6, t85, t120, t152, t169, t209, t249], [3300188, 6300204, 300236]),
  (3, [t16, t85, t120, t169, t209, t268, t285], [200880]),
  (3, [t29, t85, t120, t169, t209, t249, t285], []),
  (3, [t43, t85, t108, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t204, t209, t249, t285], []),
  (3, [t80, t85, t120, t169, t209, t260, t285], []),
  (3, [t85, t108, t120, t147, t169, t209, t285], [8000655, 1200417, 333, 9000414]),
  (3, [t85, t120, t158, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t227, t233, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t307], []),
  (3, [t24, t85, t108, t120, t186, t285], []),
  (3, [t85, t96, t108, t197, t209, t285], []),
  (3, [t85, t108, t120, t149, t169, t209], []),
  (3, [t85, t120, t169, t209, t258, t281], [])]

def fam27 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t155, t169, t209, t249, t285], [100310, 7300517, 100037, 6100740, 6101011, 6100195, 6100434, 8600934, 7600809, 1600393, 7400663, 7000953, 8200871, 4200456, 2600313, 8600769, 4601066, 6600377, 2600329, 8600705, 4600395, 6600361, 2600345]),
  (2, [t85, t113, t169, t209, t249, t285], [5800781, 1800318, 2200047]),
  (3, [t6, t85, t120, t155, t169, t209, t249], [1100252]),
  (3, [t16, t85, t120, t169, t209, t274, t285], []),
  (3, [t30, t32, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t115, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t214, t249, t285], []),
  (3, [t80, t85, t120, t169, t223, t249, t285], []),
  (3, [t85, t108, t120, t152, t169, t209, t285], [1600349, 600366, 4600398, 8600430]),
  (3, [t85, t120, t158, t209, t233, t249, t285], []),
  (3, [t85, t120, t169, t209, t227, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t308], []),
  (3, [t24, t85, t108, t123, t169, t285], []),
  (3, [t85, t96, t108, t200, t209, t285], []),
  (3, [t85, t108, t120, t157, t209, t285], [7000751]),
  (3, [t85, t120, t169, t209, t262, t285], [3001057])]

def fam28 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t160, t169, t209, t249, t285], [100326, 7300533, 6100756, 6101027, 6100211, 6100450, 8600950, 7600857, 1600489, 9400711, 5001017, 8200887, 4200472, 2600313, 4600586, 2600457, 4600411, 2600345, 4600505, 4600473]),
  (2, [t85, t114, t169, t209, t249, t285], [7200063, 1400189, 9800334, 200079]),
  (3, [t6, t85, t120, t160, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t281, t285], []),
  (3, [t30, t85, t120, t169, t209, t249, t285], []),
  (3, [t43, t85, t120, t169, t209, t253, t285], [5500129]),
  (3, [t54, t120, t169, t209, t224, t249, t285], []),
  (3, [t80, t85, t120, t185, t209, t249, t285], []),
  (3, [t85, t108, t120, t155, t169, t209, t285], [3800399, 6600157, 7400365, 5400606]),
  (3, [t85, t120, t159, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t228, t249, t285], [1400641]),
  (3, [t85, t120, t169, t209, t249, t285, t309], []),
  (3, [t24, t85, t108, t152, t169, t285], []),
  (3, [t85, t96, t108, t204, t209, t285], []),
  (3, [t85, t108, t120, t158, t209, t285], [9400160]),
  (3, [t85, t120, t169, t209, t270, t304], [])]

def fam29 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t164, t169, t209, t249, t285], [100342, 7300549, 6100772, 6101043, 6100227, 6100466, 8600966, 7600905, 1600601, 3400743, 1001065, 8200903, 4200488, 2600329, 4600634, 2600457, 4600043]),
  (2, [t85, t120, t129, t209, t249, t285], [1700988, 4900620, 7700476, 7700204, 6800481, 200112, 8201009, 4200830, 5800366]),
  (3, [t6, t85, t120, t164, t169, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t285, t286], []),
  (3, [t31, t32, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t120, t173, t209, t249, t285], [9500113]),
  (3, [t54, t120, t169, t209, t233, t249, t285], []),
  (3, [t80, t85, t120, t186, t209, t249, t285], []),
  (3, [t85, t108, t120, t160, t169, t209, t285], [7400609]),
  (3, [t85, t120, t160, t169, t209, t274, t285], []),
  (3, [t85, t120, t169, t209, t229, t249, t285], [7400449, 1400641]),
  (3, [t85, t120, t169, t209, t249, t285, t311], []),
  (3, [t24, t85, t120, t129, t249, t285], []),
  (3, [t85, t96, t108, t209, t224, t285], [8000879, 6600799]),
  (3, [t85, t108, t120, t162, t209, t285], [9400160]),
  (3, [t85, t120, t169, t209, t275, t285], [])]

def fam30 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t186, t209, t249, t285], [7100374, 4300581, 3100788, 3100004, 3100259, 3100498, 1601014, 5200919, 3200731, 4600184, 8800026, 1200504, 9600393, 1600827, 9600489, 1600907, 9600601, 1600987, 4600793, 1600650, 4600841, 1600059, 4600889, 1600427]),
  (2, [t85, t120, t136, t209, t249, t285], [701004, 1900604, 6700492, 6700220, 5200687, 5200703, 8200109, 8600369, 7201025, 3200862, 4800382]),
  (3, [t6, t85, t120, t169, t170, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t285, t296], []),
  (3, [t31, t85, t120, t169, t209, t249, t285], []),
  (3, [t43, t85, t120, t186, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t241, t249, t285], []),
  (3, [t80, t85, t151, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t164, t169, t209, t285], [7400381]),
  (3, [t85, t120, t160, t186, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t230, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t312], []),
  (3, [t24, t85, t120, t136, t249, t285], []),
  (3, [t85, t96, t108, t209, t226, t285], []),
  (3, [t85, t108, t120, t163, t209, t285], [7000751]),
  (3, [t85, t120, t186, t209, t270, t285], [])]

def fam31 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t197, t209, t249, t285], [900390, 8100597, 6900804, 6500308, 6900020, 6900275, 6900514, 2400731, 1001030, 8800026, 7400168, 9000935, 5000536, 1400937, 9400666, 7400609, 3401001, 6200985, 7400075, 7401049, 3400443]),
  (2, [t85, t120, t138, t169, t249, t285], [3701020, 900588, 9700556, 9700236, 5200271, 3400559, 1800829, 201041, 6200926, 7800398]),
  (3, [t6, t85, t120, t169, t186, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t285, t302], []),
  (3, [t32, t43, t85, t120, t209, t249, t285], [8500209, 8000524]),
  (3, [t43, t85, t152, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t244, t249, t285], []),
  (3, [t81, t85, t120, t169, t209, t249, t285], [3800897]),
  (3, [t85, t108, t120, t169, t186, t209, t285], [4400397, 3800190]),
  (3, [t85, t120, t160, t209, t249, t274, t285], []),
  (3, [t85, t120, t169, t209, t231, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t313], []),
  (3, [t24, t85, t120, t169, t270, t285], []),
  (3, [t85, t96, t108, t209, t229, t285], [7000751]),
  (3, [t85, t108, t120, t166, t209, t285], [9400160]),
  (3, [t85, t120, t186, t209, t275, t285], [])]

def fam32 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t200, t209, t249, t285], [100406, 7300613, 6100820, 6100036, 6100291, 6100530, 1600763, 8601046, 7600314, 8200951, 5400232, 9000458, 4200552, 2600313, 4600570, 2600042, 4600459, 4600058]),
  (2, [t85, t120, t144, t169, t209, t285], [9200335, 6200128, 5800845]),
  (3, [t6, t85, t120, t169, t197, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t285, t306], []),
  (3, [t32, t54, t85, t120, t209, t249, t285], [5100017]),
  (3, [t43, t85, t155, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t254, t285], []),
  (3, [t82, t85, t120, t169, t209, t249, t285], [4600865]),
  (3, [t85, t108, t120, t169, t193, t209, t285], [3800413, 8200318]),
  (3, [t85, t120, t161, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t232, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t315], []),
  (3, [t32, t43, t85, t108, t209, t285], [7700961]),
  (3, [t85, t96, t108, t209, t233, t285], []),
  (3, [t85, t108, t120, t169, t209, t221], [3400799]),
  (3, [t85, t126, t142, t209, t249, t285], [])]

def fam33 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t204, t209, t249, t285], [100422, 7300629, 6100836, 6100052, 6100307, 6100546, 1600779, 8601062, 7600378, 4600359, 8200967, 9400248, 5000506, 4200568, 2600329, 4600618, 2600042, 4600123]),
  (2, [t85, t120, t149, t169, t209, t249], [7200367, 3800861, 9800430]),
  (3, [t6, t85, t120, t169, t200, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t285, t310], []),
  (3, [t32, t64, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t160, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t261, t285], []),
  (3, [t83, t85, t120, t169, t209, t249, t285], [4600785, 4600689]),
  (3, [t85, t108, t120, t169, t197, t209, t285], [8200429]),
  (3, [t85, t120, t162, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t234, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t316], []),
  (3, [t32, t85, t108, t152, t209, t285], []),
  (3, [t85, t96, t108, t209, t241, t285], []),
  (3, [t85, t108, t120, t169, t209, t258], [3400815]),
  (3, [t85, t128, t151, t209, t249, t285], [])]

def fam34 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t224, t249, t285], [7100454, 4300661, 3100868, 3100068, 1100579, 3100339, 3100578, 8600795, 1600087, 5200983, 8600344, 4800538, 1200584, 4600409, 1600650, 1600667, 4600298, 1600139, 8600625, 4600362, 3600346, 1600475]),
  (2, [t85, t120, t158, t209, t249, t285], [200112, 4600462]),
  (3, [t6, t85, t120, t169, t204, t209, t249], []),
  (3, [t16, t85, t120, t169, t209, t285, t314], []),
  (3, [t32, t68, t85, t120, t209, t249, t285], [6100305]),
  (3, [t43, t85, t164, t169, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t268, t285], []),
  (3, [t84, t85, t120, t169, t209, t249, t285], [4600753]),
  (3, [t85, t108, t120, t169, t200, t209, t285], [1400641, 7400445]),
  (3, [t85, t120, t162, t209, t249, t268, t285], []),
  (3, [t85, t120, t169, t209, t235, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t317], []),
  (3, [t32, t85, t120, t138, t249, t285], []),
  (3, [t85, t96, t108, t209, t244, t285], []),
  (3, [t85, t108, t120, t169, t209, t291], []),
  (3, [t85, t138, t142, t169, t249, t285], [])]

def fam35 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t233, t249, t285], [4900470, 2100677, 900884, 900084, 8500563, 900355, 900594, 7201051, 6400811, 3000151, 4800538, 3001015, 3400328, 9000616, 3400545, 6200441, 9400425, 9400666, 1400641, 7400442, 4200426, 1400155, 1400490, 7400491]),
  (2, [t85, t120, t162, t209, t249, t285], [200112, 8600478]),
  (3, [t6, t85, t120, t169, t209, t210, t249], []),
  (3, [t17, t85, t120, t169, t209, t249, t285], []),
  (3, [t32, t72, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t173, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t274, t285], []),
  (3, [t85, t86, t120, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t169, t204, t209, t285], [7400461]),
  (3, [t85, t120, t163, t169, t209, t249, t285], [8600769]),
  (3, [t85, t120, t169, t209, t236, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t285, t318], []),
  (3, [t32, t85, t120, t209, t270, t285], []),
  (3, [t85, t96, t108, t209, t261, t285], [8000895, 6600815]),
  (3, [t85, t108, t120, t169, t209, t294], []),
  (3, [t85, t140, t142, t169, t209, t285], [])]

def fam36 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t241, t249, t285], [6100486, 3300693, 2100900, 2100100, 2100371, 2100610, 7600827, 6600167, 1600650, 4201031, 7000360, 9400666, 200632, 8600554, 600171, 8600602, 600507]),
  (2, [t85, t120, t163, t209, t249, t285], [7800205, 2200494, 4600383]),
  (3, [t6, t85, t120, t169, t209, t224, t249], []),
  (3, [t18, t85, t120, t169, t209, t249, t285], []),
  (3, [t32, t76, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t186, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t281, t285], []),
  (3, [t85, t87, t120, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t169, t209, t224, t285], [4400477, 5400526]),
  (3, [t85, t120, t163, t209, t249, t281, t285], []),
  (3, [t85, t120, t169, t209, t237, t249, t285], [2600577]),
  (3, [t85, t120, t169, t209, t249, t296, t310], [4600689]),
  (3, [t35, t85, t120, t169, t249, t285], []),
  (3, [t85, t96, t108, t209, t263, t285], []),
  (3, [t85, t108, t120, t169, t209, t298], []),
  (3, [t85, t143, t151, t169, t209, t285], [])]

def fam37 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t244, t249, t285], [100502, 7300709, 6100916, 6100116, 6100387, 6100626, 1600859, 8600183, 7600938, 4600375, 8201047, 1400392, 3001018, 4200648, 2600457, 4600027, 2600042, 4600107, 4600682]),
  (2, [t85, t120, t166, t209, t249, t285], [200112, 6600510]),
  (3, [t6, t85, t120, t169, t209, t233, t249], []),
  (3, [t19, t24, t85, t120, t169, t249, t285], []),
  (3, [t32, t80, t85, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t197, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t285, t290], []),
  (3, [t85, t88, t120, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t169, t209, t229, t285], [9800254, 5800509, 4200334, 7800446]),
  (3, [t85, t120, t164, t186, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t238, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t306, t310], [8600705]),
  (3, [t36, t85, t120, t209, t249, t285], []),
  (3, [t85, t96, t108, t209, t268, t285], []),
  (3, [t85, t108, t120, t169, t209, t304], []),
  (3, [t96, t120, t130, t209, t249, t285], [])]

def fam38 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t261, t285], [7100534, 4300741, 3100948, 3100148, 3100403, 1100850, 3100658, 8600875, 5201063, 1200664, 6600872, 6801050, 4600521, 1600059, 1600619, 4600074, 1600139, 1600635, 8600673, 4600922, 3600906, 1600523]),
  (2, [t85, t120, t169, t191, t209, t285], [600877, 6200128]),
  (3, [t6, t85, t120, t169, t209, t241, t249], []),
  (3, [t19, t85, t120, t169, t209, t249, t285], []),
  (3, [t32, t85, t89, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t200, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t285, t296], []),
  (3, [t85, t89, t120, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t169, t209, t233, t285], [2200525, 200462]),
  (3, [t85, t120, t165, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t239, t249, t285], []),
  (3, [t85, t120, t169, t209, t261, t281, t285], [6400063, 6600415, 4600737, 6600431]),
  (3, [t37, t85, t120, t209, t249, t285], []),
  (3, [t85, t96, t108, t209, t274, t285], []),
  (3, [t85, t108, t120, t169, t215, t285], []),
  (3, [t96, t120, t132, t209, t249, t285], [])]

def fam39 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t268, t285], [2900550, 100757, 8900964, 8900164, 8900419, 2500834, 8900674, 4400891, 7000263, 6801050, 1000024, 5400856, 7000680, 1400561, 2200553, 7400537, 7400075, 3400090, 1400155, 9401002, 5400539]),
  (2, [t85, t120, t169, t209, t221, t249], [4200893, 200526]),
  (3, [t6, t85, t120, t169, t209, t244, t249], []),
  (3, [t20, t24, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t96, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t204, t209, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t285, t302], []),
  (3, [t85, t90, t120, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t169, t209, t241, t285], [3400541, 6200302]),
  (3, [t85, t120, t166, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t240, t249, t285], []),
  (3, [t85, t120, t169, t209, t261, t285, t314], [4600753]),
  (3, [t44, t54, t120, t169, t209, t285], []),
  (3, [t85, t96, t108, t209, t281, t285], [7000751]),
  (3, [t85, t108, t120, t169, t223, t285], [1400831]),
  (3, [t108, t120, t132, t169, t209, t285], [])]

def fam40 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t274, t285], [6100566, 3300773, 2100980, 2100180, 2100435, 8100818, 2100690, 7600907, 6600279, 1600059, 4200040, 200696, 1400433, 5400904, 9000888, 7400075, 8600505, 8600473, 600651, 8600106, 600171, 8600011, 600555]),
  (2, [t85, t120, t169, t209, t227, t285], [2600909, 6200128]),
  (3, [t6, t85, t120, t169, t209, t249, t250], []),
  (3, [t20, t85, t120, t169, t209, t249, t285], []),
  (3, [t32, t85, t104, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t213, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t285, t306], []),
  (3, [t85, t92, t96, t120, t209, t249, t285], [9000607, 3801069, 1800973, 5800141]),
  (3, [t85, t108, t120, t169, t209, t244, t285], [5400657, 7400557]),
  (3, [t85, t120, t166, t209, t249, t285, t302], []),
  (3, [t85, t120, t169, t209, t242, t249, t285], []),
  (3, [t85, t120, t169, t209, t274, t281, t285], [9400047, 5400079, 8600769]),
  (3, [t44, t85, t96, t120, t209, t285], []),
  (3, [t85, t96, t108, t209, t285, t296], []),
  (3, [t85, t108, t120, t169, t225, t285], []),
  (3, [t108, t120, t147, t186, t209, t285], [])]

def fam41 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t281, t285], [6100582, 3300789, 2100996, 2100196, 2100451, 8100802, 2100706, 7600939, 7600619, 6600295, 1600139, 4200056, 200712, 7400449, 1400936, 5000920, 1400155, 600651, 2600577, 6600585, 8600569, 600171, 8600058, 8600682, 8600091, 600571]),
  (2, [t85, t120, t169, t209, t246, t285], [4600925, 6200128]),
  (3, [t6, t85, t120, t169, t209, t249, t261], []),
  (3, [t21, t24, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t108, t120, t169, t209, t285], [4900782]),
  (3, [t43, t85, t169, t209, t224, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t285, t310], []),
  (3, [t85, t92, t120, t169, t209, t249, t285], [200671, 5000447, 7000157]),
  (3, [t85, t108, t120, t169, t209, t261, t285], [4400573, 5400542]),
  (3, [t85, t120, t167, t169, t209, t249, t285], [8600705]),
  (3, [t85, t120, t169, t209, t243, t249, t285], []),
  (3, [t85, t120, t169, t224, t249, t285, t310], [4600785]),
  (3, [t44, t85, t96, t169, t209, t285], []),
  (3, [t85, t96, t108, t209, t285, t299], []),
  (3, [t85, t108, t120, t173, t209, t285], [9400160]),
  (3, [t120, t130, t169, t209, t249, t285], [])]

def fam42 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t285, t296], [7100614, 4300821, 3101028, 3100228, 3100483, 3100722, 8600955, 1600391, 5200072, 1200728, 2600968, 800379, 4600617, 1600427, 1600587, 4600122, 1600475, 4600698, 1600523]),
  (2, [t85, t120, t169, t209, t249, t258], [4200941, 200542, 600431]),
  (3, [t6, t85, t120, t169, t209, t249, t268], []),
  (3, [t21, t85, t120, t169, t209, t249, t285], []),
  (3, [t32, t85, t108, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t233, t249, t285], []),
  (3, [t54, t120, t169, t209, t249, t285, t314], []),
  (3, [t85, t93, t96, t120, t209, t249, t285], [3000623, 5800046, 7800989, 1800173]),
  (3, [t85, t108, t120, t169, t209, t268, t285], [200605, 8200478]),
  (3, [t85, t120, t168, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t244, t281, t285], []),
  (3, [t85, t120, t177, t186, t209, t249, t285], [9600511]),
  (3, [t44, t85, t120, t186, t209, t285], []),
  (3, [t85, t96, t108, t209, t285, t301], []),
  (3, [t85, t108, t120, t175, t209, t285], []),
  (3, [t120, t136, t209, t224, t249, t285], [9200879, 4200943])]

def fam43 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t285, t302], [8900630, 6100837, 4901044, 4900244, 4900499, 4900738, 500002, 1201067, 400971, 5000503, 800379, 7000104, 3000760, 7400593, 4200649, 3400633, 3400443, 9400138, 7400491, 5400657, 2200730, 1400714, 5400539]),
  (2, [t85, t120, t169, t209, t249, t294], [2200957, 4200286, 8200574]),
  (3, [t6, t85, t120, t169, t209, t249, t274], []),
  (3, [t22, t24, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t115, t120, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t241, t249, t285], []),
  (3, [t55, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t93, t108, t120, t169, t209, t285], [1000639, 3800654, 5800590, 3800173]),
  (3, [t85, t108, t120, t169, t209, t274, t285], [3400621, 8200318]),
  (3, [t85, t120, t169, t170, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t245, t249, t285], []),
  (3, [t85, t120, t180, t186, t209, t249, t285], []),
  (3, [t44, t85, t152, t169, t209, t285], []),
  (3, [t85, t96, t108, t209, t285, t302], []),
  (3, [t85, t108, t120, t176, t209, t285], [7800993]),
  (3, [t120, t136, t209, t249, t261, t285], [9200895, 4200959])]

def fam44 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t285, t306], [6100646, 3300853, 2101060, 2100260, 2100515, 2100754, 7600987, 600407, 6600519, 1600427, 4200120, 200776, 3000984, 3400443, 600603, 8600154, 600507, 8600746, 600555]),
  (2, [t85, t120, t169, t209, t249, t304], [4201005, 200606]),
  (3, [t6, t85, t120, t169, t209, t249, t281], []),
  (3, [t22, t85, t120, t169, t209, t249, t285], []),
  (3, [t32, t85, t120, t124, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t244, t249, t285], []),
  (3, [t56, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t93, t120, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t169, t209, t281, t285], [3400637, 4200334, 9400494]),
  (3, [t85, t120, t169, t171, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t246, t249, t285], []),
  (3, [t85, t120, t183, t186, t209, t249, t285], []),
  (3, [t46, t85, t120, t209, t249, t285], []),
  (3, [t85, t96, t108, t209, t285, t306], []),
  (3, [t85, t108, t120, t179, t209, t285], []),
  (3, [t120, t139, t186, t209, t249, t285], [])]

def fam45 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t285, t310], [6100662, 3300869, 2100005, 2100276, 2100531, 2100770, 7601019, 7600667, 7600587, 6600535, 1600475, 4200136, 6200296, 200792, 9001000, 7400491, 600603, 8600665, 600507, 8600762, 600571]),
  (2, [t85, t120, t169, t209, t253, t285], [3000145, 200880, 3901021, 6200128]),
  (3, [t6, t85, t120, t169, t209, t249, t296], []),
  (3, [t23, t24, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t152, t209, t249, t285], [3300540, 300556]),
  (3, [t43, t85, t169, t209, t249, t253, t285], []),
  (3, [t57, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t95, t96, t120, t209, t249, t285], [3800221]),
  (3, [t85, t108, t120, t169, t209, t285, t296], [4400653]),
  (3, [t85, t120, t169, t172, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t246, t285, t302], []),
  (3, [t85, t120, t186, t197, t209, t249, t285], [9000817]),
  (3, [t47, t54, t120, t209, t249, t285], []),
  (3, [t85, t96, t108, t209, t285, t310], []),
  (3, [t85, t108, t120, t182, t209, t285], []),
  (3, [t80, t108, t136, t209, t285], [])]

def fam46 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t85, t120, t169, t209, t249, t285, t314], [6100678, 3300885, 2100021, 2100292, 2100547, 2100786, 7601035, 7600635, 6600551, 1600523, 4200152, 200808, 1001016, 5400539, 8600681, 600555, 8600170, 600571]),
  (2, [t85, t120, t169, t209, t257, t285], [2201037, 1401038]),
  (3, [t6, t85, t120, t169, t209, t249, t302], []),
  (3, [t23, t85, t120, t169, t209, t249, t285], []),
  (3, [t32, t85, t120, t155, t209, t249, t285], [1100572]),
  (3, [t43, t85, t169, t209, t249, t261, t285], []),
  (3, [t58, t85, t120, t169, t209, t249, t285], [2600241]),
  (3, [t85, t95, t120, t169, t209, t249, t285], []),
  (3, [t85, t108, t120, t169, t209, t285, t301], [7800685]),
  (3, [t85, t120, t169, t173, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t247, t249, t285], []),
  (3, [t85, t120, t186, t198, t209, t249, t285], []),
  (3, [t47, t85, t108, t120, t209, t285], []),
  (3, [t85, t96, t108, t209, t285, t314], []),
  (3, [t85, t108, t120, t185, t209, t285], []),
  (3, [t85, t94, t108, t209, t285], [])]

def fam47 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t16, t85, t120, t169, t209], [3100032, 3100016]),
  (2, [t85, t120, t169, t209, t260, t285], [2201053, 5401054]),
  (3, [t6, t85, t120, t169, t209, t249, t306], []),
  (3, [t24, t43, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t160, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t268, t285], []),
  (3, [t59, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t104, t120, t209, t249, t285], [8200253]),
  (3, [t85, t108, t120, t169, t209, t285, t302], [6200701, 4200510]),
  (3, [t85, t120, t169, t174, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t248, t249, t285], []),
  (3, [t85, t120, t186, t200, t209, t249, t285], []),
  (3, [t47, t85, t108, t209, t249, t285], []),
  (3, [t85, t96, t111, t209, t249, t285], [7400160]),
  (3, [t85, t108, t123, t169, t209, t285], []),
  (3, [t85, t94, t112, t209, t285], [])]

def fam48 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t24, t85, t120, t169, t249], [3100048, 3100016, 5200012, 1200028]),
  (2, [t85, t120, t169, t209, t270, t285], [6101036, 2100572, 2100508, 2100252, 7600495, 4200014, 3001057, 3000031, 601070, 6600383]),
  (3, [t6, t85, t120, t169, t209, t249, t310], []),
  (3, [t24, t54, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t164, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t274, t285], []),
  (3, [t60, t85, t96, t120, t209, t249, t285], [601052]),
  (3, [t85, t96, t108, t120, t169, t209, t285], [2200429]),
  (3, [t85, t108, t120, t169, t209, t285, t306], [3400717, 2200350]),
  (3, [t85, t120, t169, t176, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t250, t285], []),
  (3, [t85, t120, t186, t204, t209, t249, t285], []),
  (3, [t48, t54, t120, t209, t249, t285], []),
  (3, [t85, t96, t113, t209, t249, t285], [7400160]),
  (3, [t85, t108, t124, t169, t209, t285], [9400160]),
  (3, [t85, t96, t108, t145, t209], [])]

def fam49 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t32, t85, t120, t209, t249], [3100064, 3100016]),
  (2, [t85, t120, t169, t223, t249, t285], [2200030, 8200638]),
  (3, [t6, t85, t120, t169, t209, t249, t314], []),
  (3, [t24, t64, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t186, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t281, t285], []),
  (3, [t60, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t108, t120, t209, t249, t285], [6200605]),
  (3, [t85, t108, t120, t169, t209, t285, t310], [3400733]),
  (3, [t85, t120, t169, t177, t209, t249, t285], [4600833, 600479]),
  (3, [t85, t120, t169, t209, t249, t251, t285], []),
  (3, [t85, t120, t186, t209, t224, t249, t285], []),
  (3, [t48, t85, t120, t209, t249, t285], []),
  (3, [t85, t96, t114, t209, t249, t285], [7400160]),
  (3, [t85, t108, t129, t152, t209, t285], []),
  (3, [t85, t96, t108, t209, t221], [])]

def fam50 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t43, t85, t169, t209, t249], [9900080, 8700016]),
  (2, [t85, t120, t173, t209, t249, t285], [5000161, 6200033, 200112, 1900670]),
  (3, [t7, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t68, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t197, t209, t249, t285], [6200033]),
  (3, [t43, t85, t169, t209, t249, t285, t289], []),
  (3, [t61, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t108, t169, t209, t249, t285], [1400433, 600621]),
  (3, [t85, t108, t120, t169, t209, t285, t314], [3400749]),
  (3, [t85, t120, t169, t178, t209, t249, t285], [3600144]),
  (3, [t85, t120, t169, t209, t249, t252, t285], []),
  (3, [t85, t120, t186, t209, t233, t249, t285], []),
  (3, [t49, t54, t108, t169, t209, t285], []),
  (3, [t85, t96, t119, t209, t249, t285], [7400160]),
  (3, [t85, t108, t129, t169, t209, t285], []),
  (3, [t85, t96, t108, t209, t258], [])]

def fam51 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t54, t120, t169, t209, t249], [9100096, 5100016, 1200076, 7200092]),
  (2, [t85, t120, t176, t209, t249, t285], [3600144, 8600369, 1400702]),
  (3, [t8, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t72, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t200, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t285, t296], []),
  (3, [t62, t85, t108, t120, t169, t209, t285], [2600686, 8600622, 4600558, 4601068]),
  (3, [t85, t96, t115, t120, t209, t249, t285], [4200301]),
  (3, [t85, t108, t120, t186, t209, t249, t285], [3800222]),
  (3, [t85, t120, t169, t179, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t253, t285], []),
  (3, [t85, t120, t186, t209, t241, t249, t285], [4600833]),
  (3, [t49, t85, t108, t169, t209, t285], []),
  (3, [t85, t96, t120, t138, t249, t285], []),
  (3, [t85, t108, t129, t209, t249, t285], []),
  (3, [t85, t96, t108, t223, t285], [])]

def fam52 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t85, t96, t120, t209, t249], [9400112, 3400076, 1000060, 9400012, 9300220, 9900913, 5900140, 7500108]),
  (2, [t85, t120, t179, t209, t249, t285], [3600144, 7400126, 8200718]),
  (3, [t9, t85, t120, t169, t209, t249, t285], [8500721]),
  (3, [t24, t76, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t204, t209, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t285, t302], []),
  (3, [t62, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t136, t209, t249, t285], [2000317]),
  (3, [t85, t108, t152, t169, t209, t249, t285], [9000830, 3000926]),
  (3, [t85, t120, t169, t180, t209, t249, t285], [4600849]),
  (3, [t85, t120, t169, t209, t249, t254, t285], []),
  (3, [t85, t120, t186, t209, t242, t249, t285], []),
  (3, [t50, t54, t108, t120, t209, t285], []),
  (3, [t85, t96, t120, t144, t209, t285], [7400160]),
  (3, [t85, t108, t136, t169, t209, t285], [3001009]),
  (3, [t85, t96, t146, t209, t285], [])]

def fam53 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t85, t108, t120, t169, t209], [7400128, 1400092, 5000044, 7400028, 3700188, 2900172, 1900913, 7900124, 9500108]),
  (2, [t85, t120, t182, t209, t249, t285], [3600144, 5400142, 8200734]),
  (3, [t10, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t80, t85, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t209, t212, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t285, t306], []),
  (3, [t63, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t152, t209, t249, t285], [9600349, 6600829, 4600845, 600861]),
  (3, [t85, t108, t169, t209, t249, t268, t285], []),
  (3, [t85, t120, t169, t181, t209, t249, t285], [3600144]),
  (3, [t85, t120, t169, t209, t249, t255, t285], []),
  (3, [t85, t120, t186, t209, t244, t249, t285], []),
  (3, [t50, t85, t108, t120, t209, t285], []),
  (3, [t85, t96, t120, t149, t209, t249], []),
  (3, [t85, t108, t136, t209, t249, t285], [4400895]),
  (3, [t108, t136, t147, t209, t285], [])]

def fam54 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t6, t85, t120, t186, t209, t249], [9600144, 1100156, 7700172]),
  (2, [t85, t120, t185, t209, t249, t285], [3600144, 1400158, 8200750]),
  (3, [t11, t16, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t88, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t209, t224, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t285, t310], []),
  (3, [t64, t85, t96, t120, t209, t249, t285], [8600369, 5800013]),
  (3, [t85, t96, t120, t155, t209, t249, t285], [3400545, 5400365, 7400014, 7401005]),
  (3, [t85, t111, t120, t169, t209, t249, t285], [6200128, 8600765]),
  (3, [t85, t120, t169, t182, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t256, t285], []),
  (3, [t85, t120, t186, t209, t249, t261, t285], []),
  (3, [t54, t85, t96, t108, t209, t285], []),
  (3, [t85, t96, t120, t191, t209, t285], [7400160]),
  (3, [t85, t108, t137, t169, t209, t285], [3001009]),
  (3, [t108, t136, t209, t224, t285], [])]

def fam55 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t12, t85, t120, t169, t209, t285], [8500721]),
  (2, [t85, t142, t169, t209, t249, t285], [5800527, 4600559, 9800575]),
  (3, [t11, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t85, t96, t120, t169, t249, t285], [5900364]),
  (3, [t32, t85, t120, t209, t233, t249, t285], []),
  (3, [t43, t85, t169, t209, t249, t285, t314], []),
  (3, [t64, t85, t108, t120, t169, t209, t285], [5800702, 7800013]),
  (3, [t85, t96, t120, t160, t209, t249, t285], [1400561]),
  (3, [t85, t113, t120, t169, t209, t249, t285], [200112, 6200128, 5800781, 1800318]),
  (3, [t85, t120, t169, t183, t209, t249, t285], [4600865]),
  (3, [t85, t120, t169, t209, t249, t257, t285], []),
  (3, [t85, t120, t186, t209, t249, t268, t285], []),
  (3, [t54, t96, t108, t120, t209, t285], []),
  (3, [t85, t96, t120, t209, t221, t249], [7800943, 1400799]),
  (3, [t85, t108, t138, t152, t169, t285], []),
  (3, [t108, t136, t209, t261, t285], [])]

def fam56 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t24, t85, t120, t169, t285], [3100048, 3100032]),
  (2, [t85, t151, t169, t209, t249, t285], [7800543, 1800591]),
  (3, [t12, t16, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t96, t120, t209, t249, t285], []),
  (3, [t32, t85, t120, t209, t241, t249, t285], []),
  (3, [t44, t85, t108, t120, t169, t209, t285], []),
  (3, [t64, t85, t120, t176, t209, t249, t285], []),
  (3, [t85, t96, t120, t164, t209, t249, t285], [7400593, 5400381]),
  (3, [t85, t113, t169, t209, t249, t274, t285], []),
  (3, [t85, t120, t169, t184, t209, t249, t285], [3600144]),
  (3, [t85, t120, t169, t209, t249, t258, t261], []),
  (3, [t85, t120, t186, t209, t249, t274, t285], [4600849]),
  (3, [t54, t96, t108, t169, t209, t285], []),
  (3, [t85, t96, t120, t209, t227, t285], [7400160]),
  (3, [t85, t108, t138, t169, t209, t285], []),
  (3, [t114, t134, t209, t249, t285], [])]

def fam57 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t32, t85, t120, t209, t285], [3100064, 3100032]),
  (2, [t6, t85, t96, t108, t209], [8600160]),
  (3, [t12, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t85, t104, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t209, t244, t249, t285], []),
  (3, [t44, t85, t120, t169, t209, t249, t285], []),
  (3, [t64, t85, t120, t186, t209, t249, t285], []),
  (3, [t85, t96, t120, t186, t209, t249, t285], [2400397]),
  (3, [t85, t114, t120, t169, t209, t249, t285], [7800205, 6200128, 3800797, 9800334]),
  (3, [t85, t120, t169, t185, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t258, t285], [4600753]),
  (3, [t85, t120, t186, t209, t249, t276, t285], []),
  (3, [t54, t96, t108, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t246, t285], [7400160]),
  (3, [t85, t108, t138, t169, t249, t285], []),
  (3, [t120, t134, t209, t249, t285], [])]

def fam58 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t43, t85, t169, t209, t285], [9900080, 8700032]),
  (2, [t24, t85, t96, t108, t285], [8600160]),
  (3, [t13, t16, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t108, t120, t169, t209, t285], [6900766]),
  (3, [t32, t85, t120, t209, t249, t252, t285], []),
  (3, [t45, t85, t120, t169, t209, t249, t285], []),
  (3, [t65, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t197, t209, t249, t285], [6200429, 6200877]),
  (3, [t85, t114, t169, t209, t249, t281, t285], []),
  (3, [t85, t120, t169, t187, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t259, t285], [8600673]),
  (3, [t85, t120, t186, t209, t249, t281, t285], []),
  (3, [t54, t101, t120, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t258], [7800959, 1400815]),
  (3, [t85, t108, t139, t169, t209, t285], [7001041]),
  (3, [t120, t136, t209, t221, t249], [])]

def fam59 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t54, t120, t169, t209, t285], [9100096, 5100032]),
  (2, [t44, t85, t96, t209, t285], [7400160]),
  (3, [t13, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t85, t108, t120, t169, t249, t285], [7900380]),
  (3, [t32, t85, t120, t209, t249, t261, t285], []),
  (3, [t47, t85, t96, t120, t209, t249, t285], []),
  (3, [t66, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t200, t209, t249, t285], [5400445]),
  (3, [t85, t115, t120, t186, t209, t249, t285], []),
  (3, [t85, t120, t169, t189, t209, t249, t285], [3400545]),
  (3, [t85, t120, t169, t209, t249, t260, t285], [8600673]),
  (3, [t85, t120, t186, t209, t249, t285, t296], []),
  (3, [t54, t108, t120, t186, t209, t285], []),
  (3, [t85, t96, t120, t209, t249, t294], []),
  (3, [t85, t108, t142, t169, t209, t285], [7001041]),
  (3, [t120, t136, t209, t249, t258], [])]

def fam60 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t85, t96, t120, t209, t285], [9400112, 600268]),
  (2, [t47, t85, t108, t209, t285], [9400160]),
  (3, [t14, t16, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t115, t120, t169, t249, t285], []),
  (3, [t32, t85, t120, t209, t249, t268, t285], []),
  (3, [t47, t85, t120, t169, t209, t249, t285], []),
  (3, [t67, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t204, t209, t249, t285], [5400461]),
  (3, [t85, t116, t120, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t190, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t263, t285], [1400433, 1400561]),
  (3, [t85, t120, t186, t209, t249, t285, t302], []),
  (3, [t54, t108, t152, t169, t209, t285], []),
  (3, [t85, t96, t120, t209, t249, t297], []),
  (3, [t85, t108, t148, t169, t209, t285], []),
  (3, [t120, t136, t223, t249, t285], [])]

def fam61 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t16, t85, t120, t186, t209, t285], [9600144]),
  (2, [t54, t96, t108, t209, t285], [600160]),
  (3, [t14, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t85, t120, t123, t169, t249, t285], [400444, 9900396]),
  (3, [t32, t85, t120, t209, t249, t274, t285], []),
  (3, [t49, t54, t120, t169, t209, t249, t285], [4300780, 6300812]),
  (3, [t68, t85, t96, t120, t209, t249, t285], [3800465, 1400029]),
  (3, [t85, t96, t120, t209, t224, t249, t285], [8800687, 2400477, 7400893]),
  (3, [t85, t117, t120, t169, t209, t249, t285], [200112, 3800350]),
  (3, [t85, t120, t169, t191, t197, t209, t285], []),
  (3, [t85, t120, t169, t209, t249, t264, t285], [7400449]),
  (3, [t85, t120, t186, t209, t249, t285, t306], [4600865]),
  (3, [t54, t120, t129, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t298], []),
  (3, [t85, t108, t149, t152, t169, t209], [])]

def fam62 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t24, t32, t85, t120, t249, t285], [3100064, 3100048]),
  (2, [t85, t101, t108, t209, t285], [6001025]),
  (3, [t15, t16, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t152, t169, t249, t285], [3300460, 6300476]),
  (3, [t32, t85, t120, t209, t249, t281, t285], []),
  (3, [t49, t85, t120, t169, t209, t249, t285], [5800796, 7800828]),
  (3, [t68, t85, t108, t120, t169, t209, t285], [6600878, 3400029]),
  (3, [t85, t96, t120, t209, t226, t249, t285], [9800493]),
  (3, [t85, t118, t120, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t191, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t265, t285], []),
  (3, [t85, t120, t186, t209, t249, t285, t307], []),
  (3, [t54, t120, t136, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t304], []),
  (3, [t85, t108, t151, t169, t209, t285], [])]

def fam63 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t24, t43, t85, t169, t249, t285], [9900080, 8700048]),
  (2, [t85, t108, t129, t209, t285], [6001025]),
  (3, [t15, t85, t120, t169, t209, t249, t285], []),
  (3, [t24, t85, t120, t155, t169, t249, t285], [1100508]),
  (3, [t32, t85, t120, t209, t249, t285, t288], []),
  (3, [t50, t54, t85, t120, t209, t249, t285], [2100289]),
  (3, [t68, t85, t120, t186, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t233, t249, t285], [200525, 200909]),
  (3, [t85, t119, t120, t169, t209, t249, t285], [6200128, 1800813]),
  (3, [t85, t120, t169, t192, t209, t249, t285], [1400561, 7400609]),
  (3, [t85, t120, t169, t209, t249, t266, t285], [5400657]),
  (3, [t85, t120, t186, t209, t249, t285, t310], []),
  (3, [t54, t120, t138, t169, t249, t285], []),
  (3, [t85, t96, t120, t209, t253, t285], [7400160]),
  (3, [t85, t108, t152, t186, t209, t285], [6001025])]

def fam64 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t24, t54, t120, t169, t249, t285], [9100096, 5100048, 1200316, 7200332]),
  (2, [t85, t108, t136, t209, t285], [9600863, 4400879, 7400735]),
  (3, [t16, t43, t85, t120, t169, t209, t285], [2500193, 2000268]),
  (3, [t24, t85, t120, t160, t169, t249, t285], []),
  (3, [t32, t85, t120, t209, t249, t285, t296], []),
  (3, [t50, t54, t120, t169, t209, t249, t285], []),
  (3, [t69, t85, t120, t169, t209, t249, t285], [9000817]),
  (3, [t85, t96, t120, t209, t241, t249, t285], [1400541]),
  (3, [t85, t120, t121, t169, t209, t249, t285], []),
  (3, [t85, t120, t169, t193, t209, t249, t285], [1400433, 7400609]),
  (3, [t85, t120, t169, t209, t249, t267, t285], []),
  (3, [t85, t120, t186, t209, t249, t285, t314], []),
  (3, [t54, t120, t169, t209, t270, t285], []),
  (3, [t85, t96, t120, t209, t257, t285], []),
  (3, [t85, t109, t120, t169, t209, t285], [])]

def fam65 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t24, t85, t96, t120, t249, t285], [9400112, 3400316, 1000300, 9400012, 9300492, 9900929, 5900380, 7500348]),
  (2, [t85, t108, t138, t169, t285], []),
  (3, [t16, t54, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t164, t169, t249, t285], []),
  (3, [t32, t85, t120, t209, t249, t285, t302], []),
  (3, [t50, t85, t120, t169, t209, t249, t285], []),
  (3, [t70, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t244, t249, t285], [5400557]),
  (3, [t85, t120, t122, t169, t209, t249, t285], [3900062, 6200128]),
  (3, [t85, t120, t169, t194, t209, t249, t285], []),
  (3, [t85, t120, t169, t209, t249, t269, t285], []),
  (3, [t85, t152, t169, t209, t233, t249, t285], [1800881]),
  (3, [t60, t85, t96, t108, t209, t285], []),
  (3, [t85, t96, t120, t209, t260, t285], []),
  (3, [t85, t110, t120, t169, t209, t285], [])]

def fam66 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t24, t85, t108, t120, t169, t285], [7400128, 1400332, 5000284, 7400028, 9400444, 3700460, 2900428, 1900929, 7900364, 9500348]),
  (2, [t85, t112, t169, t209, t285], [200767]),
  (3, [t16, t64, t85, t120, t169, t209, t285], []),
  (3, [t24, t85, t120, t169, t172, t249, t285], []),
  (3, [t32, t85, t120, t209, t249, t285, t306], []),
  (3, [t51, t54, t120, t169, t209, t249, t285], []),
  (3, [t71, t85, t120, t169, t209, t249, t285], []),
  (3, [t85, t96, t120, t209, t249, t261, t285], [8800703, 2400573, 7800765, 7400941]),
  (3, [t85, t120, t123, t169, t209, t249, t285], [7900766, 7400110]),
  (3, [t85, t120, t169, t195, t209, t249, t285], [7400593]),
  (3, [t85, t120, t169, t209, t249, t270, t285], [2600577]),
  (3, [t85, t152, t169, t209, t249, t285, t302], [3800897]),
  (3, [t62, t85, t96, t108, t209, t285], []),
  (3, [t85, t96, t120, t209, t262, t285], []),
  (3, [t85, t112, t120, t169, t209, t285], [])]

def chunk0 : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19]

def chunk1 : List (List (ℕ × List ℕ × List ℕ)) := [fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39]

def chunk2 : List (List (ℕ × List ℕ × List ℕ)) := [fam40, fam41, fam42, fam43, fam44, fam45, fam46, fam47, fam48, fam49, fam50, fam51, fam52, fam53, fam54, fam55, fam56, fam57, fam58, fam59]

def chunk3 : List (List (ℕ × List ℕ × List ℕ)) := [fam60, fam61, fam62, fam63, fam64, fam65, fam66]

def parts : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14, fam15, fam16, fam17, fam18, fam19,
  fam20, fam21, fam22, fam23, fam24, fam25, fam26, fam27, fam28, fam29, fam30, fam31, fam32, fam33, fam34, fam35, fam36, fam37, fam38, fam39,
  fam40, fam41, fam42, fam43, fam44, fam45, fam46, fam47, fam48, fam49, fam50, fam51, fam52, fam53, fam54, fam55, fam56, fam57, fam58, fam59,
  fam60, fam61, fam62, fam63, fam64, fam65, fam66]

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
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok60 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok61 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok62 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok63 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok64 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok65 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok66 e he)

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
  ⟨(0, base, [2100096, 5100256, 9300080, 6900240, 8100064, 4100224, 8100048, 4100208, 8100032, 4100192, 8100016, 4100176, 7400272, 2000416, 2600288, 3600144, 9600480, 2600304, 9600544, 2600320, 9600608, 2600336, 9600672, 200112, 6200352, 4200496, 8200368, 2200560, 6200128, 2200384, 8200624, 200400, 200688, 600432, 2600576, 600448, 2600640, 600464, 2600704, 600512, 2600656, 600528, 2600720, 600592, 2600736]), by decide +kernel, rfl, rfl⟩

theorem base_len : base.length = 6 := by decide +kernel

theorem base_nd : base.Nodup := by decide +kernel

theorem tab_eq : ∀ p : Fin 64, (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3939035648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) (fun i : Fin 6 => p.val.testBit i.val) =
    tab.testBit p.val := by
  decide +kernel

def upper : Circuit :=
  ⟨[⟨GateOp.and, [1, 4]⟩,
   ⟨GateOp.and, [3, 6]⟩,
   ⟨GateOp.or, [3, 6]⟩,
   ⟨GateOp.or, [0, 7]⟩,
   ⟨GateOp.and, [1, 2]⟩,
   ⟨GateOp.or, [0, 10]⟩,
   ⟨GateOp.and, [8, 11]⟩,
   ⟨GateOp.and, [5, 9]⟩,
   ⟨GateOp.or, [12, 13]⟩], 14⟩

theorem upper_mono : Monotone2 upper := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_size : upper.size = 9 := rfl

theorem upper_eval : ∀ x : Fin 6 → Bool, upper.eval (List.ofFn x) =
    Nat.testBit (4008372906 * 2 ^ 32 + 3939035648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_16389

theorem PEqualNP.Outside.L_meta_16389 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3939035648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3939035648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro t ⟨C, hC, hs, hev⟩
  have h := PEqualNP.Outside.L_meta_16389.lower PEqualNP.Outside.L_meta_16389.tab 6 4 PEqualNP.Outside.L_meta_16389.parts PEqualNP.Outside.L_meta_16389.perms PEqualNP.Outside.L_meta_16389.zs PEqualNP.Outside.L_meta_16389.base PEqualNP.Outside.L_meta_16389.tab_lt
    PEqualNP.Outside.L_meta_16389.tab_one PEqualNP.Outside.L_meta_16389.tab_zero PEqualNP.Outside.L_meta_16389.zs_ok PEqualNP.Outside.L_meta_16389.perms_ok PEqualNP.Outside.L_meta_16389.ok PEqualNP.Outside.L_meta_16389.pool_eq
    PEqualNP.Outside.L_meta_16389.nec PEqualNP.Outside.L_meta_16389.base_mem PEqualNP.Outside.L_meta_16389.base_len PEqualNP.Outside.L_meta_16389.base_nd
    C hC (fun p => (hev _).trans (PEqualNP.Outside.L_meta_16389.tab_eq p))
  have hs' : C.gates.length ≤ t := hs
  have hu : PEqualNP.Outside.L_meta_16389.upper.size = 9 := PEqualNP.Outside.L_meta_16389.upper_size
  exact ⟨PEqualNP.Outside.L_meta_16389.upper, PEqualNP.Outside.L_meta_16389.upper_mono, by omega, PEqualNP.Outside.L_meta_16389.upper_eval⟩
