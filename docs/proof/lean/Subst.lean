/-
  Formalization of Section 2 of "String Substitution Theory for Finite Charset"
  (../main.tex).

  * `subst A B C` is the paper's `[A/B]C` (Definition 1): scan `C` from the
    left and replace every occurrence of the block `B` by `A`, taking
    leftmost-first, non-overlapping matches; the scan never restarts inside
    inserted text.  The paper leaves `[A/ε]` undefined; here the empty block
    never matches, so `subst A []` is the identity.
  * Composition is right-to-left, as in the paper:
    `subst A B (subst C D E)` is `[A/B][C/D]E`.

  Status: every theorem of Section 2 is proven, including `repC2_correct`
  (the paper's Theorem (Multiple Substitution): the unrestricted comma-code
  construction, no hypothesis on the patterns beyond `X_i ≠ ε` and
  everything over `σ`).  For the comma code the *code layer* is proven:
  `enc2Pass_eq` (the pass composition computes the block map) and
  `dec2Pass_enc2` (the decode round trip); the phase-locking staging
  argument is the content of `repC2_correct`'s proof (via `renLoop`/
  `insLoop`/`markRounds`/`assemble`).  `repC` is an
  enc-based variant of the construction, which computes `repRef` only under
  the condition that every `X_i` is a single character or does not end in
  `x` (a statement not proven here); it is kept as a demo of the shadowing
  failure.  (Theorem (escaping) is `repC2` on special pair sets; not
  formalized.)  Also proven along the way: the Double Substitution Lemma,
  cat, benc/bdec border coding, eq, ite, head, and tail (the last two need
  `X ⊆ Σ`, as the paper assumes `Σ = {σ₁..σ_N}` throughout).

  Build: `lake build`.  Quick iteration: `lake env lean Subst.lean`.
-/

variable {α : Type} [DecidableEq α]

/-! ## Definition 1: substitution -/

/-- `matchHere B C`: does `C` begin with the block `B`?
    If so, return the rest of `C`, else `none`. -/
def matchHere : List α → List α → Option (List α)
  | [], C => some C
  | _, [] => none
  | b :: B', c :: C' => if b = c then matchHere B' C' else none

theorem matchHere_length : ∀ B C D : List α,
    matchHere B C = some D → D.length + B.length ≤ C.length := by
  intro B
  induction B with
  | nil =>
      intro C D h
      simp only [matchHere] at h
      injection h with h'
      subst h'
      simp only [List.length_nil]
      omega
  | cons b B' ih =>
      intro C D h
      cases C with
      | nil => simp [matchHere] at h
      | cons c C' =>
          by_cases hbc : b = c
          · subst hbc
            simp [matchHere] at h
            have hlen := ih C' D h
            simp only [List.length_cons] at hlen ⊢
            omega
          · simp [matchHere, hbc] at h

/-- The scan of Definition 1, for a nonempty pattern. -/
def substNE (A B : List α) (hB : B ≠ []) : List α → List α
  | [] => []
  | c :: C =>
      match _h : matchHere B (c :: C) with
      | some D => A ++ substNE A B hB D
      | none => c :: substNE A B hB C
termination_by T => T.length
decreasing_by
  · have hlen := matchHere_length B (c :: C) D _h
    have hBpos : 1 ≤ B.length := by
      cases B with
      | nil => exact absurd rfl hB
      | cons _ _ => simp
    omega
  · simp only [List.length_cons]
    omega

/-- Definition 1: `[A/B]C`.  The empty pattern never matches. -/
def subst (A B C : List α) : List α :=
  match B with
  | [] => C
  | b :: B' => substNE A (b :: B') (by simp) C

theorem subst_nil_pattern (A C : List α) : subst A [] C = C := rfl

theorem subst_cons_pattern (A : List α) (b : α) (B' C : List α) :
    subst A (b :: B') C = substNE A (b :: B') (by simp) C := rfl

theorem substNE_nil (A B : List α) (hB : B ≠ []) : substNE A B hB [] = [] := by
  rw [substNE.eq_1]

theorem substNE_cons_match (A B : List α) (hB : B ≠ []) (c : α) (C D : List α)
    (h : matchHere B (c :: C) = some D) :
    substNE A B hB (c :: C) = A ++ substNE A B hB D := by
  rw [substNE.eq_2, h]

theorem substNE_cons_none (A B : List α) (hB : B ≠ []) (c : α) (C : List α)
    (h : matchHere B (c :: C) = none) :
    substNE A B hB (c :: C) = c :: substNE A B hB C := by
  rw [substNE.eq_2, h]

theorem subst_nil (A B : List α) : subst A B [] = [] := by
  cases B with
  | nil => rfl
  | cons b B' => rw [subst_cons_pattern, substNE_nil]

theorem subst_cons_match (A B : List α) (hB : B ≠ []) (c : α) (C D : List α)
    (h : matchHere B (c :: C) = some D) :
    subst A B (c :: C) = A ++ subst A B D := by
  cases B with
  | nil => exact absurd rfl hB
  | cons b B' =>
      rw [subst_cons_pattern, substNE_cons_match _ _ _ _ _ _ h, subst_cons_pattern]

theorem subst_cons_none (A B : List α) (c : α) (C : List α)
    (h : matchHere B (c :: C) = none) :
    subst A B (c :: C) = c :: subst A B C := by
  cases B with
  | nil => rfl
  | cons b B' => rw [subst_cons_pattern, substNE_cons_none _ _ _ _ _ h, subst_cons_pattern]

/-! ### Definition 1, on instances -/

#eval subst ['a', 'b'] ['b'] ['b']                -- [a, b]   ([ab/b]b = ab)
#eval subst ['a', 'b'] ['b'] ['a', 'b']           -- [a, a, b]
#eval subst ['a'] ['a'] ['a', 'a']                -- [a, a]   ([a/a]aa = aa)
#eval subst ['x', 'y'] ['x'] ['y', 'x']           -- [y, x, y] (no restart in inserted text)
#eval subst ['a', 'a'] ['a', 'b', 'a'] ['a', 'b', 'a']  -- [a, a]
#eval subst [] ['a'] ['b', 'a', 'a']              -- [b]      (deletion: A = ε)

/-! ## Theorem 2.2: enc and dec -/

/-- `enc b x = [xb/b]`: escape every `b` into `xb`. -/
def enc (b x : α) (S : List α) : List α := subst [x, b] [b] S

/-- `dec b x = [b/xb]`: the inverse of `enc b x`. -/
def dec (b x : α) (S : List α) : List α := subst [b] [x, b] S

theorem matchHere_one_self (b : α) (S : List α) : matchHere [b] (b :: S) = some S := by
  simp [matchHere]

theorem matchHere_one_ne (b c : α) (S : List α) (h : c ≠ b) :
    matchHere [b] (c :: S) = none := by
  simp [matchHere, Ne.symm h]

theorem matchHere_two_self (x b : α) (T : List α) :
    matchHere [x, b] (x :: b :: T) = some T := by
  simp [matchHere]

theorem matchHere_two_ne (x b c : α) (T : List α) (h : c ≠ x) :
    matchHere [x, b] (c :: T) = none := by
  simp [matchHere, Ne.symm h]

theorem matchHere_two_head (x b : α) (T : List α) (h : matchHere [b] T = none) :
    matchHere [x, b] (x :: T) = none := by
  simp [matchHere, h]

theorem enc_nil (b x : α) : enc b x [] = [] := by rw [enc, subst_nil]

theorem dec_nil (b x : α) : dec b x [] = [] := by rw [dec, subst_nil]

theorem enc_cons_b (b x : α) (S : List α) : enc b x (b :: S) = x :: b :: enc b x S := by
  show subst [x, b] [b] (b :: S) = x :: b :: subst [x, b] [b] S
  rw [subst_cons_match _ _ (by simp) _ _ _ (matchHere_one_self b S)]
  simp only [List.cons_append, List.nil_append]

theorem enc_cons_ne (b x : α) (c : α) (S : List α) (h : c ≠ b) :
    enc b x (c :: S) = c :: enc b x S := by
  show subst [x, b] [b] (c :: S) = c :: subst [x, b] [b] S
  rw [subst_cons_none _ _ _ _ (matchHere_one_ne b c S h)]

theorem dec_cons_xb (b x : α) (T : List α) :
    dec b x (x :: b :: T) = b :: dec b x T := by
  show subst [b] [x, b] (x :: b :: T) = b :: subst [b] [x, b] T
  rw [subst_cons_match _ _ (by simp) _ _ _ (matchHere_two_self x b T)]
  simp only [List.cons_append, List.nil_append]

theorem dec_cons_ne (b x : α) (c : α) (T : List α) (h : c ≠ x) :
    dec b x (c :: T) = c :: dec b x T := by
  show subst [b] [x, b] (c :: T) = c :: subst [b] [x, b] T
  rw [subst_cons_none _ _ _ _ (matchHere_two_ne x b c T h)]

theorem dec_cons_x_ne (b x : α) (T : List α) (h : matchHere [x, b] (x :: T) = none) :
    dec b x (x :: T) = x :: dec b x T := by
  show subst [b] [x, b] (x :: T) = x :: subst [b] [x, b] T
  rw [subst_cons_none _ _ _ _ h]

/-- Theorem 2.2 (F2): an `enc`-image never begins with `b`. -/
theorem enc_not_startsWith_b (b x : α) (hxb : x ≠ b) (S : List α) :
    matchHere [b] (enc b x S) = none := by
  cases S with
  | nil => rw [enc, subst_nil]; rfl
  | cons c S =>
      by_cases hcb : c = b
      · rw [hcb, enc_cons_b]
        exact matchHere_one_ne _ _ _ hxb
      · rw [enc_cons_ne _ _ _ _ hcb]
        exact matchHere_one_ne _ _ _ hcb

/-- Theorem 2.2 (i), first half: `dec ∘ enc = id` (the round trip). -/
theorem dec_enc (b x : α) (hxb : x ≠ b) : ∀ S : List α, dec b x (enc b x S) = S := by
  intro S
  induction S with
  | nil => rw [enc, subst_nil, dec, subst_nil]
  | cons c S ih =>
      by_cases hcb : c = b
      · subst hcb
        rw [enc_cons_b, dec_cons_xb, ih]
      · by_cases hcx : c = x
        · rw [hcx, enc_cons_ne b x x S hxb,
              dec_cons_x_ne b x (enc b x S)
                (matchHere_two_head x b (enc b x S) (enc_not_startsWith_b b x hxb S)), ih]
        · rw [enc_cons_ne b x c S hcb, dec_cons_ne b x c (enc b x S) hcx, ih]

/-- Theorem 2.2 (i), second half: `enc` is a monoid morphism. -/
theorem enc_append (b x : α) (S T : List α) :
    enc b x (S ++ T) = enc b x S ++ enc b x T := by
  induction S with
  | nil =>
      show enc b x ([] ++ T) = enc b x [] ++ enc b x T
      rw [enc_nil]
      rfl
  | cons c S ih =>
      by_cases hcb : c = b
      · subst hcb
        rw [List.cons_append, enc_cons_b, enc_cons_b, ih]
        simp only [List.cons_append]
      · rw [List.cons_append, enc_cons_ne b x c (S ++ T) hcb, enc_cons_ne b x c S hcb, ih]
        rfl

/-! ### Occurrence and the no-`bb` invariant -/

/-- `Occ p l`: `p` occurs in `l` as a contiguous block (the paper's `p ⊂ l`). -/
def Occ (p l : List α) : Prop := ∃ u v, l = u ++ p ++ v

omit [DecidableEq α] in
theorem occ_cons_inv {p : List α} {c : α} {l : List α} (h : Occ p (c :: l)) :
    Occ p l ∨ ∃ v, c :: l = p ++ v := by
  obtain ⟨u, v, hv⟩ := h
  cases u with
  | nil => exact Or.inr ⟨v, hv⟩
  | cons d u =>
      rw [List.cons_append] at hv
      injection hv with _ h2
      exact Or.inl ⟨u, v, h2⟩

/-- Theorem 2.2 (ii) / (F1): an `enc`-image contains no `bb`. -/
theorem no_bb (b x : α) (hxb : x ≠ b) : ∀ S : List α, ¬ Occ [b, b] (enc b x S) := by
  intro S
  induction S with
  | nil => intro ⟨u, v, hv⟩; rw [enc_nil] at hv; simp at hv
  | cons c S ih =>
      by_cases hcb : c = b
      · subst hcb
        intro h
        rw [enc_cons_b] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
          · exact ih h2
          · rw [List.cons_append] at hv'
            injection hv' with _ henc
            exfalso
            have H := enc_not_startsWith_b _ _ hxb S
            rw [henc] at H
            simp only [List.cons_append, List.nil_append] at H
            simp [matchHere] at H
        · rw [List.cons_append] at hv
          injection hv with hx _
          exact hxb hx
      · intro h
        rw [enc_cons_ne b x c S hcb] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · exact ih h1
        · rw [List.cons_append] at hv
          injection hv with hc _
          exact hcb hc

#eval enc 'b' 'x' ['a', 'b', 'a', 'c']                       -- [a, x, b, a, c]
#eval dec 'b' 'x' (enc 'b' 'x' ['a', 'b', 'a', 'c'])          -- [a, b, a, c]
#eval enc 'b' 'x' "abacb".toList ++ enc 'b' 'x' "ba".toList   -- morphism: enc S ++ enc T
#eval enc 'b' 'x' ("abacb" ++ "ba").toList                    -- ... equals enc (S ++ T)

/-! ### Scan and occurrence toolkit -/

theorem matchHere_self (B : List α) : matchHere B B = some [] := by
  induction B with
  | nil => rfl
  | cons b B' ih => simp [matchHere, ih]

theorem matchHere_prefix (B D : List α) : matchHere B (B ++ D) = some D := by
  induction B generalizing D with
  | nil => rfl
  | cons b B' ih => rw [List.cons_append]; simp [matchHere, ih]

theorem matchHere_app : ∀ (B C D : List α), matchHere B C = some D → C = B ++ D := by
  intro B
  induction B with
  | nil =>
      intro C D h
      simp only [matchHere] at h
      injection h with _h
  | cons b B' ih =>
      intro C D h
      cases C with
      | nil => simp [matchHere] at h
      | cons c C' =>
          by_cases hbc : b = c
          · subst hbc
            simp [matchHere] at h
            exact congrArg (b :: ·) (ih C' D h)
          · simp [matchHere, hbc] at h

theorem matchHere_occ {B C D : List α} (h : matchHere B C = some D) : Occ B C :=
  ⟨[], D, by rw [List.nil_append]; exact matchHere_app B C D h⟩

omit [DecidableEq α] in
theorem occ_cons {p : List α} {c : α} {l : List α} (h : Occ p l) : Occ p (c :: l) := by
  obtain ⟨u, v, hv⟩ := h
  exact ⟨c :: u, v, by rw [List.cons_append]; exact congrArg (c :: ·) hv⟩

omit [DecidableEq α] in
theorem occ_left {p q : List α} {l : List α} (h : Occ (p ++ q) l) : Occ p l := by
  obtain ⟨u, v, hv⟩ := h
  refine ⟨u, q ++ v, ?_⟩
  rw [hv]
  simp [List.append_assoc]

omit [DecidableEq α] in
theorem occ_length {p l : List α} (h : Occ p l) : p.length ≤ l.length := by
  obtain ⟨u, v, hv⟩ := h
  rw [hv, List.length_append, List.length_append]
  omega

omit [DecidableEq α] in
theorem occ_single {c : α} {l : List α} : Occ [c] l ↔ c ∈ l := by
  constructor
  · rintro ⟨u, v, hv⟩
    rw [hv]
    simp [List.mem_append]
  · intro h
    induction l with
    | nil => cases h
    | cons d l' ih =>
        rcases List.mem_cons.1 h with h' | h'
        · exact ⟨[], l', by simp [h']⟩
        · exact occ_cons (ih h')

omit [DecidableEq α] in
theorem append_left_cancel : ∀ (a l r : List α), a ++ l = a ++ r → l = r := by
  intro a
  induction a with
  | nil => intro l r h; simpa using h
  | cons c a' ih =>
      intro l r h
      rw [List.cons_append, List.cons_append] at h
      injection h with _ h'
      exact ih l r h'

/-- If `B` does not occur in `C` at all, `[A/B]C = C`. -/
theorem subst_no_occ (A B : List α) : ∀ (C : List α), ¬ Occ B C → subst A B C = C := by
  intro C
  induction C with
  | nil => intro _; exact subst_nil A B
  | cons c C' ih =>
      intro h
      have hC' : ¬ Occ B C' := fun hc => h (occ_cons hc)
      cases B with
      | nil => rfl
      | cons b B' =>
          cases hm : matchHere (b :: B') (c :: C') with
          | none =>
              rw [subst_cons_none _ _ _ _ hm]
              exact congrArg (c :: ·) (ih hC')
          | some D =>
              rw [subst_cons_match _ _ (by simp) _ _ _ hm]
              exact absurd (matchHere_occ hm) h

/-- If the only occurrences of `B` in `C ++ B` end at the end, then
`[A/B](C ++ B) = C ++ A`: the scan passes through `C` and replaces the
final occurrence. -/
theorem subst_suffix_unique (A B : List α) (hB : B ≠ []) : ∀ C : List α,
    (∀ u v, C ++ B = u ++ B ++ v → v = []) → subst A B (C ++ B) = C ++ A := by
  intro C
  induction C with
  | nil =>
      intro _
      cases B with
      | nil => exact absurd rfl hB
      | cons b B' =>
          show subst A (b :: B') (b :: B') = A
          rw [subst_cons_match A (b :: B') hB b B' [] (matchHere_self (b :: B')),
              subst_nil, List.append_nil]
  | cons c C' ih =>
      intro h
      have hC' : ∀ u v, C' ++ B = u ++ B ++ v → v = [] := by
        intro u v hv
        exact h (c :: u) v (by rw [List.cons_append, hv, List.cons_append,
          List.cons_append])
      rw [List.cons_append]
      cases hm : matchHere B (c :: (C' ++ B)) with
      | none =>
          rw [subst_cons_none _ _ _ _ hm]
          exact congrArg (c :: ·) (ih hC')
      | some D =>
          rw [subst_cons_match _ _ hB _ _ _ hm]
          have hD : D = [] := h [] D (by
            rw [List.nil_append]
            exact matchHere_app B (c :: (C' ++ B)) D hm)
          have heq : c :: (C' ++ B) = B ++ D := matchHere_app B _ _ hm
          rw [hD, List.append_nil] at heq
          have hl := congrArg List.length heq
          rw [List.length_cons, List.length_append] at hl
          omega

theorem matchHere_none_ne_cons {b : α} {L : List α} (w : List α)
    (h : matchHere [b] L = none) : L ≠ b :: w := by
  intro he
  rw [he] at h
  simp [matchHere] at h

/-- An `enc`-image followed by the marker `xb²` never begins with `b`. -/
theorem enc_app_head (b x : α) (hxb : x ≠ b) (S : List α) :
    matchHere [b] (enc b x S ++ [x, b, b]) = none := by
  cases hS : enc b x S with
  | nil =>
      have hb : b ≠ x := Ne.symm hxb
      simp [List.nil_append, matchHere, hb]
  | cons d T =>
      have hne : b ≠ d := by
        intro hbd
        have h2 := enc_not_startsWith_b b x hxb S
        rw [hS] at h2
        simp [matchHere, hbd] at h2
      simp [matchHere, List.cons_append, hne]

/-- The marker `xb^k`. -/
def marker (x b : α) (k : Nat) : List α := x :: List.replicate k b

/-- The marker `xb²` does not occur inside any `enc`-image. -/
theorem no_marker_occ (b x : α) (hxb : x ≠ b) : ∀ S : List α,
    ¬ Occ [x, b, b] (enc b x S) := by
  intro S
  induction S with
  | nil =>
      intro ⟨u, v, hv⟩
      rw [enc_nil] at hv
      cases u with
      | nil => simp at hv
      | cons a u' => simp at hv
  | cons c S' ih =>
      intro h
      by_cases hcb : c = b
      · subst hcb
        rw [enc_cons_b] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
          · exact ih h2
          · rw [List.cons_append] at hv'
            injection hv' with hd _
            exact hxb hd.symm
        · rw [List.cons_append] at hv
          injection hv with _ h1
          rw [List.cons_append] at h1
          injection h1 with _ henc
          exact matchHere_none_ne_cons v (enc_not_startsWith_b _ x hxb S') henc
      · rw [enc_cons_ne b x c S' hcb] at h
        rcases occ_cons_inv h with h1 | ⟨v, hv⟩
        · exact ih h1
        · rw [List.cons_append] at hv
          injection hv with _ henc
          exact matchHere_none_ne_cons ([b] ++ v) (enc_not_startsWith_b b x hxb S') henc

/-- The only occurrence of the marker `xb²` in `enc Z ++ xb²` is the final one. -/
theorem m2_suffix_unique (b x : α) (hxb : x ≠ b) : ∀ (Z u v : List α),
    enc b x Z ++ [x, b, b] = u ++ [x, b, b] ++ v → u = enc b x Z ∧ v = [] := by
  intro Z
  induction Z with
  | nil =>
      intro u v hv
      rw [enc_nil, List.nil_append] at hv
      have hl := congrArg List.length hv
      simp only [List.length_append] at hl
      have hu : u = [] := by
        cases u with
        | nil => rfl
        | cons a u' => exfalso; simp only [List.length_cons] at hl; omega
      have hv' : v = [] := by
        cases v with
        | nil => rfl
        | cons a v' => exfalso; simp only [List.length_cons] at hl; omega
      exact ⟨by rw [enc_nil]; exact hu, hv'⟩
  | cons c Z' ih =>
      intro u v hv
      by_cases hcb : c = b
      · subst hcb
        rw [enc_cons_b, List.cons_append, List.cons_append] at hv
        cases u with
        | nil =>
            rw [List.nil_append, List.cons_append, List.cons_append, List.cons_append,
                List.nil_append] at hv
            injection hv with _ h1
            injection h1 with _ h2
            exact ((matchHere_none_ne_cons v (enc_app_head _ x hxb Z')) h2).elim
        | cons a u' =>
            rw [List.cons_append, List.cons_append] at hv
            injection hv with ha h1
            subst ha
            cases u' with
            | nil =>
                rw [List.nil_append, List.cons_append] at h1
                injection h1 with hb' _
                exact (hxb hb'.symm).elim
            | cons a₂ u₂ =>
                rw [List.cons_append, List.cons_append] at h1
                injection h1 with ha₂ h2
                subst ha₂
                refine ⟨?_, (ih u₂ v h2).2⟩
                rw [enc_cons_b, (ih u₂ v h2).1]
      · rw [enc_cons_ne b x c Z' hcb, List.cons_append] at hv
        cases u with
        | nil =>
            rw [List.nil_append, List.cons_append] at hv
            injection hv with _ h1
            exact ((matchHere_none_ne_cons ([b] ++ v) (enc_app_head b x hxb Z')) h1).elim
        | cons a u' =>
            rw [List.cons_append, List.cons_append] at hv
            injection hv with ha h1
            subst ha
            refine ⟨?_, (ih u' v h1).2⟩
            rw [enc_cons_ne b x c Z' hcb, (ih u' v h1).1]

/-! ## Lemma (Double Substitution) -/

/-- `W ⊏ Y`: `W` is a prefix of `Y`. -/
def IsPref (W Y : List α) : Prop := ∃ T, Y = W ++ T

/-- `W ⊐ Y`: `W` is a suffix of `Y`. -/
def IsSuff (W Y : List α) : Prop := ∃ T, Y = T ++ W

/-- `Y` is unbordered: no `W` other than `ε` and `Y` itself is both a
prefix and a suffix of `Y`. -/
def Unbordered (Y : List α) : Prop :=
  ∀ W : List α, (IsPref W Y ∧ IsSuff W Y) → (W = [] ∨ W = Y)

omit [DecidableEq α] in
/-- If `u ++ S = G ++ T` and `|u| ≤ |G|`, then `G` splits right after `u`. -/
theorem pref_of : ∀ (u G S T : List α), u ++ S = G ++ T → u.length ≤ G.length →
    ∃ A, G = u ++ A ∧ S = A ++ T := by
  intro u
  induction u with
  | nil => intro G S T h _; exact ⟨G, rfl, h⟩
  | cons u₀ u' ih =>
      intro G S T h hlen
      cases G with
      | nil => simp at hlen
      | cons g₀ G' =>
          rw [List.cons_append, List.cons_append] at h
          injection h with h₀ h'
          subst h₀
          obtain ⟨A, hG, hS⟩ := ih G' S T h' (by simp only [List.length_cons] at hlen; omega)
          exact ⟨A, by rw [hG]; rfl, hS⟩

omit [DecidableEq α] in
theorem occ_trans {X Y Z : List α} (h1 : Occ X Y) (h2 : Occ Y Z) : Occ X Z := by
  obtain ⟨u, v, hv⟩ := h1
  obtain ⟨s, t, ht⟩ := h2
  refine ⟨s ++ u, v ++ t, ?_⟩
  rw [ht, hv]
  simp [List.append_assoc]

/-- The greedy scan passes through a prefix in which no occurrence of `B`
starts: every `B`-occurrence of the whole text starts at `≥ |P|`. -/
theorem subst_leftmost_pass (A B : List α) :
    ∀ (P T : List α), (∀ u v, P ++ T = u ++ B ++ v → P.length ≤ u.length) →
      subst A B (P ++ T) = P ++ subst A B T := by
  intro P
  induction P with
  | nil => intro T _; rfl
  | cons c P' ih =>
      intro T h
      have hm : matchHere B (c :: (P' ++ T)) = none := by
        cases hme : matchHere B (c :: (P' ++ T)) with
        | none => rfl
        | some D =>
            exact absurd (h [] D (matchHere_app B (c :: (P' ++ T)) D hme)) (by simp)
      rw [List.cons_append, subst_cons_none _ _ _ _ hm]
      exact congrArg (c :: ·) (ih T (fun u v huv => by
        have hh := h (c :: u) v (congrArg (c :: ·) huv)
        simp only [List.length_cons] at hh
        omega))

/-- The greedy scan fires at the first position past such a prefix. -/
theorem subst_leftmost_fire (A B : List α) (hB : B ≠ []) (P T D : List α)
    (hcond : ∀ u v, P ++ T = u ++ B ++ v → P.length ≤ u.length)
    (hm : matchHere B T = some D) :
    subst A B (P ++ T) = P ++ A ++ subst A B D := by
  rw [subst_leftmost_pass A B P T hcond]
  cases B with
  | nil => exact absurd rfl hB
  | cons b B' =>
      have hTB : T = (b :: B') ++ D := matchHere_app (b :: B') T D hm
      rw [hTB] at hm ⊢
      rw [List.cons_append]
      have hm' : matchHere (b :: B') (b :: (B' ++ D)) = some D := hm
      rw [subst_cons_match A (b :: B') hB b (B' ++ D) D hm']
      simp [List.append_assoc]

/-- Every nonempty pattern that occurs has a leftmost occurrence. -/
theorem leftmost_occ (B : List α) (hB : B ≠ []) : ∀ (Z : List α), Occ B Z →
    ∃ G T D, Z = G ++ T ∧ matchHere B T = some D ∧
      (∀ u v, Z = u ++ B ++ v → G.length ≤ u.length) := by
  intro Z
  induction Z with
  | nil =>
      intro ho
      obtain ⟨u, v, hv⟩ := ho
      cases u with
      | nil =>
          rw [List.nil_append] at hv
          cases B with
          | nil => exact absurd rfl hB
          | cons b B' => rw [List.cons_append] at hv; exact nomatch hv
      | cons u₀ u' => rw [List.cons_append, List.cons_append] at hv; exact nomatch hv
  | cons c C ih =>
      intro ho
      cases hm : matchHere B (c :: C)
      · have hC : Occ B C := by
          rcases occ_cons_inv ho with h1 | ⟨v, hv⟩
          · exact h1
          · rw [show c :: C = B ++ v from hv] at hm
            rw [matchHere_prefix B v] at hm
            simp at hm
        obtain ⟨G, T, D, hC', hmT, hmin⟩ := ih hC
        refine ⟨c :: G, T, D, by rw [hC']; rfl, hmT, ?_⟩
        intro u v huv
        cases u with
        | nil =>
            rw [show c :: C = B ++ v from huv] at hm
            rw [matchHere_prefix B v] at hm
            simp at hm
        | cons u₀ u' =>
            have hC2 : C = u' ++ B ++ v := by
              rw [List.cons_append, List.cons_append] at huv
              injection huv with _ hC2'
            have h4 := hmin u' v hC2
            simp only [List.length_cons]
            omega
      · exact ⟨[], c :: C, _, rfl, hm, fun _ _ _ => Nat.zero_le _⟩

/-- Lemma (Double Substitution): with `X ⊂ Y` and `Y` unbordered,
`[X/Y][Y/X]Z = Z`. -/
theorem double_subst_aux (X Y : List α) (hX : X ≠ []) (hY : Unbordered Y) (hXY : Occ X Y) :
    ∀ (n : Nat) (Z : List α), Z.length ≤ n → subst X Y (subst Y X Z) = Z := by
  have hYne : Y ≠ [] := by
    intro he
    obtain ⟨u, v, hv⟩ := hXY
    rw [he] at hv
    cases u with
    | nil =>
        rw [List.nil_append] at hv
        cases X with
        | nil => exact absurd rfl hX
        | cons x₀ X' => rw [List.cons_append] at hv; exact nomatch hv
    | cons u₀ u' => rw [List.cons_append, List.cons_append] at hv; exact nomatch hv
  have h1X : 1 ≤ X.length := by
    cases X with
    | nil => exact absurd rfl hX
    | cons x₀ X' => simp
  intro n
  induction n with
  | zero =>
      intro Z hZ
      cases Z with
      | nil => rw [subst_nil, subst_nil]
      | cons c C => simp at hZ
  | succ n ih =>
      intro Z hZ
      by_cases hocc : Occ X Z
      · obtain ⟨G, T, D, hZT, hmT, hmin⟩ := leftmost_occ X hX Z hocc
        have hTD : T = X ++ D := matchHere_app X T D hmT
        have hGnoX : ¬ Occ X G := by
          intro ho
          obtain ⟨a, b, hGab⟩ := ho
          have hz : Z = a ++ X ++ (b ++ T) := by rw [hZT, hGab]; simp [List.append_assoc]
          have hmin' := hmin a (b ++ T) hz
          have hlen := congrArg List.length hGab
          simp [List.length_append] at hlen
          omega
        have hYcond : ∀ u v, G ++ (Y ++ subst Y X D) = u ++ Y ++ v →
            G.length ≤ u.length := by
          intro u v huv
          by_cases hlt : u.length < G.length
          · exfalso
            simp only [List.append_assoc] at huv
            obtain ⟨A, hG, hS⟩ := pref_of u G (Y ++ v) (Y ++ subst Y X D) huv.symm
              (Nat.le_of_lt hlt)
            have hGA : G.length = u.length + A.length := by
              rw [hG]; exact List.length_append
            have hA0 : 0 < A.length := by omega
            by_cases hAB : A.length < Y.length
            · -- straddle: extract a proper border of Y
              obtain ⟨B, hY1, hS2⟩ := pref_of A Y (Y ++ subst Y X D) v hS.symm
                (Nat.le_of_lt hAB)
              have hYB : Y.length = A.length + B.length := by
                rw [hY1]; exact List.length_append
              obtain ⟨C, hY2, _⟩ := pref_of B Y v (subst Y X D) hS2.symm (by omega)
              rcases hY B ⟨⟨C, hY2⟩, ⟨A, hY1⟩⟩ with hB1 | hB2
              · rw [hB1] at hYB; simp at hYB; omega
              · rw [hB2] at hYB; omega
            · -- ends inside the gap: Y ⊂ G, hence X ⊂ G
              obtain ⟨A', hA', _⟩ := pref_of Y A v (Y ++ subst Y X D) hS (by omega)
              exact hGnoX (occ_trans hXY ⟨u, A', by
                rw [hG, hA']; exact (List.append_assoc u Y A').symm⟩)
          · omega
        have hZlen : Z.length = G.length + T.length := by
          rw [hZT]; exact List.length_append
        have hTlen : T.length = X.length + D.length := by
          rw [hTD]; exact List.length_append
        have hDlen : D.length ≤ n := by omega
        rw [hZT, subst_leftmost_fire Y X hX G T D
            (fun u v huv => hmin u v (by rw [hZT]; exact huv)) hmT,
          List.append_assoc,
          subst_leftmost_fire X Y hYne G (Y ++ subst Y X D) (subst Y X D) hYcond
            (matchHere_prefix Y (subst Y X D)),
          ih D hDlen, hTD]
        exact List.append_assoc G X D
      · have hnoY : ¬ Occ Y Z := fun ho => hocc (occ_trans hXY ho)
        rw [subst_no_occ Y X Z hocc, subst_no_occ X Y Z hnoY]

theorem double_subst {X Y : List α} (hX : X ≠ []) (hY : Unbordered Y) (hXY : Occ X Y)
    (Z : List α) : subst X Y (subst Y X Z) = Z :=
  double_subst_aux X Y hX hY hXY Z.length Z (Nat.le_refl _)

-- The unborderedness hypothesis is essential: `Y = "aba"` is bordered by `"a"`.
#eval subst ['b', 'a'] ['a', 'b', 'a'] (subst ['a', 'b', 'a'] ['b', 'a'] ['b', 'a', 'a', 'b', 'b', 'a'])
-- [b, a, b, a, b, a] ≠ "baabba"

/-! ## Theorem (cat): concatenation -/

/-- Theorem (cat): `dec([enc(Y)/xb³][enc(X)/xb²](xb²xb³))`. -/
def cat (b x : α) (X Y : List α) : List α :=
  dec b x (subst (enc b x X) (marker x b 2)
    (subst (enc b x Y) (marker x b 3) (marker x b 2 ++ marker x b 3)))

theorem cat_step1 (b x : α) (hxb : x ≠ b) (Y : List α) :
    subst (enc b x Y) (marker x b 3) (marker x b 2 ++ marker x b 3)
      = marker x b 2 ++ enc b x Y := by
  have hb : b ≠ x := Ne.symm hxb
  show subst (enc b x Y) [x, b, b, b] (x :: b :: b :: x :: b :: b :: b :: [])
      = x :: b :: b :: enc b x Y
  have h0 : matchHere [x, b, b, b] (x :: b :: b :: x :: b :: b :: b :: []) = none := by
    simp [matchHere, hb]
  rw [subst_cons_none _ _ _ _ h0]
  show x :: subst (enc b x Y) [x, b, b, b] (b :: b :: x :: b :: b :: b :: [])
      = x :: b :: b :: enc b x Y
  have h1 : matchHere [x, b, b, b] (b :: b :: x :: b :: b :: b :: []) = none := by
    simp [matchHere, hb]
  rw [subst_cons_none _ _ _ _ h1]
  show x :: b :: subst (enc b x Y) [x, b, b, b] (b :: x :: b :: b :: b :: [])
      = x :: b :: b :: enc b x Y
  have h2 : matchHere [x, b, b, b] (b :: x :: b :: b :: b :: []) = none := by
    simp [matchHere, hb]
  rw [subst_cons_none _ _ _ _ h2]
  rw [subst_cons_match _ _ (by simp) _ _ [] (matchHere_self [x, b, b, b]), subst_nil,
      List.append_nil]

theorem cat_step2 (b x : α) (hxb : x ≠ b) (X Y : List α) :
    subst (enc b x X) (marker x b 2) (marker x b 2 ++ enc b x Y)
      = enc b x X ++ enc b x Y := by
  have h1 : matchHere [x, b, b] (x :: ([b, b] ++ enc b x Y)) = some (enc b x Y) :=
    matchHere_prefix [x, b, b] (enc b x Y)
  show subst (enc b x X) [x, b, b] (x :: ([b, b] ++ enc b x Y)) = enc b x X ++ enc b x Y
  rw [subst_cons_match _ _ (by simp) _ _ _ h1]
  exact congrArg (enc b x X ++ ·) (subst_no_occ (enc b x X) [x, b, b] (enc b x Y)
    (no_marker_occ b x hxb Y))

theorem cat_correct (b x : α) (hxb : x ≠ b) (X Y : List α) :
    cat b x X Y = X ++ Y := by
  show dec b x (subst (enc b x X) (marker x b 2)
      (subst (enc b x Y) (marker x b 3) (marker x b 2 ++ marker x b 3))) = X ++ Y
  rw [cat_step1 b x hxb Y, cat_step2 b x hxb X Y, ← enc_append, dec_enc b x hxb]

#eval cat 'b' 'x' ['a', 'b'] ['c']                    -- [a, b, c]
#eval cat 'b' 'x' [] []                               -- []
#eval cat 'b' 'x' ['b', 'b', 'x'] ['x', 'x', 'b']     -- marker-poisoned input: [b, b, x, x, x, b]

/-! ## Theorem (benc round trip) and Theorem (eq) -/

/-- `enc` with marker borders. -/
def benc (b x : α) (X : List α) : List α :=
  marker x b 2 ++ enc b x X ++ marker x b 2

/-- Strip the borders. -/
def bdec (b x : α) (S : List α) : List α := subst [] (marker x b 2) S

/-- In a bordered encoding `benc(X)`, the marker `xb²` occurs only as the
two borders. -/
theorem occ_m2_benc (b x : α) (hxb : x ≠ b) (X u v : List α)
    (h : benc b x X = u ++ marker x b 2 ++ v) :
    u = [] ∨ u = marker x b 2 ++ enc b x X := by
  have hm : marker x b 2 = [x, b, b] := rfl
  rw [hm] at h ⊢
  rw [show benc b x X = x :: b :: b :: (enc b x X ++ [x, b, b]) from rfl] at h
  cases u with
  | nil => exact Or.inl rfl
  | cons a u' =>
      rw [List.cons_append, List.cons_append] at h
      injection h with ha h1
      subst ha
      cases u' with
      | nil =>
          rw [List.nil_append, List.cons_append] at h1
          injection h1 with hb' _
          exact (hxb hb'.symm).elim
      | cons a₂ u₂ =>
          rw [List.cons_append, List.cons_append] at h1
          injection h1 with ha₂ h2
          subst ha₂
          cases u₂ with
          | nil =>
              rw [List.nil_append, List.cons_append] at h2
              injection h2 with hb'' _
              exact (hxb hb''.symm).elim
          | cons a₃ u₃ =>
              rw [List.cons_append, List.cons_append] at h2
              injection h2 with ha₃ h3
              subst ha₃
              refine Or.inr ?_
              rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append,
                (m2_suffix_unique b x hxb X u₃ v h3).1]

/-- Border injectivity: if `benc(Y)` occurs in `benc(X)` then `Y = X`. -/
theorem benc_occ_inv (b x : α) (hxb : x ≠ b) (X Y : List α) :
    Occ (benc b x Y) (benc b x X) → Y = X := by
  rintro ⟨u, v, hv⟩
  have hY : benc b x Y = [x, b, b] ++ (enc b x Y ++ [x, b, b]) := rfl
  rw [hY] at hv
  have htrailing : benc b x X = (u ++ [x, b, b] ++ enc b x Y) ++ [x, b, b] ++ v := by
    rw [hv]; simp [List.append_assoc]
  have hleading : benc b x X = u ++ [x, b, b] ++ ((enc b x Y ++ [x, b, b]) ++ v) := by
    rw [hv]; simp [List.append_assoc]
  rcases occ_m2_benc b x hxb X (u ++ [x, b, b] ++ enc b x Y) v htrailing with hw1 | hw2
  · simp at hw1
  · rcases occ_m2_benc b x hxb X u ((enc b x Y ++ [x, b, b]) ++ v) hleading with hu1 | hu2
    · rw [hu1, List.nil_append] at hw2
      have henc : enc b x Y = enc b x X := append_left_cancel [x, b, b] _ _ hw2
      rw [← dec_enc b x hxb Y, henc, dec_enc b x hxb X]
    · rw [hu2] at hw2
      have hl := congrArg List.length hw2
      simp [marker, List.replicate, List.length_append] at hl

theorem bdec_benc (b x : α) (hxb : x ≠ b) (X : List α) :
    bdec b x (benc b x X) = enc b x X := by
  show subst [] [x, b, b] (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = enc b x X
  have h1 : matchHere [x, b, b] (x :: ([b, b] ++ (enc b x X ++ [x, b, b])))
      = some (enc b x X ++ [x, b, b]) :=
    matchHere_prefix [x, b, b] (enc b x X ++ [x, b, b])
  rw [subst_cons_match [] [x, b, b] (by simp) x _ _ h1, List.nil_append]
  have h2 := subst_suffix_unique [] [x, b, b] (by simp) (enc b x X)
    (fun u v hv => (m2_suffix_unique b x hxb X u v hv).2)
  rw [List.append_nil] at h2
  exact h2

/-- Theorem (eq): `[⊥/benc(X)][⊤/benc(Y)]benc(X)`. -/
def eqC (top bot b x : α) (X Y : List α) : List α :=
  subst [bot] (benc b x X) (subst [top] (benc b x Y) (benc b x X))

/-- The paper picks distinct `⊤ ≠ ⊥` merely to name the two outputs; the
proof below needs no distinctness of `⊤`, `⊥` at all. -/
theorem eqC_correct (top bot b x : α) (hxb : x ≠ b) (X Y : List α) :
    eqC top bot b x X Y = if X = Y then [top] else [bot] := by
  have h1 : subst [top] (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = [top] := by
    have hm : matchHere (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = some [] :=
      matchHere_self (benc b x X)
    rw [subst_cons_match [top] (benc b x X) (by simp [benc, marker]) x _ _ hm, subst_nil,
        List.append_nil]
  by_cases hXY : X = Y
  · subst hXY
    show subst [bot] (benc b x X)
        (subst [top] (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))))
      = (if X = X then [top] else [bot])
    rw [h1]
    have h2 : ¬ Occ (benc b x X) [top] := by
      intro ho
      have hl := occ_length ho
      simp [benc, marker, List.replicate, List.length_append] at hl
    rw [subst_no_occ [bot] (benc b x X) [top] h2]
    simp
  · have hne : ¬ Occ (benc b x Y) (benc b x X) :=
      fun ho => hXY (benc_occ_inv b x hxb X Y ho).symm
    show subst [bot] (benc b x X) (subst [top] (benc b x Y) (benc b x X))
      = (if X = Y then [top] else [bot])
    rw [subst_no_occ [top] (benc b x Y) (benc b x X) hne]
    show subst [bot] (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b])))
      = (if X = Y then [top] else [bot])
    have hm : matchHere (benc b x X) (x :: ([b, b] ++ (enc b x X ++ [x, b, b]))) = some [] :=
      matchHere_self (benc b x X)
    rw [subst_cons_match [bot] (benc b x X) (by simp [benc, marker]) x _ _ hm, subst_nil,
        List.append_nil]
    simp [hXY]

#eval eqC 't' 'f' 'b' 'x' ['a', 'b'] ['a', 'b']        -- [t]
#eval eqC 't' 'f' 'b' 'x' ['a', 'b'] ['a', 'c']        -- [f]
#eval eqC 't' 'f' 'b' 'x' [] []                        -- [t]

/-! ## Theorem (Selection, `if`) -/

/-- Theorem (Selection): `[enc(Y)/bb][enc(X)/⊤][bb/⊥]C` (rightmost first). -/
def iteC (top bot b x : α) (C X Y : List α) : List α :=
  dec b x (subst (enc b x Y) [b, b]
    (subst (enc b x X) [top] (subst [b, b] [bot] C)))

theorem iteC_correct (top bot b x : α) (hxb : x ≠ b) (htb : top ≠ b) (htop : top ≠ bot)
    (C X Y : List α) (hC : C = [top] ∨ C = [bot]) :
    iteC top bot b x C X Y = if C = [top] then X else Y := by
  rcases hC with hC | hC
  · subst hC
    have hn1 : ¬ Occ [bot] [top] := by
      intro ho
      have h := occ_single.1 ho
      simp at h
      exact htop h.symm
    have h1 : subst [b, b] [bot] [top] = [top] := subst_no_occ [b, b] [bot] [top] hn1
    have h2 : subst (enc b x X) [top] [top] = enc b x X := by
      rw [subst_cons_match (enc b x X) [top] (by simp) top _ []
            (matchHere_self [top]), subst_nil, List.append_nil]
    have h3 : subst (enc b x Y) [b, b] (enc b x X) = enc b x X :=
      subst_no_occ (enc b x Y) [b, b] (enc b x X) (no_bb b x hxb X)
    show dec b x (subst (enc b x Y) [b, b] (subst (enc b x X) [top] (subst [b, b] [bot] [top])))
      = (if [top] = [top] then X else Y)
    rw [h1, h2, h3, dec_enc b x hxb]
    simp
  · subst hC
    have h1 : subst [b, b] [bot] [bot] = [b, b] := by
      rw [subst_cons_match [b, b] [bot] (by simp) bot _ [] (matchHere_self [bot]), subst_nil,
          List.append_nil]
    have hn2 : ¬ Occ [top] [b, b] := by
      intro ho
      have h := occ_single.1 ho
      rcases List.mem_cons.1 h with h' | h'
      · exact htb h'
      · rcases List.mem_cons.1 h' with h'' | h''
        · exact htb h''
        · cases h''
    have h2 : subst (enc b x X) [top] [b, b] = [b, b] :=
      subst_no_occ (enc b x X) [top] [b, b] hn2
    have h3 : subst (enc b x Y) [b, b] [b, b] = enc b x Y := by
      rw [subst_cons_match (enc b x Y) [b, b] (by simp) b _ [] (matchHere_self [b, b]),
          subst_nil, List.append_nil]
    show dec b x (subst (enc b x Y) [b, b] (subst (enc b x X) [top] (subst [b, b] [bot] [bot])))
      = (if [bot] = [top] then X else Y)
    rw [h1, h2, h3, dec_enc b x hxb]
    have hne : ([bot] : List α) ≠ [top] := by
      intro he
      injection he with h'
      exact htop h'.symm
    simp [hne]

#eval iteC 't' 'f' 'b' 'x' ['t'] ['y', 'e', 's'] ['n', 'o']   -- [y, e, s]
#eval iteC 't' 'f' 'b' 'x' ['f'] ['y', 'e', 's'] ['n', 'o']   -- [n, o]

/-! ## Theorem (head and tail) -/

/-- The deletion cascade of `tail` for the alphabet `σ₁ :: σ₂ :: rest`. -/
def tailCascade (s1 : α) : List α → List α → List α
  | [], T => T
  | c :: cs, T => subst [] [s1, s1, c] (tailCascade s1 cs T)

/-- Theorem (tail): everything but the first character. -/
def tail (sig : List α) (X : List α) : List α :=
  match sig with
  | s1 :: s2 :: rest =>
      dec s1 s2 (subst [] [s1, s1]
        (subst [] [s1, s1, s2]
          (subst [] [s1, s1, s2, s1]
            (tailCascade s1 rest ([s1, s1] ++ enc s1 s2 X)))))
  | _ => X

/-- Theorem (head): the first character. -/
def head (sig : List α) (X : List α) : List α :=
  match sig with
  | s1 :: s2 :: _ =>
      dec s1 s2 (subst [] (enc s1 s2 (tail sig X) ++ [s1, s1])
        (enc s1 s2 X ++ [s1, s1]))
  | _ => X

/-! ### The `tail` cascade -/

/-- No pattern containing `σ₁σ₁` occurs in an `enc`-image (by (F1)). -/
theorem no_s1s1_occ (s1 s2 : α) (hs : s2 ≠ s1) (Z : List α) (c : α) :
    ¬ Occ [s1, s1, c] (enc s1 s2 Z) :=
  fun h => no_bb s1 s2 hs Z (occ_left (p := [s1, s1]) (q := [c]) h)

theorem no_s1s1s2s1_occ (s1 s2 : α) (hs : s2 ≠ s1) (Z : List α) :
    ¬ Occ [s1, s1, s2, s1] (enc s1 s2 Z) :=
  fun h => no_bb s1 s2 hs Z (occ_left (p := [s1, s1]) (q := [s2, s1]) h)

/-- `[ε/σ₁σ₁d]` is inert on `σ₁σ₁·enc(Z)` unless `Z` starts with `d`. -/
theorem no_s1s1c_pref (s1 s2 d : α) (hs : s2 ≠ s1) (hd2 : d ≠ s2)
    (Z : List α) (hZ : ∀ Z', Z ≠ d :: Z') :
    ¬ Occ [s1, s1, d] ([s1, s1] ++ enc s1 s2 Z) := by
  intro h
  rw [List.cons_append, List.cons_append, List.nil_append] at h
  rcases occ_cons_inv h with h1 | ⟨v, hv⟩
  · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
    · exact no_s1s1_occ s1 s2 hs Z d h2
    · rw [List.cons_append] at hv'
      injection hv' with _ henc
      exact matchHere_none_ne_cons ([d] ++ v') (enc_not_startsWith_b s1 s2 hs Z) henc
  · rw [List.cons_append] at hv
    injection hv with _ h1
    rw [List.cons_append] at h1
    injection h1 with _ henc
    cases Z with
    | nil => rw [enc_nil] at henc; simp at henc
    | cons z Z' =>
        by_cases hz : z = s1
        · rw [hz, enc_cons_b, List.cons_append, List.nil_append] at henc
          injection henc with hd0 _
          exact hd2 hd0.symm
        · rw [enc_cons_ne s1 s2 z Z' hz, List.cons_append, List.nil_append] at henc
          injection henc with hd0 _
          exact hZ Z' (by rw [hd0])

/-- `[ε/σ₁σ₁σ₂σ₁]` is inert on `σ₁σ₁·enc(Z)` unless `Z` starts with `σ₁`. -/
theorem no_s1s1s2s1_pref (s1 s2 : α) (hs : s2 ≠ s1) (Z : List α)
    (hZ : ∀ Z', Z ≠ s1 :: Z') :
    ¬ Occ [s1, s1, s2, s1] ([s1, s1] ++ enc s1 s2 Z) := by
  intro h
  rw [List.cons_append, List.cons_append, List.nil_append] at h
  rcases occ_cons_inv h with h1 | ⟨v, hv⟩
  · rcases occ_cons_inv h1 with h2 | ⟨v', hv'⟩
    · exact no_s1s1s2s1_occ s1 s2 hs Z h2
    · rw [List.cons_append] at hv'
      injection hv' with _ henc
      exact matchHere_none_ne_cons ([s2, s1] ++ v') (enc_not_startsWith_b s1 s2 hs Z) henc
  · rw [List.cons_append] at hv
    injection hv with _ h1
    rw [List.cons_append] at h1
    injection h1 with _ h1'
    cases Z with
    | nil => rw [enc_nil] at h1'; simp at h1'
    | cons z Z' =>
        by_cases hz : z = s1
        · exact hZ Z' (by rw [hz])
        · rw [enc_cons_ne s1 s2 z Z' hz, List.cons_append, List.cons_append,
              List.nil_append] at h1'
          injection h1' with hz2 henc'
          exact matchHere_none_ne_cons v (enc_not_startsWith_b s1 s2 hs Z') henc'

theorem subst_prefix_fire (s1 s2 d : α) (hs : s2 ≠ s1) (hd : d ≠ s1) (Z' : List α) :
    subst [] [s1, s1, d] ([s1, s1] ++ enc s1 s2 (d :: Z')) = enc s1 s2 Z' := by
  have h1 : enc s1 s2 (d :: Z') = d :: enc s1 s2 Z' := enc_cons_ne s1 s2 d Z' hd
  rw [h1]
  show subst [] [s1, s1, d] (s1 :: (s1 :: (d :: enc s1 s2 Z'))) = enc s1 s2 Z'
  have hm : matchHere [s1, s1, d] (s1 :: (s1 :: (d :: enc s1 s2 Z')))
      = some (enc s1 s2 Z') :=
    matchHere_prefix [s1, s1, d] (enc s1 s2 Z')
  rw [subst_cons_match [] [s1, s1, d] (by simp) s1 _ _ hm, List.nil_append]
  exact subst_no_occ [] [s1, s1, d] (enc s1 s2 Z') (no_s1s1_occ s1 s2 hs Z' d)

theorem subst_prefix_fire_s1 (s1 s2 : α) (hs : s2 ≠ s1) (Z' : List α) :
    subst [] [s1, s1, s2, s1] ([s1, s1] ++ enc s1 s2 (s1 :: Z')) = enc s1 s2 Z' := by
  have h1 : enc s1 s2 (s1 :: Z') = s2 :: s1 :: enc s1 s2 Z' := enc_cons_b s1 s2 Z'
  rw [h1]
  show subst [] [s1, s1, s2, s1] (s1 :: (s1 :: (s2 :: (s1 :: enc s1 s2 Z'))))
    = enc s1 s2 Z'
  have hm : matchHere [s1, s1, s2, s1] (s1 :: (s1 :: (s2 :: (s1 :: enc s1 s2 Z'))))
      = some (enc s1 s2 Z') :=
    matchHere_prefix [s1, s1, s2, s1] (enc s1 s2 Z')
  rw [subst_cons_match [] [s1, s1, s2, s1] (by simp) s1 _ _ hm, List.nil_append]
  exact subst_no_occ [] [s1, s1, s2, s1] (enc s1 s2 Z') (no_s1s1s2s1_occ s1 s2 hs Z')

/-- The deletion cascade leaves `σ₁σ₁·enc(Z)` untouched when `Z` starts with
none of its characters. -/
theorem tailCascade_inert (s1 s2 : α) (hs : s2 ≠ s1) :
    ∀ (cs Z : List α), (∀ c ∈ cs, c ≠ s1 ∧ c ≠ s2) →
      (∀ c ∈ cs, ∀ Z'', Z ≠ c :: Z'') →
      tailCascade s1 cs ([s1, s1] ++ enc s1 s2 Z) = [s1, s1] ++ enc s1 s2 Z := by
  intro cs
  induction cs with
  | nil => intro Z _ _; rfl
  | cons d cs' ih =>
      intro Z hcs hZ
      have hcs' : ∀ c ∈ cs', c ≠ s1 ∧ c ≠ s2 := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
      have hZ' : ∀ c ∈ cs', ∀ Z'', Z ≠ c :: Z'' :=
        fun c hc Z'' => hZ c (List.mem_cons_of_mem _ hc) Z''
      show subst [] [s1, s1, d] (tailCascade s1 cs' ([s1, s1] ++ enc s1 s2 Z))
        = [s1, s1] ++ enc s1 s2 Z
      rw [ih Z hcs' hZ']
      exact subst_no_occ [] [s1, s1, d] ([s1, s1] ++ enc s1 s2 Z)
        (no_s1s1c_pref s1 s2 d hs (hcs d (List.mem_cons_self ..)).2 Z
          (hZ d (List.mem_cons_self ..)))

/-- If `Z` starts with a character `d` of the cascade, the cascade deletes the
marker and `d`, leaving `enc(Z)`. -/
theorem tailCascade_fire (s1 s2 : α) (hs : s2 ≠ s1) (d : α) (hd : d ≠ s1) (Z' : List α) :
    ∀ (cs : List α), (∀ c ∈ cs, c ≠ s1 ∧ c ≠ s2) → d ∈ cs →
      tailCascade s1 cs ([s1, s1] ++ enc s1 s2 (d :: Z')) = enc s1 s2 Z' := by
  intro cs
  induction cs with
  | nil => intro _ hin; exact absurd hin (by simp)
  | cons e cs' ih =>
      intro hcs hin
      have hcs' : ∀ c ∈ cs', c ≠ s1 ∧ c ≠ s2 := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
      show subst [] [s1, s1, e] (tailCascade s1 cs' ([s1, s1] ++ enc s1 s2 (d :: Z')))
        = enc s1 s2 Z'
      rcases List.mem_cons.1 hin with hde | hin'
      · subst hde
        by_cases hdIn' : d ∈ cs'
        · rw [ih hcs' hdIn']
          exact subst_no_occ [] [s1, s1, d] (enc s1 s2 Z') (no_s1s1_occ s1 s2 hs Z' d)
        · rw [tailCascade_inert s1 s2 hs cs' (d :: Z') hcs'
            (fun c hc Z'' heq => hdIn' (by injection heq with hcd _; rw [hcd]; exact hc))]
          exact subst_prefix_fire s1 s2 d hs hd Z'
      · rw [ih hcs' hin']
        exact subst_no_occ [] [s1, s1, e] (enc s1 s2 Z') (no_s1s1_occ s1 s2 hs Z' e)

theorem tail_correct (sig : List α) (hnd : sig.Pairwise (· ≠ ·)) (h2 : 2 ≤ sig.length)
    (X : List α) (hX : ∀ c ∈ X, c ∈ sig) :
    tail sig X = X.drop 1 := by
  cases sig with
  | nil => simp at h2
  | cons s1 sig' =>
      cases sig' with
      | nil => simp at h2
      | cons s2 rest =>
          rw [List.pairwise_cons] at hnd
          have hnd2 := hnd.2
          rw [List.pairwise_cons] at hnd2
          have hs : s2 ≠ s1 := fun he => hnd.1 s2 (List.mem_cons_self ..) he.symm
          have hrest : ∀ c ∈ rest, c ≠ s1 ∧ c ≠ s2 := by
            intro c hc
            exact ⟨fun he => hnd.1 c (List.mem_cons_of_mem _ hc) he.symm,
                   fun he => hnd2.1 c hc he.symm⟩
          show dec s1 s2 (subst [] [s1, s1]
            (subst [] [s1, s1, s2]
              (subst [] [s1, s1, s2, s1]
                (tailCascade s1 rest ([s1, s1] ++ enc s1 s2 X)))))
            = X.drop 1
          cases X with
          | nil =>
              rw [tailCascade_inert s1 s2 hs rest [] hrest
                (fun c _ Z'' heq => nomatch heq),
                enc_nil, List.append_nil]
              have hn4 : ¬ Occ [s1, s1, s2, s1] [s1, s1] := by
                intro ho
                have hl := occ_length ho
                simp at hl
              rw [subst_no_occ [] [s1, s1, s2, s1] [s1, s1] hn4]
              have hn3 : ¬ Occ [s1, s1, s2] [s1, s1] := by
                intro ho
                have hl := occ_length ho
                simp at hl
              rw [subst_no_occ [] [s1, s1, s2] [s1, s1] hn3,
                subst_cons_match [] [s1, s1] (by simp) s1 _ []
                  (matchHere_self [s1, s1]), subst_nil, List.nil_append, dec_nil]
              simp
          | cons c X' =>
              rcases List.mem_cons.1 (hX c (List.mem_cons_self ..)) with hc | hc
              · rw [hc, tailCascade_inert s1 s2 hs rest (s1 :: X') hrest
                  (fun c' hc' Z'' heq =>
                    (hrest c' hc').1 (by injection heq with hcd _; exact hcd.symm)),
                  subst_prefix_fire_s1 s1 s2 hs X',
                  subst_no_occ [] [s1, s1, s2] (enc s1 s2 X') (no_s1s1_occ s1 s2 hs X' s2),
                  subst_no_occ [] [s1, s1] (enc s1 s2 X') (no_bb s1 s2 hs X'),
                  dec_enc s1 s2 hs]
                simp
              · rcases List.mem_cons.1 hc with hc | hc
                · rw [hc, tailCascade_inert s1 s2 hs rest (s2 :: X') hrest
                    (fun c' hc' Z'' heq =>
                      (hrest c' hc').2 (by injection heq with hcd _; exact hcd.symm)),
                    subst_no_occ [] [s1, s1, s2, s1] ([s1, s1] ++ enc s1 s2 (s2 :: X'))
                      (no_s1s1s2s1_pref s1 s2 hs (s2 :: X')
                        (fun Z'' heq => hs (by injection heq with hcd _))),
                    subst_prefix_fire s1 s2 s2 hs hs X',
                    subst_no_occ [] [s1, s1] (enc s1 s2 X') (no_bb s1 s2 hs X'),
                    dec_enc s1 s2 hs]
                  simp
                · rw [tailCascade_fire s1 s2 hs c (hrest c hc).1 X' rest hrest hc,
                    subst_no_occ [] [s1, s1, s2, s1] (enc s1 s2 X')
                      (no_s1s1s2s1_occ s1 s2 hs X'),
                    subst_no_occ [] [s1, s1, s2] (enc s1 s2 X') (no_s1s1_occ s1 s2 hs X' s2),
                    subst_no_occ [] [s1, s1] (enc s1 s2 X') (no_bb s1 s2 hs X'),
                    dec_enc s1 s2 hs]
                  simp

/-! ### The `head` machinery -/

theorem matchHere_ne (b : α) (B' : List α) (c : α) (C : List α) (hbc : b ≠ c) :
    matchHere (b :: B') (c :: C) = none := by
  simp [matchHere, hbc]

theorem subst_self (A B : List α) (hB : B ≠ []) : subst A B B = A := by
  cases B with
  | nil => exact absurd rfl hB
  | cons b B' =>
      rw [subst_cons_match A (b :: B') hB b B' [] (matchHere_self (b :: B')), subst_nil,
        List.append_nil]

theorem dec_single (s1 s2 : α) (hs : s2 ≠ s1) (c : α) (hc : c ≠ s1) : dec s1 s2 [c] = [c] := by
  have hE : enc s1 s2 [c] = [c] := by rw [enc_cons_ne s1 s2 c [] hc, enc_nil]
  rw [← hE, dec_enc s1 s2 hs [c], hE]

theorem dec_s2s1 (s1 s2 : α) (hs : s2 ≠ s1) : dec s1 s2 [s2, s1] = [s1] := by
  have hE : enc s1 s2 [s1] = [s2, s1] := by rw [enc_cons_b s1 s2 [], enc_nil]
  rw [← hE, dec_enc s1 s2 hs [s1]]

/-- First-position self-match of the head pattern is impossible: for `c ≠ σ₁`,
`c·Q` is never `Q` glued to a tail (the paper's "second candidate" for `a ≠ σ₁`). -/
theorem head_no_pos0 (s1 s2 : α) (hs : s2 ≠ s1) :
    ∀ (X' : List α) (c : α), c ≠ s1 → ∀ D : List α,
      c :: (enc s1 s2 X' ++ [s1, s1]) = (enc s1 s2 X' ++ [s1, s1]) ++ D → False := by
  intro X'
  induction X' with
  | nil =>
      intro c hc D h
      rw [enc_nil, List.nil_append, List.cons_append, List.cons_append,
        List.nil_append] at h
      injection h with h0 _
      exact hc h0
  | cons x X'' ih =>
      intro c hc D h
      by_cases hx : x = s1
      · rw [hx, enc_cons_b s1 s2 X'', List.cons_append, List.cons_append,
          List.cons_append, List.cons_append] at h
        injection h with _ h1
        injection h1 with h2 _
        exact hs h2
      · rw [enc_cons_ne s1 s2 x X'' hx, List.cons_append, List.cons_append] at h
        injection h with hcx h2
        exact ih x (by rw [← hcx]; exact hc) D h2

/-- Two-position self-match is impossible too (the `a = σ₁` candidates): neither
`σ₂σ₁·Q` nor `σ₁σ₂·Q` equals `Q` glued to a tail. -/
theorem no_border_both (s1 s2 : α) (hs : s2 ≠ s1) :
    ∀ (X' D : List α),
      (s2 :: s1 :: (enc s1 s2 X' ++ [s1, s1])
          = (enc s1 s2 X' ++ [s1, s1]) ++ D → False) ∧
      (s1 :: s2 :: (enc s1 s2 X' ++ [s1, s1])
          = (enc s1 s2 X' ++ [s1, s1]) ++ D → False) := by
  intro X'
  induction X' with
  | nil =>
      intro D
      rw [enc_nil, List.nil_append, List.cons_append, List.cons_append, List.nil_append]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · injection h with h0 _
        exact hs h0
      · injection h with _ h1
        injection h1 with h2 _
        exact hs h2
  | cons x X'' ih =>
      intro D
      by_cases hx : x = s1
      · rw [hx, enc_cons_b s1 s2 X'', List.cons_append, List.cons_append,
          List.cons_append, List.cons_append]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · injection h with _ h1
          injection h1 with _ h4
          exact (ih D).1 h4
        · injection h with h1 _
          exact hs h1.symm
      · rw [enc_cons_ne s1 s2 x X'' hx, List.cons_append, List.cons_append]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · injection h with h1 h2
          subst h1
          exact (ih D).2 h2
        · injection h with h1 h2
          subst h1
          exact (ih D).1 h2

theorem head_correct (sig : List α) (hnd : sig.Pairwise (· ≠ ·)) (h2 : 2 ≤ sig.length)
    (X : List α) (hX : ∀ c ∈ X, c ∈ sig) : head sig X = X.take 1 := by
  have htail : tail sig X = X.drop 1 := tail_correct sig hnd h2 X hX
  cases sig with
  | nil => simp at h2
  | cons s1 sig' =>
      cases sig' with
      | nil => simp at h2
      | cons s2 rest =>
          rw [List.pairwise_cons] at hnd
          have hs : s2 ≠ s1 := fun he => hnd.1 s2 (List.mem_cons_self ..) he.symm
          show dec s1 s2 (subst [] (enc s1 s2 (tail (s1 :: s2 :: rest) X) ++ [s1, s1])
            (enc s1 s2 X ++ [s1, s1])) = X.take 1
          rw [htail]
          cases X with
          | nil =>
              show dec s1 s2 (subst [] (enc s1 s2 [] ++ [s1, s1])
                (enc s1 s2 [] ++ [s1, s1])) = []
              rw [enc_nil, List.nil_append,
                subst_cons_match [] [s1, s1] (by simp) s1 _ [] (matchHere_self [s1, s1]),
                subst_nil, List.nil_append, dec_nil]
          | cons c X' =>
              have hQne : enc s1 s2 X' ++ [s1, s1] ≠ [] := by
                intro he
                cases hE : enc s1 s2 X' with
                | nil => rw [hE, List.nil_append] at he; exact nomatch he
                | cons e E' => rw [hE, List.cons_append] at he; exact nomatch he
              show dec s1 s2 (subst [] (enc s1 s2 X' ++ [s1, s1])
                (enc s1 s2 (c :: X') ++ [s1, s1])) = [c]
              by_cases hcb : c = s1
              · rw [hcb, enc_cons_b s1 s2 X', List.cons_append, List.cons_append]
                cases hm0 : matchHere (enc s1 s2 X' ++ [s1, s1])
                    (s2 :: s1 :: (enc s1 s2 X' ++ [s1, s1]))
                · rw [subst_cons_none _ _ _ _ hm0]
                  cases X' with
                  | nil =>
                      rw [enc_nil, List.nil_append]
                      have hm : matchHere [s1, s1] (s1 :: [s1, s1]) = some [s1] :=
                        matchHere_prefix [s1, s1] [s1]
                      have hn : ¬ Occ [s1, s1] [s1] := by
                        intro ho
                        have hl := occ_length ho
                        simp at hl
                      rw [subst_cons_match [] [s1, s1] (by simp) s1 [s1, s1] [s1] hm,
                        List.nil_append, subst_no_occ [] [s1, s1] [s1] hn,
                        dec_s2s1 s1 s2 hs]
                  | cons x X'' =>
                      by_cases hx : x = s1
                      · rw [hx, enc_cons_b s1 s2 X'', List.cons_append, List.cons_append]
                        have hm : matchHere (s2 :: s1 :: (enc s1 s2 X'' ++ [s1, s1]))
                            (s1 :: (s2 :: s1 :: (enc s1 s2 X'' ++ [s1, s1]))) = none :=
                          matchHere_ne s2 _ s1 _ hs
                        have hKne : s2 :: s1 :: (enc s1 s2 X'' ++ [s1, s1]) ≠ [] := by
                          intro he
                          exact nomatch he
                        rw [subst_cons_none _ _ _ _ hm, subst_self _ _ hKne,
                          dec_s2s1 s1 s2 hs]
                      · rw [enc_cons_ne s1 s2 x X'' hx, List.cons_append]
                        have hm : matchHere (x :: (enc s1 s2 X'' ++ [s1, s1]))
                            (s1 :: (x :: (enc s1 s2 X'' ++ [s1, s1]))) = none :=
                          matchHere_ne x _ s1 _ hx
                        have hKne : x :: (enc s1 s2 X'' ++ [s1, s1]) ≠ [] := by
                          intro he
                          exact nomatch he
                        rw [subst_cons_none _ _ _ _ hm, subst_self _ _ hKne,
                          dec_s2s1 s1 s2 hs]
                · exact ((no_border_both s1 s2 hs X' _).1 (matchHere_app _ _ _ hm0)).elim
              · rw [enc_cons_ne s1 s2 c X' hcb, List.cons_append]
                cases hm : matchHere (enc s1 s2 X' ++ [s1, s1])
                    (c :: (enc s1 s2 X' ++ [s1, s1]))
                · rw [subst_cons_none _ _ _ _ hm, subst_self _ _ hQne,
                    dec_single s1 s2 hs c hcb]
                · exact (head_no_pos0 s1 s2 hs X' c hcb _ (matchHere_app _ _ _ hm)).elim

#eval tail ['a', 'b', 'c'] ['c', 'a', 'b']              -- [a, b]
#eval tail ['a', 'b'] ['a', 'a', 'b']                   -- [a, b]  (X starting with σ₁)
#eval tail ['a', 'b'] []                                -- []
#eval head ['a', 'b', 'c'] ['c', 'a', 'b']              -- [c]
#eval head ['a', 'b', 'c'] []                           -- []

/-! ## Definition (freezing) and Theorem (rep_n): multiple substitution -/

/-- If the unfrozen text `T` begins with the block `X`, return the rest. -/
def dropU? : List α → List (α × Option Nat) → Option (List (α × Option Nat))
  | [], T => some T
  | _, [] => none
  | c :: X', (d, none) :: T' => if c = d then dropU? X' T' else none
  | _ :: _, _ :: _ => none

theorem dropU?_length : ∀ (X : List α) (T U : List (α × Option Nat)),
    dropU? X T = some U → U.length + X.length ≤ T.length := by
  intro X
  induction X with
  | nil =>
      intro T U h
      simp only [dropU?] at h
      injection h with h'
      subst h'
      simp only [List.length_nil]
      omega
  | cons c X ih =>
      intro T U h
      cases T with
      | nil => simp [dropU?] at h
      | cons t T' =>
          obtain ⟨d, o⟩ := t
          cases o with
          | none =>
              by_cases hcd : c = d
              · subst hcd
                simp [dropU?] at h
                have hlen := ih T' U h
                simp only [List.length_cons] at hlen ⊢
                omega
              · simp [dropU?, hcd] at h
          | some j => simp [dropU?] at h

/-- The first `k` entries, frozen (they form the matched block). -/
def freezeBlock (i : Nat) : Nat → List (α × Option Nat) → List (α × Option Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, (d, _) :: T' => (d, some i) :: freezeBlock i k T'

/-- One freezing round: scan for `X` leftmost-first, non-overlapping, among
the unfrozen positions, freezing every match (tagged with the round `i`). -/
def freezePass (X : List α) (hX : X ≠ []) (i : Nat) :
    List (α × Option Nat) → List (α × Option Nat)
  | [] => []
  | t :: T' =>
      match _h : dropU? X (t :: T') with
      | some U => freezeBlock i X.length (t :: T') ++ freezePass X hX i U
      | none => t :: freezePass X hX i T'
termination_by T => T.length
decreasing_by
  · have hlen := dropU?_length X (t :: T') U _h
    have : 1 ≤ X.length := by
      cases X with
      | nil => exact absurd rfl hX
      | cons _ _ => simp
    simp only [List.length_cons] at hlen ⊢
    omega
  · simp only [List.length_cons]
    omega

/-- Run the freezing rounds, in order. -/
def markRounds : List (List α × List α) → Nat → List (α × Option Nat) → List (α × Option Nat)
  | [], _, T => T
  | (X, _) :: ps, i, T => markRounds ps (i + 1) (if h : X = [] then T else freezePass X h i T)

/-- Length of the maximal run of round-`i` entries at the head. -/
def runLen : Nat → List (α × Option Nat) → Nat
  | _, [] => 0
  | i, (_, some j) :: T => if j = i then runLen i T + 1 else 0
  | _, (_, none) :: _ => 0

/-- Definition (freezing), final pass: replace each frozen run of round `i`
by one `Y_i` per `|X_i|`-sized chunk; unfrozen characters pass through. -/
def assemble (pairs : List (List α × List α)) : List (α × Option Nat) → List α
  | [] => []
  | (t, none) :: T' => t :: assemble pairs T'
  | (t, some i) :: T' =>
      (List.replicate
        (runLen i ((t, some i) :: T') / (pairs.getD (i - 1) ([], [])).1.length)
        (pairs.getD (i - 1) ([], [])).2).flatten
        ++ assemble pairs (List.drop (runLen i ((t, some i) :: T')) ((t, some i) :: T'))
termination_by T => T.length
decreasing_by
  · simp only [List.length_cons]
    omega
  · have hk : 1 ≤ runLen i ((t, some i) :: T') := by simp [runLen]
    have hd : (List.drop (runLen i ((t, some i) :: T')) ((t, some i) :: T')).length
        = ((t, some i) :: T').length - runLen i ((t, some i) :: T') := List.length_drop
    simp only [List.length_cons] at hd ⊢
    omega

/-- Definition (freezing): the reference semantics of multiple substitution. -/
def repRef (pairs : List (List α × List α)) (S : List α) : List α :=
  assemble pairs (markRounds pairs 1 (S.map (fun c => (c, none))))

/-- Theorem (rep_n), construction: renaming and repair passes, `i = 1..n`. -/
def renameRepair (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (Xi, _) :: ps, T =>
      renameRepair b x (i + 1) ps
        (subst (enc b x Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc b x Xi) T))

/-- Theorem (rep_n), construction: instantiation passes, `i = n..1`. -/
def instantiate (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (_, Yi) :: ps, T =>
      instantiate b x (i - 1) ps (subst (enc b x Yi) (marker x b (i + 1)) T)

/-- An enc-based variant of the multiple-substitution construction, which
computes the freezing semantics only under the condition that every `X_i`
is a single character or does not end in `x` (a statement not proven in
this file).  Kept for the shadowing demo below. -/
def repC (b x : α) (pairs : List (List α × List α)) (S : List α) : List α :=
  dec b x (instantiate b x pairs.length pairs.reverse
    (renameRepair b x 1 pairs (enc b x S)))

#eval repRef [(['a'], ['b', 'a'])] ['a', 'b', 'a']                     -- [b, a, b, b, a]
#eval repC 'a' 'c' [(['a'], ['b', 'a'])] ['a', 'b', 'a']               -- [b, a, b, b, a]
#eval repRef [(['a', 'b'], ['c']), (['b', 'a'], ['a', 'a'])] ['a', 'b', 'a']  -- [c, a]
#eval repC 'a' 'c' [(['a', 'b'], ['c']), (['b', 'a'], ['a', 'a'])] ['a', 'b', 'a']  -- [c, a]

-- The single-char / no-trailing-`x` condition is essential — the
-- shadowing example: `X₁ = "ab"` and `X₂ = "bbb"` both end with `x = 'b'`.
#eval repC 'a' 'b' [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
#eval repRef [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
-- the two disagree: a spurious match of enc(X₁) shadows a genuine one

-- Regression sweep: repC against the freezing semantics on the patterns it
-- is meant to handle (b = 'a', x = 'c'; every pattern is a single char or
-- avoids a trailing 'c'), all string shapes over {a, b, c}.
#eval Id.run do
  let mut allOk := true
  let strs : List (List Char) :=
    ["", "a", "b", "c", "ab", "ba", "ca", "bc", "abc", "aab", "bcc"].map String.toList
  let pats : List (List Char) :=
    ["a", "b", "c", "ab", "ba", "aa", "bb", "cab"].map String.toList
  for S in strs do
    for X1 in pats do
      for X2 in pats do
        let pairs := [(X1, ['x']), (X2, ['y'])]
        if repC 'a' 'c' pairs S != repRef pairs S then
          allOk := false
  return allOk
-- true

/-! ## The comma code and the unrestricted multiple substitution

The paper's Theorem (Multiple Substitution): the same
rename/repair/instantiate architecture as `repC`, run over the *comma code*
`enc2` (every character escaped as the block `x·c` -- all code words length
2, phase-locked).  It computes the freezing semantics for *arbitrary*
nonempty patterns: no hypothesis on the patterns is needed (the failure of
the enc-based variant is a remark in the paper -- `repC` above).  The code
layer is proven here (`enc2Pass_eq`, `dec2Pass_enc2`); the staging argument
is stated as `repC2_correct` with a roadmap. -/

/-- The comma code as a function: every character `c` of `S` becomes the
block `x·c`.  The paper defines it as the pass composition `[xx/x]` then
`[xc/c]` per `c ≠ x`; see `enc2Pass_eq` for the bridge. -/
def enc2 (x : α) (S : List α) : List α := (S.map fun c => [x, c]).flatten

omit [DecidableEq α] in
theorem enc2_nil (x : α) : enc2 x [] = [] := rfl

omit [DecidableEq α] in
theorem enc2_cons (x c : α) (S : List α) :
    enc2 x (c :: S) = [x, c] ++ enc2 x S := by
  simp [enc2, List.map_cons, List.flatten_cons]

omit [DecidableEq α] in
theorem enc2_append (x : α) (S T : List α) :
    enc2 x (S ++ T) = enc2 x S ++ enc2 x T := by
  simp [enc2, List.map_append, List.flatten_append]

omit [DecidableEq α] in
theorem enc2_injective (x : α) : ∀ S T : List α, enc2 x S = enc2 x T → S = T := by
  intro S
  induction S with
  | nil =>
      intro T h
      cases T with
      | nil => rfl
      | cons t T' => simp [enc2] at h
  | cons c S' ih =>
      intro T h
      cases T with
      | nil => simp [enc2] at h
      | cons d T' =>
          rw [enc2_cons, enc2_cons] at h
          simp only [List.cons_append, List.nil_append] at h
          injection h with _ h1
          injection h1 with h3 h4
          subst h3
          exact congrArg (c :: ·) (ih T' h4)

/-- A unit of the comma code in progress: the block `x·c` once the character
has been escaped (or is `x` itself, doubled by the first pass), bare before
that.  `l` is the list of already-processed characters. -/
def encUnit (x : α) (l : List α) (c : α) : List α :=
  if c = x ∨ c ∈ l then [x, c] else [c]

/-- The doubling pass `[xx/x]` produces the unit text with nothing
processed: `xx` for each `x`, bare `c` for each `c ≠ x`. -/
theorem subst_double_pass (x : α) : ∀ S : List α,
    subst [x, x] [x] S = (S.map (encUnit x [])).flatten := by
  intro S
  induction S with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons c S ih =>
      by_cases hcx : c = x
      · rw [hcx, subst_cons_match [x, x] [x] (by simp) x S S (matchHere_one_self x S),
          ih]
        simp [encUnit]
      · rw [subst_cons_none [x, x] [x] c S (matchHere_one_ne x c S hcx), ih]
        simp [encUnit, hcx]

/-- A single-character pass never touches a unit that does not contain it. -/
theorem subst_pass_unit {x c : α} : ∀ (u T : List α), c ∉ u →
    subst [x, c] [c] (u ++ T) = u ++ subst [x, c] [c] T := by
  intro u
  induction u with
  | nil => intro T _; rfl
  | cons d u' ih =>
      intro T h
      have hd : d ≠ c := fun he => h (by rw [he]; exact List.mem_cons_self)
      rw [List.cons_append,
        subst_cons_none [x, c] [c] d (u' ++ T) (matchHere_one_ne c d (u' ++ T) hd),
        List.cons_append, ih T (fun hm => h (List.mem_cons_of_mem _ hm))]

/-- The pass escapes exactly its own bare unit. -/
theorem subst_pass_escape {x c : α} (T : List α) :
    subst [x, c] [c] ([c] ++ T) = [x, c] ++ subst [x, c] [c] T := by
  show subst [x, c] [c] (c :: T) = [x, c] ++ subst [x, c] [c] T
  rw [subst_cons_match [x, c] [c] (by simp) c T T (matchHere_one_self c T)]

theorem encUnit_stable {x c d : α} (hdc : d ≠ c) (l : List α) :
    encUnit x (c :: l) d = encUnit x l d := by
  by_cases hdx : d = x
  · subst hdx; simp [encUnit]
  · by_cases hdl : d ∈ l
    · simp [encUnit, hdx, hdl]
    · simp [encUnit, hdx, hdl, hdc]

/-- Inserting the (never processed) `x` into the processed list changes no
unit: `x` is escaped by the doubling pass, not by a `[xc/c]` pass. -/
theorem encUnit_cons_x (x : α) (u w : List α) (d : α) :
    encUnit x (u ++ [x] ++ w) d = encUnit x (u ++ w) d := by
  by_cases hdx : d = x
  · subst hdx; simp [encUnit]
  · simp [encUnit, List.mem_append, hdx]

/-- One encoding pass on a unit text: `[xc/c]` escapes the bare units `c`
and leaves every other unit untouched. -/
theorem subst_pass_units {x c : α} (hcx : c ≠ x) : ∀ (l S : List α), c ∉ l →
    subst [x, c] [c] ((S.map (encUnit x l)).flatten) =
      (S.map (encUnit x (c :: l))).flatten := by
  intro l S hcl
  induction S with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons d S' ih =>
      rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons]
      by_cases hdc : d = c
      · rw [hdc]
        have hu : encUnit x l c = [c] := by simp [encUnit, hcx, hcl]
        have hu' : encUnit x (c :: l) c = [x, c] := by simp [encUnit]
        rw [hu, subst_pass_escape, ih, hu']
      · have hcu : c ∉ encUnit x l d := by
          by_cases hP : d = x ∨ d ∈ l
          · have hu : encUnit x l d = [x, d] := ite_eq_left hP
            rw [hu]
            intro hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with hc | hc
            · exact absurd hc hcx
            · exact absurd hc.symm hdc
          · have hu : encUnit x l d = [d] := ite_eq_right hP
            rw [hu]
            intro hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            exact absurd hc.symm hdc
        have hu : encUnit x (c :: l) d = encUnit x l d := encUnit_stable hdc l
        rw [subst_pass_unit (encUnit x l d) ((S'.map (encUnit x l)).flatten) hcu, ih, hu]

/-- The encoding passes of the comma code: `[xx/x]` first, then `[xc/c]`
for each `c ∈ σ` with `c ≠ x` (in σ's order; the order is immaterial). -/
def enc2Go (x : α) : List α → List α → List α
  | [], T => T
  | c :: σ, T => if c = x then enc2Go x σ T else enc2Go x σ (subst [x, c] [c] T)

/-- The comma code as the pass composition of the paper. -/
def enc2Pass (x : α) (σ S : List α) : List α := enc2Go x σ (subst [x, x] [x] S)

theorem enc2Go_units (x : α) : ∀ (σ l S : List α), σ.Pairwise (· ≠ ·) →
    (∀ d ∈ l, ∀ e ∈ σ, d ≠ e) →
    enc2Go x σ ((S.map (encUnit x l)).flatten) =
      (S.map (encUnit x (σ.reverse ++ l))).flatten := by
  intro σ
  induction σ with
  | nil => intro l S _ _; rfl
  | cons c σ' ih =>
      intro l S hnd hdis
      rw [List.pairwise_cons] at hnd
      by_cases hcx : c = x
      · simp only [enc2Go]
        rw [ite_eq_left hcx,
          ih l S hnd.2 (fun d hd e he => hdis d hd e (List.mem_cons_of_mem _ he)),
          hcx, List.reverse_cons]
        have hmap : S.map (encUnit x (σ'.reverse ++ l))
            = S.map (encUnit x (σ'.reverse ++ [x] ++ l)) := by
          refine List.map_congr_left fun d _ => ?_
          exact (encUnit_cons_x x σ'.reverse l d).symm
        rw [hmap]
      · have hcl : c ∉ l := fun hc => absurd rfl (hdis c hc c List.mem_cons_self)
        have hdis' : ∀ d ∈ c :: l, ∀ e ∈ σ', d ≠ e := by
          intro d hd e he
          rcases List.mem_cons.mp hd with hd | hd
          · subst hd; exact hnd.1 e he
          · exact hdis d hd e (List.mem_cons_of_mem _ he)
        have happ : σ'.reverse ++ c :: l = (c :: σ').reverse ++ l := by
          rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
        simp only [enc2Go]
        rw [ite_eq_right hcx, subst_pass_units hcx l S hcl,
          ih (c :: l) S hnd.2 hdis', happ]

/-- The pass composition of the paper computes the block map: the comma code
is an expression of the baseline calculus (Lemma (Comma Code) (i), first
half). -/
theorem enc2Pass_eq (x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·)) (S : List α)
    (hS : ∀ c ∈ S, c ∈ σ) : enc2Pass x σ S = enc2 x S := by
  rw [enc2Pass, subst_double_pass, enc2Go_units x σ [] S hnd (by simp), List.append_nil]
  have hunit : ∀ d ∈ S, encUnit x σ.reverse d = [x, d] := by
    intro d hd
    by_cases hdx : d = x
    · subst hdx; simp [encUnit]
    · simp [encUnit, hdx, List.mem_reverse.mpr (hS d hd)]
  have hmap : S.map (encUnit x σ.reverse) = S.map (fun c => [x, c]) :=
    List.map_congr_left hunit
  rw [enc2]
  exact congrArg List.flatten hmap

/-- A decoding unit: the intact block `x·d`, or the bare character `d` once
its block has been collapsed.  The guard `d ≠ x` reflects that `x` is never
processed by these passes (`xx`-blocks are handled by the final halving
pass), and makes the definition insensitive to `x` in the processed list. -/
def decUnit (x : α) (l : List α) (d : α) : List α :=
  if d ≠ x ∧ d ∈ l then [d] else [x, d]

theorem decUnit_stable {x c d : α} (hdc : d ≠ c) (l : List α) :
    decUnit x (c :: l) d = decUnit x l d := by
  by_cases hdx : d = x
  · subst hdx; simp [decUnit]
  · by_cases hdl : d ∈ l
    · simp [decUnit, hdx, hdl]
    · simp [decUnit, hdx, hdl, hdc]

theorem decUnit_cons_x (x : α) (u w : List α) (d : α) :
    decUnit x (u ++ [x] ++ w) d = decUnit x (u ++ w) d := by
  by_cases hdx : d = x
  · subst hdx; simp [decUnit]
  · simp [decUnit, List.mem_append, hdx]

theorem decUnit_collapse {x c : α} (hcx : c ≠ x) (l : List α) :
    decUnit x (c :: l) c = [c] := by
  simp [decUnit, hcx]

/-- In a unit text, no single-character pattern of a not-yet-processed `c`
starts at the head: the flattened units begin with a comma `x` or with an
already-processed character. -/
theorem dec_head_none {x c : α} (hcx : c ≠ x) (l : List α) (hcl : c ∉ l) :
    ∀ Z : List α, matchHere [c] ((Z.map (decUnit x l)).flatten) = none := by
  intro Z
  induction Z with
  | nil => rfl
  | cons d Z' ih =>
      rw [List.map_cons, List.flatten_cons]
      by_cases h : d ≠ x ∧ d ∈ l
      · have hdc : d ≠ c := fun he => hcl (he ▸ h.2)
        have hu : decUnit x l d = [d] := ite_eq_left h
        rw [hu, List.cons_append, matchHere_one_ne c d _ hdc]
      · have hu : decUnit x l d = [x, d] := ite_eq_right h
        rw [hu, List.cons_append, List.cons_append,
          matchHere_one_ne c x _ (Ne.symm hcx)]

/-- One decoding pass on a unit text: `[c/xc]` collapses the intact blocks
`x·c` and leaves every other unit untouched.  (The potential straddle at
the data `x` of an `xx`-block dies by `dec_head_none`.) -/
theorem subst_collapse_units {x c : α} (hcx : c ≠ x) : ∀ (l Z : List α), c ∉ l →
    (∀ e ∈ l, e ≠ x) →
    subst [c] [x, c] ((Z.map (decUnit x l)).flatten) =
      (Z.map (decUnit x (c :: l))).flatten := by
  intro l Z hcl hlx
  induction Z with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons d Z' ih =>
      rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons]
      by_cases hdc : d = c
      · rw [hdc]
        have hu : decUnit x l c = [x, c] := by simp [decUnit, hcl]
        rw [hu]
        show subst [c] [x, c] (x :: c :: (Z'.map (decUnit x l)).flatten) = _
        rw [subst_cons_match [c] [x, c] (by simp) x
            (c :: (Z'.map (decUnit x l)).flatten) ((Z'.map (decUnit x l)).flatten)
            (matchHere_two_self x c ((Z'.map (decUnit x l)).flatten)),
          ih, decUnit_collapse hcx l]
      · by_cases hdx : d = x
        · rw [hdx]
          have hu : decUnit x l x = [x, x] := by simp [decUnit]
          have hu' : decUnit x (c :: l) x = [x, x] := by simp [decUnit]
          rw [hu, hu']
          show subst [c] [x, c] (x :: x :: (Z'.map (decUnit x l)).flatten) = _
          rw [subst_cons_none [c] [x, c] x (x :: (Z'.map (decUnit x l)).flatten)
              (matchHere_two_head x c (x :: (Z'.map (decUnit x l)).flatten)
                (matchHere_one_ne c x _ (Ne.symm hcx))),
            subst_cons_none [c] [x, c] x ((Z'.map (decUnit x l)).flatten)
              (matchHere_two_head x c ((Z'.map (decUnit x l)).flatten)
                (dec_head_none hcx l hcl Z')),
            ih]
          rfl
        · by_cases hdl : d ∈ l
          · have hbar : decUnit x l d = [d] := by simp [decUnit, hdx, hdl]
            have hu' : decUnit x (c :: l) d = [d] := by
              rw [decUnit_stable hdc l, hbar]
            rw [hbar, hu']
            show subst [c] [x, c] (d :: (Z'.map (decUnit x l)).flatten) = _
            rw [subst_cons_none [c] [x, c] d ((Z'.map (decUnit x l)).flatten)
                (matchHere_two_ne x c d _ hdx), ih]
            rfl
          · have hint : decUnit x l d = [x, d] := by simp [decUnit, hdx, hdl]
            have hu' : decUnit x (c :: l) d = [x, d] := by
              rw [decUnit_stable hdc l, hint]
            rw [hint, hu']
            show subst [c] [x, c] (x :: d :: (Z'.map (decUnit x l)).flatten) = _
            rw [subst_cons_none [c] [x, c] x (d :: (Z'.map (decUnit x l)).flatten)
                (matchHere_two_head x c (d :: (Z'.map (decUnit x l)).flatten)
                  (matchHere_one_ne c d _ hdc)),
              subst_cons_none [c] [x, c] d ((Z'.map (decUnit x l)).flatten)
                (matchHere_two_ne x c d _ hdx), ih]
            rfl

/-- The decoding passes of the comma code: `[c/xc]` for each `c ∈ σ` with
`c ≠ x`, with `[x/xx]` last (the order among the `c`'s is immaterial). -/
def dec2Passes (x : α) : List α → List α → List α
  | [], T => T
  | c :: σ, T => if c = x then dec2Passes x σ T else dec2Passes x σ (subst [c] [x, c] T)

/-- `dec2` as the pass composition of the paper. -/
def dec2Pass (x : α) (σ S : List α) : List α := subst [x] [x, x] (dec2Passes x σ S)

theorem dec2Passes_units (x : α) : ∀ (σ l Z : List α), σ.Pairwise (· ≠ ·) →
    (∀ e ∈ l, e ≠ x) → (∀ d ∈ l, ∀ e ∈ σ, d ≠ e) →
    dec2Passes x σ ((Z.map (decUnit x l)).flatten) =
      (Z.map (decUnit x (σ.reverse ++ l))).flatten := by
  intro σ
  induction σ with
  | nil => intro l Z _ _ _; rfl
  | cons c σ' ih =>
      intro l Z hnd hlx hdis
      rw [List.pairwise_cons] at hnd
      by_cases hcx : c = x
      · simp only [dec2Passes]
        rw [ite_eq_left hcx,
          ih l Z hnd.2 hlx (fun d hd e he => hdis d hd e (List.mem_cons_of_mem _ he)),
          hcx, List.reverse_cons]
        have hmap : Z.map (decUnit x (σ'.reverse ++ l))
            = Z.map (decUnit x (σ'.reverse ++ [x] ++ l)) := by
          refine List.map_congr_left fun d _ => ?_
          exact (decUnit_cons_x x σ'.reverse l d).symm
        rw [hmap]
      · have hcl : c ∉ l := fun hc => absurd rfl (hdis c hc c List.mem_cons_self)
        have hlx' : ∀ e ∈ c :: l, e ≠ x := by
          intro e he
          rcases List.mem_cons.mp he with he | he
          · subst he; exact hcx
          · exact hlx e he
        have hdis' : ∀ d ∈ c :: l, ∀ e ∈ σ', d ≠ e := by
          intro d hd e he
          rcases List.mem_cons.mp hd with hd | hd
          · subst hd; exact hnd.1 e he
          · exact hdis d hd e (List.mem_cons_of_mem _ he)
        have happ : σ'.reverse ++ c :: l = (c :: σ').reverse ++ l := by
          rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
        simp only [dec2Passes]
        rw [ite_eq_right hcx, subst_collapse_units hcx l Z hcl hlx,
          ih (c :: l) Z hnd.2 hlx' hdis', happ]

/-- The final halving pass `[x/xx]` on `Z` with every `x` doubled. -/
theorem subst_halve (x : α) : ∀ Z : List α,
    subst [x] [x, x] ((Z.map (fun d => if d = x then [x, x] else [d])).flatten) = Z := by
  intro Z
  induction Z with
  | nil =>
      simp only [List.map_nil, List.flatten_nil]
      exact subst_nil _ _
  | cons d Z' ih =>
      rw [List.map_cons, List.flatten_cons]
      by_cases hdx : d = x
      · have hu : (if d = x then [x, x] else [d]) = [x, x] := ite_eq_left hdx
        rw [hu]
        show subst [x] [x, x] (x :: x :: (Z'.map (fun d => if d = x then [x, x] else [d])).flatten) = _
        rw [subst_cons_match [x] [x, x] (by simp) x
            (x :: (Z'.map (fun d => if d = x then [x, x] else [d])).flatten)
            ((Z'.map (fun d => if d = x then [x, x] else [d])).flatten)
            (matchHere_two_self x x ((Z'.map (fun d => if d = x then [x, x] else [d])).flatten)),
          ih]
        rw [hdx]
        rfl
      · have hu : (if d = x then [x, x] else [d]) = [d] := ite_eq_right hdx
        rw [hu]
        show subst [x] [x, x] (d :: (Z'.map (fun d => if d = x then [x, x] else [d])).flatten) = _
        rw [subst_cons_none [x] [x, x] d ((Z'.map (fun d => if d = x then [x, x] else [d])).flatten)
            (matchHere_two_ne x x d _ hdx), ih]

/-- The decode round trip: `dec2` inverts `enc2` on inputs over `σ` (Lemma
(Comma Code) (i), second half). -/
theorem dec2Pass_enc2 (x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·)) (Z : List α)
    (hZ : ∀ c ∈ Z, c ∈ σ) : dec2Pass x σ (enc2 x Z) = Z := by
  have hmap : Z.map (fun c => [x, c]) = Z.map (decUnit x []) := by
    refine List.map_congr_left fun d _ => ?_
    simp [decUnit]
  have hstart : enc2 x Z = (Z.map (decUnit x [])).flatten :=
    congrArg List.flatten hmap
  rw [dec2Pass, hstart, dec2Passes_units x σ [] Z hnd (by simp) (by simp), List.append_nil]
  have hfinal : Z.map (decUnit x σ.reverse)
      = Z.map (fun d => if d = x then [x, x] else [d]) := by
    refine List.map_congr_left fun d hd => ?_
    by_cases hdx : d = x
    · subst hdx; simp [decUnit]
    · have hmem : d ∈ σ.reverse := List.mem_reverse.mpr (hZ d hd)
      simp [decUnit, hdx, hmem]
  rw [hfinal, subst_halve]

/-- Theorem (Multiple Substitution), construction: the same
rename/repair architecture as `repC`, over the comma code. -/
def renameRepair2 (b x : α) (σ : List α) :
    Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (Xi, _) :: ps, T =>
      renameRepair2 b x σ (i + 1) ps
        (subst (enc2Pass x σ Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc2Pass x σ Xi) T))

/-- Theorem (Multiple Substitution), construction:
instantiation passes, `i = n..1`. -/
def instantiate2 (b x : α) (σ : List α) :
    Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (_, Yi) :: ps, T =>
      instantiate2 b x σ (i - 1) ps (subst (enc2Pass x σ Yi) (marker x b (i + 1)) T)

/-- Theorem (Multiple Substitution): the construction of the
paper -- `dec2` then instantiation then rename/repair then `enc2`, all as
`subst` passes over the alphabet. -/
def repC2 (b x : α) (σ : List α) (pairs : List (List α × List α)) (S : List α) : List α :=
  dec2Pass x σ (instantiate2 b x σ pairs.length pairs.reverse
    (renameRepair2 b x σ 1 pairs (enc2Pass x σ S)))

/-! ### Normal-form items and occurrence toolkit

  A round's invariant is kept structurally: the intermediate texts are the
  concatenation of *items* -- `enc2`-fragments and markers -- rather than
  raw characters.  A *damaged* marker (`dmg`) is the intermediate state in
  which a spurious round-`i` match has eaten an older marker's first two
  characters; it remembers the eaten fragment tail `W` so that the repair
  pass can restore it. -/

/-- An item of the normal form: an `enc2`-image (a fragment), the round-`i`
marker `x b^{i+1}`, or a damaged marker -- a round-`i` marker followed by
`j` trailing `b`'s (the remains of the round-`j` marker `x b^{j+1}` whose
first two characters were eaten by a spurious match; `W` records the
fragment tail eaten along with them). -/
inductive NFItem (α : Type)
  | frag (W : List α)
  | mark (i : Nat)
  | dmg (W : List α) (i j : Nat)

/-- The flat text of an item list. -/
def itext (b x : α) : List (NFItem α) → List α
  | [] => []
  | NFItem.frag W :: ns => enc2 x W ++ itext b x ns
  | NFItem.mark i :: ns => marker x b (i + 1) ++ itext b x ns
  | NFItem.dmg _ i j :: ns => (marker x b (i + 1) ++ List.replicate j b) ++ itext b x ns

omit [DecidableEq α] in
/-- An occurrence of the middle part of an occurring block. -/
theorem occ_mid {u p v l : List α} (h : Occ (u ++ p ++ v) l) : Occ p l := by
  obtain ⟨s, t, ht⟩ := h
  refine ⟨s ++ u, v ++ t, ?_⟩
  rw [ht]
  simp [List.append_assoc]

omit [DecidableEq α] in
/-- An occurrence of `p` in `l₁ ++ l₂` lies in `l₁`, lies in `l₂`, or
straddles the boundary -- and then a nonempty suffix `p₂` of `p` is a
nonempty prefix of `l₂`. -/
theorem occ_app_cases {p l₁ l₂ : List α} (h : Occ p (l₁ ++ l₂)) :
    Occ p l₁ ∨ Occ p l₂ ∨ ∃ p₁ p₂ v, p = p₁ ++ p₂ ∧ p₁ ≠ [] ∧ p₂ ≠ [] ∧
      l₂ = p₂ ++ v := by
  obtain ⟨u, v, hv⟩ := h
  rw [List.append_assoc] at hv
  by_cases hu1 : l₁.length ≤ u.length
  · obtain ⟨A, hA, hS⟩ := pref_of l₁ u l₂ (p ++ v) hv hu1
    exact Or.inr (Or.inl ⟨A, v, by rw [hS, List.append_assoc]⟩)
  · by_cases hu2 : u.length + p.length ≤ l₁.length
    · obtain ⟨A, hA, hS⟩ := pref_of u l₁ (p ++ v) l₂ hv.symm (by omega)
      -- hA : l₁ = u ++ A,  hS : p ++ v = A ++ l₂
      obtain ⟨B, hA', hB⟩ := pref_of p A v l₂ hS (by
        have hA2 : u.length + A.length = l₁.length := by rw [hA, List.length_append]
        omega)
      refine Or.inl ⟨u, B, ?_⟩
      rw [hA, hA']
      simp [List.append_assoc]
    · obtain ⟨A, hA, hS⟩ := pref_of u l₁ (p ++ v) l₂ hv.symm (by omega)
      -- hA : l₁ = u ++ A,  hS : p ++ v = A ++ l₂
      have hA2 : u.length + A.length = l₁.length := by rw [hA, List.length_append]
      have hAlt : A.length < p.length := by omega
      obtain ⟨p₂, hp2, hS2⟩ := pref_of A p l₂ v hS.symm (by omega)
      have hpp : p.length = A.length + p₂.length := by rw [hp2]; exact List.length_append
      refine Or.inr (Or.inr ⟨A, p₂, v, hp2, ?_, ?_, hS2⟩)
      · cases A with
        | nil => simp only [List.length_nil] at hA2; omega
        | cons a A' => simp
      · cases p₂ with
        | nil => simp only [List.length_nil] at hpp; omega
        | cons c p₂' => simp

/-! ### Text-level facts about `enc2`-images and markers -/

omit [DecidableEq α] in
theorem enc2_head (x c : α) (W : List α) : enc2 x (c :: W) = x :: c :: enc2 x W := by
  simp [enc2_cons]

omit [DecidableEq α] in
theorem replicate_append (a : α) : ∀ (m n : Nat),
    List.replicate m a ++ List.replicate n a = List.replicate (m + n) a := by
  intro m
  induction m with
  | zero => intro n; rw [Nat.zero_add]; rfl
  | succ m ih =>
      intro n
      show a :: (List.replicate m a ++ List.replicate n a) = List.replicate (Nat.succ m + n) a
      rw [ih, Nat.succ_add]
      rfl

omit [DecidableEq α] in
/-- A nonempty suffix of a run of `a`'s starts with `a`. -/
theorem replicate_suffix (a : α) : ∀ (k : Nat) (s p : List α),
    s ++ p = List.replicate k a → p ≠ [] → ∃ r, p = a :: r := by
  intro k
  induction k with
  | zero =>
      intro s p h hp
      cases p with
      | nil => exact absurd rfl hp
      | cons c p' => exact absurd h (by simp)
  | succ k ih =>
      intro s p h hp
      rw [show List.replicate (Nat.succ k) a = a :: List.replicate k a from rfl] at h
      cases s with
      | nil =>
          rw [List.nil_append] at h
          cases p with
          | nil => exact absurd rfl hp
          | cons c p' =>
              injection h with hc _
              exact ⟨p', by rw [hc]⟩
      | cons d s' =>
          rw [List.cons_append] at h
          injection h with hd h'
          subst hd
          exact ih s' p h' hp

omit [DecidableEq α] in
/-- A proper suffix of a marker `x b^k` starts with `b`. -/
theorem marker_straddle (x b : α) (k : Nat) (p₁ p₂ : List α)
    (h : marker x b k = p₁ ++ p₂) (h1 : p₁ ≠ []) (h2 : p₂ ≠ []) :
    ∃ r, p₂ = b :: r := by
  cases p₁ with
  | nil => exact absurd rfl h1
  | cons d s =>
      rw [List.cons_append, marker] at h
      injection h with hd h'
      subst hd
      exact replicate_suffix b k s p₂ h'.symm h2

omit [DecidableEq α] in
/-- The head of an `enc2`-image: empty or comma-first. -/
theorem enc2_nil_or_x (x : α) : ∀ W : List α, enc2 x W = [] ∨ ∃ T, enc2 x W = x :: T := by
  intro W
  cases W with
  | nil => exact Or.inl rfl
  | cons c W' => exact Or.inr ⟨c :: enc2 x W', enc2_head x c W'⟩

omit [DecidableEq α] in
/-- The head of an item list's text: empty or comma/marker-first. -/
theorem itext_nil_or_x (b x : α) : ∀ ns : List (NFItem α),
    itext b x ns = [] ∨ ∃ T, itext b x ns = x :: T := by
  intro ns
  induction ns with
  | nil => exact Or.inl rfl
  | cons it ns ih =>
      cases it with
      | frag W =>
          rcases enc2_nil_or_x x W with h | ⟨T, h⟩
          · rw [itext, h, List.nil_append]; exact ih
          · exact Or.inr ⟨T ++ itext b x ns, by rw [itext, h, List.cons_append]⟩
      | mark i => exact Or.inr ⟨_, rfl⟩
      | dmg W i j => exact Or.inr ⟨_, rfl⟩

omit [DecidableEq α] in
/-- An `enc2`-image contains no `bb` (every `b` is data, followed by the
next block's comma). -/
theorem no_bb_enc2 (x b : α) (hxb : x ≠ b) : ∀ W : List α, ¬ Occ [b, b] (enc2 x W) := by
  intro W
  induction W with
  | nil =>
      intro h
      have hl := occ_length h
      rw [enc2_nil] at hl
      simp at hl
  | cons c W' ih =>
      intro h
      rw [enc2_cons] at h
      rcases occ_app_cases h with h1 | h1 | ⟨p₁, p₂, v, hp, h1, h2, h3⟩
      · -- Occ [b,b] [x,c] forces x = b
        obtain ⟨u, w, hw⟩ := h1
        cases u with
        | nil =>
            rw [List.nil_append, List.cons_append, List.cons_append, List.nil_append] at hw
            injection hw with hx _
            exact hxb hx
        | cons d u' =>
            have hl := congrArg List.length hw
            simp only [List.length_append, List.length_cons] at hl
            omega
      · exact ih h1
      · -- straddle: a nonempty suffix of `[b,b]` starts with `b`, so `enc2 W'`
        -- would start with `b`, but an image is empty or comma-first
        obtain ⟨r, hr⟩ := replicate_suffix b 2 p₁ p₂ (by show p₁ ++ p₂ = [b, b]; rw [hp]) h2
        have hst : enc2 x W' = p₂ ++ v := h3
        rcases enc2_nil_or_x x W' with hnil | ⟨T, hcons⟩
        · rw [hnil] at hst
          cases p₂ with
          | nil => exact absurd rfl h2
          | cons d p' => exact nomatch hst
        · rw [hr, hcons] at hst
          injection hst with hbx _
          exact hxb hbx

omit [DecidableEq α] in
/-- A marker with at least two `b`'s contains `bb`. -/
theorem marker_occ_bb {x b : α} {n : Nat} (l : List α) (hn : 2 ≤ n)
    (h : Occ (marker x b n) l) : Occ [b, b] l := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 m] at hm
  subst hm
  have hsplit : marker x b (m + 2) = ([x] ++ [b, b]) ++ List.replicate m b := rfl
  rw [hsplit] at h
  exact occ_mid h

/-! ### The block lemmas of the phase-locking argument

  The code of every character is the 2-block `x·c`, so a normal text (a
  concatenation of `enc2`-fragments and markers) reads as a sequence of
  2-blocks.  The three facts below classify every match of a code
  `enc2 X` in such a text: it either starts at a block boundary
  (aligned), or it is *shadowed* (an aligned match starts one position
  earlier and fires first), or it is a *spurious* aligned match that eats
  the head of a following marker -- exactly the case the repair pass
  undoes. -/

theorem matchHere_cons_self (c : α) (B C : List α) :
    matchHere (c :: B) (c :: C) = matchHere B C := by
  simp [matchHere]

/-- Inversion for a `matchHere` at a cons-cons position. -/
theorem matchHere_cons_inv {c d : α} {B C D : List α}
    (h : matchHere (c :: B) (d :: C) = some D) : c = d ∧ matchHere B C = some D := by
  by_cases hcd : c = d
  · subst hcd
    rw [matchHere_cons_self] at h
    exact ⟨rfl, h⟩
  · rw [matchHere_ne c B d C hcd] at h
    exact absurd h (by simp)

/-- β-shadowing: if the code `enc2 X` matches starting at a *data*
position -- at the head `w` of the remaining fragment text
`w :: enc2 W' ++ T` -- then it also matches starting one position
earlier, at the fragment's comma.  So once the scan has rejected the
comma position it also rejects the data position, and the scan advances
block by block through a fragment; a misaligned match never fires.
Requires the continuation `T` after the fragment to be empty or
marker-headed (`x b …`), which the round invariant maintains. -/
theorem beta_shadow (x b : α) (hxb : x ≠ b) : ∀ (X : List α) (w : α) (W' T : List α),
    (T = [] ∨ ∃ T₂, T = x :: b :: T₂) → ∀ D : List α,
    matchHere (enc2 x X) (w :: enc2 x W' ++ T) = some D →
    ∃ D', matchHere (enc2 x X) (x :: w :: enc2 x W' ++ T) = some D' := by
  intro X
  induction X with
  | nil =>
      intro w W' T _ D _
      exact ⟨x :: w :: enc2 x W' ++ T, rfl⟩
  | cons c X' ih =>
      intro w W' T hT D h
      rw [enc2_head] at h ⊢
      obtain ⟨hw, h2⟩ := matchHere_cons_inv h
      subst hw
      cases W' with
      | nil =>
          -- the fragment is exhausted; the misaligned match reads `T`
          show ∃ D', matchHere (x :: c :: enc2 x X') (x :: x :: T) = some D'
          have h2' : matchHere (c :: enc2 x X') T = some D := h2
          cases T with
          | nil => simp [matchHere] at h2'
          | cons d T' =>
              obtain ⟨hd, h3⟩ := matchHere_cons_inv h2'
              rcases hT with hT | ⟨T₂, hT⟩
              · exact absurd hT (by simp)
              · injection hT with hdx hT₂
                rw [hdx] at hd
                rw [hdx, hT₂, hd]
                rw [hT₂] at h3
                cases X' with
                | nil => exact ⟨x :: b :: T₂, by simp [matchHere, enc2_nil]⟩
                | cons e X'' =>
                    rw [enc2_head] at h3
                    obtain ⟨hxe, _⟩ := matchHere_cons_inv h3
                    exact absurd hxe hxb
      | cons w₂ W'' =>
          -- the misaligned match recurses one block into the fragment
          have h2' : matchHere (c :: enc2 x X') (x :: w₂ :: enc2 x W'' ++ T) = some D := h2
          obtain ⟨hc, h3⟩ := matchHere_cons_inv h2'
          obtain ⟨D₂, hD₂⟩ := ih w₂ W'' T hT D h3
          refine ⟨D₂, ?_⟩
          show matchHere (x :: c :: enc2 x X') (x :: x :: x :: w₂ :: (enc2 x W'' ++ T))
              = some D₂
          rw [hc, matchHere_cons_self, matchHere_cons_self]
          exact hD₂

/-- L2 (aligned classification): a match of the code `enc2 X` starting at
a block boundary of the fragment text `enc2 W ++ T` is either *genuine*
-- it ends inside the fragment, consuming whole blocks (`W = X ++ W₂`)
-- or *spurious* (γ): it consumes the whole fragment plus the head `x b`
of the following marker, which is only possible when `X = W ++ [b]`.
The continuation `T` must be empty or marker-headed with two `b`'s
(every marker `x b^{j+1}` has `j ≥ 1`). -/
theorem aligned_class (x b : α) (hxb : x ≠ b) : ∀ (W X : List α) (T D : List α),
    (T = [] ∨ ∃ T₃, T = x :: b :: b :: T₃) →
    matchHere (enc2 x X) (enc2 x W ++ T) = some D →
    (∃ W₂, W = X ++ W₂ ∧ D = enc2 x W₂ ++ T) ∨
      (∃ T₃, T = x :: b :: b :: T₃ ∧ X = W ++ [b] ∧ D = b :: T₃) := by
  intro W
  induction W with
  | nil =>
      intro X T D hT h
      have h' : matchHere (enc2 x X) T = some D := h
      cases X with
      | nil =>
          refine Or.inl ⟨[], rfl, ?_⟩
          have h5 : some T = some D := h'
          injection h5 with hD
          exact hD.symm
      | cons c X' =>
          rw [enc2_head] at h'
          cases T with
          | nil => simp [matchHere] at h'
          | cons d T' =>
              obtain ⟨_, h2⟩ := matchHere_cons_inv h'
              rcases hT with hT | ⟨T₃, hT⟩
              · exact absurd hT (by simp)
              · injection hT with hdx hT'
                rw [hdx, hT']
                rw [hT'] at h2
                obtain ⟨hc, h3⟩ := matchHere_cons_inv h2
                rw [hc]
                cases X' with
                | nil =>
                    refine Or.inr ⟨T₃, rfl, rfl, ?_⟩
                    have h4 : some (b :: T₃) = some D := h3
                    injection h4 with hD
                    exact hD.symm
                | cons e X'' =>
                    rw [enc2_head] at h3
                    obtain ⟨hxe, _⟩ := matchHere_cons_inv h3
                    exact absurd hxe hxb
  | cons w W' ih =>
      intro X T D hT h
      cases X with
      | nil =>
          refine Or.inl ⟨w :: W', rfl, ?_⟩
          have h5 : some (enc2 x (w :: W') ++ T) = some D := h
          injection h5 with hD
          exact hD.symm
      | cons c X' =>
          have ha : matchHere (x :: c :: enc2 x X') (x :: w :: (enc2 x W' ++ T))
              = some D := h
          obtain ⟨_, hb⟩ := matchHere_cons_inv ha
          obtain ⟨hcw, h1⟩ := matchHere_cons_inv hb
          rcases ih X' T D hT h1 with ⟨W₂, hW', hD⟩ | ⟨T₃, hT3, hX', hD⟩
          · refine Or.inl ⟨W₂, ?_, hD⟩
            rw [← hcw, hW']
            rfl
          · refine Or.inr ⟨T₃, hT3, ?_, hD⟩
            rw [hX', ← hcw]
            rfl

/-- L1 (aligned fire): a genuine occurrence of `X` at the head of a
fragment fires: the code `enc2 X` matches and the scan resumes exactly
at `enc2 W₂ ++ T`. -/
theorem aligned_fire (x : α) (X W₂ T : List α) :
    matchHere (enc2 x X) (enc2 x (X ++ W₂) ++ T) = some (enc2 x W₂ ++ T) := by
  rw [enc2_append, List.append_assoc]
  exact matchHere_prefix _ _

/-- LM2: the code of the single character `b` matches the head of any
marker `x b^{j+1}`, eating exactly the marker's first two characters. -/
theorem mark_fire (x b : α) (j : Nat) (T : List α) :
    matchHere (enc2 x [b]) (marker x b (j + 1) ++ T) = some (List.replicate j b ++ T) := by
  show matchHere [x, b] (x :: b :: (List.replicate j b ++ T))
      = some (List.replicate j b ++ T)
  rw [matchHere_cons_self, matchHere_cons_self]
  rfl

/-- LM1: no code `enc2 X` with `X` neither empty nor the single
character `b` matches at a marker's head (`x b b …`). -/
theorem mark_none (x b : α) (hxb : x ≠ b) (X R : List α) (hX : X ≠ []) (hXb : X ≠ [b]) :
    matchHere (enc2 x X) (x :: b :: b :: R) = none := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
      show matchHere (x :: c :: enc2 x X') (x :: b :: b :: R) = none
      rw [matchHere_cons_self]
      by_cases hcb : c = b
      · rw [hcb, matchHere_cons_self]
        cases X' with
        | nil => exact absurd (by rw [hcb]) hXb
        | cons e X'' =>
            rw [enc2_head, matchHere_ne x _ b _ hxb]
      · rw [matchHere_ne c _ b _ hcb]

/-- The contrapositive of `beta_shadow`: when the aligned position has
been rejected, the following data position is rejected too, so the scan
skips a whole block of the fragment. -/
theorem beta_skip (x b : α) (hxb : x ≠ b) (X : List α) (w : α) (W' T : List α)
    (hT : T = [] ∨ ∃ T₂, T = x :: b :: T₂)
    (hA : matchHere (enc2 x X) (enc2 x (w :: W') ++ T) = none) :
    matchHere (enc2 x X) (w :: (enc2 x W' ++ T)) = none := by
  cases hM : matchHere (enc2 x X) (w :: (enc2 x W' ++ T)) with
  | none => rfl
  | some D =>
      obtain ⟨D', hD'⟩ := beta_shadow x b hxb X w W' T hT D hM
      have hD2 : matchHere (enc2 x X) (enc2 x (w :: W') ++ T) = some D' := hD'
      rw [hD2] at hA
      exact absurd hA (by simp)

omit [DecidableEq α] in
/-- Prepend the block `x·w` to an item list, merging into a leading
fragment. -/
def shiftItem (w : α) : List (NFItem α) → List (NFItem α)
  | NFItem.frag W :: ns => NFItem.frag (w :: W) :: ns
  | ns => NFItem.frag [w] :: ns

omit [DecidableEq α] in
/-- Prepend the fragment `A` to an item list, merging into a leading
fragment; an empty `A` prepends nothing. -/
def pushFrag (A : List α) : List (NFItem α) → List (NFItem α)
  | NFItem.frag W :: ns => NFItem.frag (A ++ W) :: ns
  | ns => if A = [] then ns else NFItem.frag A :: ns

omit [DecidableEq α] in
/-- Canonical item lists (the round invariant between rounds): every
fragment is nonempty and followed by a marker (or ends the list), every
marker has index `≥ 1`, and there are no damaged markers. -/
def Canon : List (NFItem α) → Prop
  | [] => True
  | NFItem.mark j :: ns => 1 ≤ j ∧ Canon ns
  | NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag _ :: NFItem.frag _ :: _ => False
  | NFItem.frag _ :: NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag W :: NFItem.mark j :: ns => W ≠ [] ∧ 1 ≤ j ∧ Canon ns
  | NFItem.frag W :: [] => W ≠ []

omit [DecidableEq α] in
/-- The canonical state between rounds, with the additional bound that
every marker's round is at most `m` (before round `i = m + 1` runs). -/
def CanonB (m : Nat) : List (NFItem α) → Prop
  | [] => True
  | NFItem.mark j :: ns => 1 ≤ j ∧ j ≤ m ∧ CanonB m ns
  | NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag _ :: NFItem.frag _ :: _ => False
  | NFItem.frag _ :: NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag W :: NFItem.mark j :: ns => W ≠ [] ∧ 1 ≤ j ∧ j ≤ m ∧ CanonB m ns
  | NFItem.frag W :: [] => W ≠ []

omit [DecidableEq α] in
/-- Every fragment in the list is nonempty. -/
def fragsNE : List (NFItem α) → Prop
  | [] => True
  | NFItem.frag W :: ns => W ≠ [] ∧ fragsNE ns
  | _ :: ns => fragsNE ns

/-- The shape of a rename round's output: fragments are nonempty and
never adjacent, markers have index `≥ 1` and `≤ i`, and damaged markers
belong to round `i` with at least one leftover `b`; a damaged marker
remembers the fragment `A` eaten in front of the pattern's final `b`,
so `X = A ++ [b]`. -/
def Rounded (b : α) (i : Nat) (X : List α) : List (NFItem α) → Prop
  | [] => True
  | NFItem.mark j :: ns => 1 ≤ j ∧ j ≤ i ∧ Rounded b i X ns
  | NFItem.dmg A i' j :: ns =>
      i' = i ∧ 1 ≤ j ∧ j ≤ i ∧ X = A ++ [b] ∧ Rounded b i X ns
  | NFItem.frag _ :: NFItem.frag _ :: _ => False
  | NFItem.frag W :: NFItem.dmg A i' j :: ns =>
      W ≠ [] ∧ i' = i ∧ 1 ≤ j ∧ j ≤ i ∧ X = A ++ [b] ∧ Rounded b i X ns
  | NFItem.frag W :: NFItem.mark j :: ns => W ≠ [] ∧ 1 ≤ j ∧ j ≤ i ∧ Rounded b i X ns
  | NFItem.frag W :: [] => W ≠ []

/-- The rename scan through the fragment `W`, which is followed by the
marker `mark j`; the result covers exactly the fragment and the marker.
Round `i`, pattern `X` (nonempty; the `[]` case is a degenerate
pass-through). -/
def fragGo (b x : α) (i : Nat) : List α → List α → Nat → List (NFItem α)
  | [], W, _ => [NFItem.frag W, NFItem.mark 1]
  | c :: X', w :: W', j =>
      if (w :: W').take (c :: X').length = c :: X' then
        NFItem.mark i :: fragGo b x i (c :: X') ((w :: W').drop (c :: X').length) j
      else if (c :: X') = (w :: W') ++ [b] then [NFItem.dmg (w :: W') i j]
      else shiftItem w (fragGo b x i (c :: X') W' j)
  | c :: X', [], j =>
      if (c :: X') = [b] then [NFItem.dmg [] i j] else [NFItem.mark j]
termination_by _ W _ => W.length
decreasing_by
  · have h1 : 1 ≤ (c :: X').length := by simp
    have h2 : ((w :: W').drop (c :: X').length).length = (w :: W').length - (c :: X').length :=
      List.length_drop
    have h3 : 1 ≤ (w :: W').length := by simp
    omega
  · simp only [List.length_cons]
    omega

/-- The rename scan through the final fragment `W`, which is followed by
nothing. -/
def fragEnd (b x : α) (i : Nat) : List α → List α → List (NFItem α)
  | [], W => [NFItem.frag W]
  | c :: X', w :: W' =>
      if (w :: W').take (c :: X').length = c :: X' then
        NFItem.mark i :: fragEnd b x i (c :: X') ((w :: W').drop (c :: X').length)
      else shiftItem w (fragEnd b x i (c :: X') W')
  | _ :: _, [] => []
termination_by _ W => W.length
decreasing_by
  · have h1 : 1 ≤ (c :: X').length := by simp
    have h2 : ((w :: W').drop (c :: X').length).length = (w :: W').length - (c :: X').length :=
      List.length_drop
    have h3 : 1 ≤ (w :: W').length := by simp
    omega
  · simp only [List.length_cons]
    omega

/-- Round `i` of the rename: replace every match of the code `enc2 X` by
the marker `x b^{i+1}`, marking the damage a spurious match does to a
following marker. -/
def renameNF (b x : α) (i : Nat) (X : List α) : List (NFItem α) → List (NFItem α)
  | [] => []
  | NFItem.mark j :: ns =>
      if X = [b] then NFItem.dmg [] i j :: renameNF b x i X ns
      else NFItem.mark j :: renameNF b x i X ns
  | NFItem.frag W :: NFItem.mark j :: ns =>
      fragGo b x i X W j ++ renameNF b x i X ns
  | NFItem.frag W :: ns =>
      fragEnd b x i X W ++ renameNF b x i X ns
  | NFItem.dmg A i' j :: ns => NFItem.dmg A i' j :: renameNF b x i X ns

/-- The repair pass of round `i` (pattern `X`): each damaged marker is
restored to the fragment it ate followed by the eaten marker. -/
def repairNF (b x : α) (i : Nat) (X : List α) : List (NFItem α) → List (NFItem α)
  | [] => []
  | NFItem.mark j :: ns => NFItem.mark j :: repairNF b x i X ns
  | NFItem.dmg A _ j :: ns => pushFrag A (NFItem.mark j :: repairNF b x i X ns)
  | NFItem.frag W :: NFItem.dmg A _ j :: ns =>
      NFItem.frag (W ++ A) :: NFItem.mark j :: repairNF b x i X ns
  | NFItem.frag W :: ns => NFItem.frag W :: repairNF b x i X ns

/-- The instantiation pass `k`: each marker `mark k` becomes the
fragment `Y`. -/
def instNF (b x : α) (k : Nat) (Y : List α) : List (NFItem α) → List (NFItem α)
  | [] => []
  | NFItem.frag W :: ns => NFItem.frag W :: instNF b x k Y ns
  | NFItem.mark j :: ns =>
      if j = k then pushFrag Y (instNF b x k Y ns)
      else NFItem.mark j :: instNF b x k Y ns
  | NFItem.dmg A i' j :: ns => NFItem.dmg A i' j :: instNF b x k Y ns

theorem matchHere_app_left : ∀ (P Q R R' : List α),
    matchHere Q R = some R' → matchHere (P ++ Q) (P ++ R) = some R' := by
  intro P
  induction P with
  | nil => intro Q R R' h; exact h
  | cons a P' ih =>
      intro Q R R' h
      show matchHere (a :: (P' ++ Q)) (a :: (P' ++ R)) = some R'
      rw [matchHere_cons_self]
      exact ih Q R R' h

/-- The γ-fire: when `X = W ++ [b]` and the continuation after the
fragment is marker-headed, the spurious match consumes the fragment and
the marker's head `x b`. -/
theorem gamma_fire (x b : α) (W T₃ : List α) :
    matchHere (enc2 x (W ++ [b])) (enc2 x W ++ (x :: b :: b :: T₃)) = some (b :: T₃) := by
  have h1 : enc2 x (W ++ [b]) = enc2 x W ++ [x, b] := by
    rw [enc2_append]; rfl
  have h2 : matchHere [x, b] (x :: b :: b :: T₃) = some (b :: T₃) := by
    rw [matchHere_cons_self, matchHere_cons_self]
    rfl
  rw [h1]
  exact matchHere_app_left (enc2 x W) [x, b] (x :: b :: b :: T₃) (b :: T₃) h2

omit [DecidableEq α] in
theorem take_append_self : ∀ (X W : List α), (X ++ W).take X.length = X := by
  intro X
  induction X with
  | nil => intro W; rfl
  | cons c X' ih =>
      intro W
      show (c :: (X' ++ W)).take (X'.length + 1) = c :: X'
      rw [List.take_succ_cons, ih W]

omit [DecidableEq α] in
theorem drop_append_self : ∀ (X W : List α), (X ++ W).drop X.length = W := by
  intro X
  induction X with
  | nil => intro W; rfl
  | cons c X' ih =>
      intro W
      show (c :: (X' ++ W)).drop (X'.length + 1) = W
      rw [List.drop_succ_cons, ih W]

omit [DecidableEq α] in
theorem itext_append (b x : α) : ∀ (ns₁ ns₂ : List (NFItem α)),
    itext b x (ns₁ ++ ns₂) = itext b x ns₁ ++ itext b x ns₂ := by
  intro ns₁
  induction ns₁ with
  | nil => intro ns₂; rfl
  | cons n ns ih =>
      intro ns₂
      cases n with
      | frag W => simp only [itext, List.cons_append, ih, List.append_assoc]
      | mark i => simp only [itext, List.cons_append, ih, List.append_assoc]
      | dmg W i j => simp only [itext, List.cons_append, ih, List.append_assoc]

omit [DecidableEq α] in
theorem itext_shift (b x : α) (w : α) (ns : List (NFItem α)) :
    itext b x (shiftItem w ns) = x :: w :: itext b x ns := by
  cases ns with
  | nil => simp [itext, shiftItem, enc2_head, enc2_nil]
  | cons n ns' =>
      cases n with
      | frag W => simp [itext, shiftItem, enc2_head, List.cons_append]
      | mark i => simp [itext, shiftItem, enc2_head, enc2_nil, List.cons_append]
      | dmg W i j => simp [itext, shiftItem, enc2_head, enc2_nil, List.cons_append]

omit [DecidableEq α] in
theorem itext_push (b x : α) (A : List α) (ns : List (NFItem α)) :
    itext b x (pushFrag A ns) = enc2 x A ++ itext b x ns := by
  cases ns with
  | nil =>
      by_cases hA : A = []
      · subst hA; simp [pushFrag, itext, enc2_nil]
      · simp [pushFrag, itext, hA]
  | cons n ns' =>
      cases n with
      | frag W =>
          simp only [pushFrag, itext, enc2_append, List.append_assoc]
      | mark i =>
          by_cases hA : A = []
          · subst hA; simp [pushFrag, itext, enc2_nil]
          · simp [pushFrag, itext, hA]
      | dmg W i j =>
          by_cases hA : A = []
          · subst hA; simp [pushFrag, itext, enc2_nil]
          · simp [pushFrag, itext, hA]

/-! ### Scan lemmas for the round passes

  The rename pass replaces `enc2 x X` by the round-`i` marker, the
  repair pass replaces the round-`i+1` marker by `enc2 x X ++ [b]`, and
  the instantiation pass replaces the round-`k` marker by `enc2 x Y`.
  Each pass scans left to right, so each of the three proofs below
  peels the text one character at a time; these lemmas dispose of the
  stretches where no match can start. -/

/-- A nonempty run of `a`'s cannot match a text that is empty or
headed by a different character. -/
theorem mh_rep_none (a c : α) (hac : a ≠ c) : ∀ (k : Nat), 1 ≤ k → ∀ (T : List α),
    (T = [] ∨ ∃ T', T = c :: T') → matchHere (List.replicate k a) T = none := by
  intro k hk T hT
  rcases hT with h | ⟨T', h⟩
  · subst h
    cases k with
    | zero => exact absurd hk (by omega)
    | succ k' => rfl
  · subst h
    cases k with
    | zero => exact absurd hk (by omega)
    | succ k' =>
        show matchHere (a :: List.replicate k' a) (c :: T') = none
        exact matchHere_ne a _ c T' hac

/-- If the pattern `B` never matches a text starting with `b`, a run of
`b`'s passes through the scan untouched. -/
theorem bpass (b : α) (A B : List α) (hB : ∀ C, matchHere B (b :: C) = none) :
    ∀ (m : Nat) (T : List α), subst A B (List.replicate m b ++ T)
      = List.replicate m b ++ subst A B T := by
  intro m
  induction m with
  | zero => intro T; rfl
  | succ m ih =>
      intro T
      show subst A B (b :: (List.replicate m b ++ T))
          = b :: (List.replicate m b ++ subst A B T)
      rw [subst_cons_none A B b (List.replicate m b ++ T) (hB _), ih T]

/-- The pattern `enc2 x X` never matches a text starting with `b`. -/
theorem enc2_b_none (x b : α) (hxb : x ≠ b) (X : List α) (hX : X ≠ []) (C : List α) :
    matchHere (enc2 x X) (b :: C) = none := by
  obtain ⟨c, X', hXc⟩ : ∃ c X', X = c :: X' := by
    cases X with
    | nil => exact absurd rfl hX
    | cons c X' => exact ⟨c, X', rfl⟩
  rw [hXc, enc2_head]
  exact matchHere_ne x _ b C hxb

omit [DecidableEq α] in
/-- The code of a nonempty pattern is nonempty. -/
theorem enc2_ne_nil (x : α) (X : List α) (hX : X ≠ []) : enc2 x X ≠ [] := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' => simp [enc2_head]

/-- A marker passes through the rename scan untouched when the pattern
is neither `[]` nor the single character `b`. -/
theorem markpass (x b : α) (hxb : x ≠ b) (A : List α) (X : List α) (hX : X ≠ [])
    (hXb : X ≠ [b]) (j : Nat) (hj : 1 ≤ j) (T : List α) :
    subst A (enc2 x X) (marker x b (j + 1) ++ T)
      = marker x b (j + 1) ++ subst A (enc2 x X) T := by
  have hB := enc2_b_none x b hxb X hX
  cases j with
  | zero => exact absurd hj (by omega)
  | succ j' =>
      have hE : marker x b (j' + 1 + 1) ++ T = x :: (List.replicate (j' + 1 + 1) b ++ T) := rfl
      have hM : matchHere (enc2 x X) (x :: (List.replicate (j' + 1 + 1) b ++ T)) = none :=
        mark_none x b hxb X (List.replicate j' b ++ T) hX hXb
      rw [hE, subst_cons_none A (enc2 x X) x _ hM, bpass b A (enc2 x X) hB]
      rfl

/-! ### The rename scan through one fragment -/

omit [DecidableEq α] in
theorem take_drop_id : ∀ (k : Nat) (l : List α), l.take k ++ l.drop k = l := by
  intro k
  induction k with
  | zero => intro l; rfl
  | succ k ih =>
      intro l
      cases l with
      | nil => rfl
      | cons a l' =>
          show (a :: l'.take k) ++ l'.drop k = a :: l'
          rw [List.cons_append, ih l']

/-- Unfolding `fragGo` at a nonempty fragment. -/
theorem fragGo_cons (b x : α) (i : Nat) (c : α) (X' : List α) (w : α) (W' : List α) (j : Nat) :
    fragGo b x i (c :: X') (w :: W') j =
      if (w :: W').take (c :: X').length = c :: X' then
        NFItem.mark i :: fragGo b x i (c :: X') ((w :: W').drop (c :: X').length) j
      else if (c :: X') = (w :: W') ++ [b] then [NFItem.dmg (w :: W') i j]
      else shiftItem w (fragGo b x i (c :: X') W' j) := by
  simp only [fragGo]

/-- Unfolding `fragGo` at an exhausted fragment. -/
theorem fragGo_end (b x : α) (i : Nat) (c : α) (X' : List α) (j : Nat) :
    fragGo b x i (c :: X') [] j =
      if (c :: X') = [b] then [NFItem.dmg [] i j] else [NFItem.mark j] := by
  simp only [fragGo]

/-- The alpha-branch of `fragGo`: the pattern is a prefix of the
remaining fragment, so the round-`i` marker is emitted and the scan
continues inside the fragment. -/
theorem fragGo_alpha (b x : α) (i : Nat) (c : α) (X' : List α) (w : α) (W' : List α) (j : Nat)
    (hα : (w :: W').take (c :: X').length = c :: X') :
    fragGo b x i (c :: X') (w :: W') j
      = NFItem.mark i :: fragGo b x i (c :: X') ((w :: W').drop (c :: X').length) j := by
  rw [fragGo_cons]
  split
  · rfl
  · next h => exact absurd hα h

/-- The gamma-branch of `fragGo`: the pattern is the remaining fragment
plus one `b`, so the match eats into the following marker and leaves a
damaged marker. -/
theorem fragGo_gamma (b x : α) (i : Nat) (c : α) (X' : List α) (w : α) (W' : List α) (j : Nat)
    (hα : ¬((w :: W').take (c :: X').length = c :: X'))
    (hγ : (c :: X') = (w :: W') ++ [b]) :
    fragGo b x i (c :: X') (w :: W') j = [NFItem.dmg (w :: W') i j] := by
  rw [fragGo_cons]
  split
  · next h => exact absurd h hα
  · rfl

/-- The skip-branch of `fragGo`: no match at the fragment head, so the
first block is kept and the scan moves on. -/
theorem fragGo_skip (b x : α) (i : Nat) (c : α) (X' : List α) (w : α) (W' : List α) (j : Nat)
    (hα : ¬((w :: W').take (c :: X').length = c :: X'))
    (hγ : ¬((c :: X') = (w :: W') ++ [b])) :
    fragGo b x i (c :: X') (w :: W') j = shiftItem w (fragGo b x i (c :: X') W' j) := by
  rw [fragGo_cons]
  split
  · next h => exact absurd h hα
  · rfl

omit [DecidableEq α] in
/-- The text of a nonempty fragment followed by a tail, as a cons of its
first block. -/
theorem frag_cons_text (x : α) (w : α) (W' T : List α) :
    enc2 x (w :: W') ++ T = x :: (w :: (enc2 x W' ++ T)) := by
  simp [enc2_head]

omit [DecidableEq α] in
/-- If the first `k` characters of `l` are `P`, then `l` splits at `k`
into `P` and the rest. -/
theorem take_eq_split : ∀ (k : Nat) (l P : List α), l.take k = P → l = P ++ l.drop k := by
  intro k l P h
  have htd := take_drop_id k l
  rw [h] at htd
  exact htd.symm

/-- The rename scan at an exhausted fragment: the next item is the
marker `mark j`, so the scan either fires into the marker's head (the
pattern is exactly `[b]`) or passes the whole marker through. -/
theorem fragGo_end_scan (x b : α) (hxb : x ≠ b) (i : Nat) (X : List α) (hX : X ≠ [])
    (j : Nat) (hj : 1 ≤ j) (ns : List (NFItem α))
    (hNS : subst (marker x b (i + 1)) (enc2 x X) (itext b x ns)
      = itext b x (renameNF b x i X ns)) :
    subst (marker x b (i + 1)) (enc2 x X) (marker x b (j + 1) ++ itext b x ns)
      = itext b x (fragGo b x i X [] j ++ renameNF b x i X ns) := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
    by_cases hXb : (c :: X') = [b]
    · rw [hXb] at hNS ⊢
      have hcon : marker x b (j + 1) ++ itext b x ns
          = x :: (List.replicate (j + 1) b ++ itext b x ns) := rfl
      have hB : ∀ C, matchHere (enc2 x [b]) (b :: C) = none :=
        enc2_b_none x b hxb [b] (by simp)
      rw [hcon, subst_cons_match (marker x b (i + 1)) (enc2 x [b]) (by simp [enc2]) x
          (List.replicate (j + 1) b ++ itext b x ns) (List.replicate j b ++ itext b x ns)
          (mark_fire x b j (itext b x ns)),
        bpass b (marker x b (i + 1)) (enc2 x [b]) hB j (itext b x ns), hNS,
        show fragGo b x i [b] [] j = [NFItem.dmg [] i j] from by
          rw [fragGo_end]; simp]
      show marker x b (i + 1) ++ (List.replicate j b ++ itext b x (renameNF b x i [b] ns))
          = (marker x b (i + 1) ++ List.replicate j b) ++ itext b x (renameNF b x i [b] ns)
      exact (List.append_assoc _ _ _).symm
    · rw [markpass x b hxb (marker x b (i + 1)) (c :: X') hX hXb j hj (itext b x ns), hNS,
        show fragGo b x i (c :: X') [] j = [NFItem.mark j] from by
          rw [fragGo_end]; simp [hXb]]
      rfl

/-- The rename scan through the fragment `W` followed by the marker
`mark j` (round `j ≥ 1`): the round-`i` substitution over the fragment
text plus the marker produces exactly `fragGo`'s output followed by the
scan of whatever follows the marker.  Proven by strong induction on the
fragment: an alpha-match restarts after the match inside the fragment,
a gamma-match eats into the marker and stops, and otherwise the scan
moves one block on. -/
theorem fragGo_scan (x b : α) (hxb : x ≠ b) (i : Nat) (X : List α) (hX : X ≠ []) :
    ∀ (n : Nat) (W : List α), W.length ≤ n → ∀ (j : Nat) (ns : List (NFItem α)), 1 ≤ j →
    subst (marker x b (i + 1)) (enc2 x X) (itext b x ns)
      = itext b x (renameNF b x i X ns) →
    subst (marker x b (i + 1)) (enc2 x X) (enc2 x W ++ (marker x b (j + 1) ++ itext b x ns))
      = itext b x (fragGo b x i X W j ++ renameNF b x i X ns) := by
  intro n
  induction n with
  | zero =>
      intro W hW j ns hj hNS
      cases W with
      | nil =>
          show subst (marker x b (i + 1)) (enc2 x X) (marker x b (j + 1) ++ itext b x ns)
              = itext b x (fragGo b x i X [] j ++ renameNF b x i X ns)
          exact fragGo_end_scan x b hxb i X hX j hj ns hNS
      | cons w W' =>
          have h1 : 1 ≤ (w :: W').length := by simp
          omega
  | succ n ih =>
      intro W hW j ns hj hNS
      cases j with
      | zero => exact absurd hj (by omega)
      | succ j' =>
      cases X with
      | nil => exact absurd rfl hX
      | cons c X' =>
      cases W with
      | nil =>
          show subst (marker x b (i + 1)) (enc2 x (c :: X'))
              (marker x b (j' + 1 + 1) ++ itext b x ns)
              = itext b x (fragGo b x i (c :: X') [] (j' + 1)
                  ++ renameNF b x i (c :: X') ns)
          exact fragGo_end_scan x b hxb i (c :: X') hX (j' + 1) (by omega) ns hNS
      | cons w W' =>
          have hcon : enc2 x (w :: W') ++ (marker x b (j' + 1 + 1) ++ itext b x ns)
              = x :: (w :: (enc2 x W' ++ (marker x b (j' + 1 + 1) ++ itext b x ns))) :=
            frag_cons_text x w W' _
          by_cases hα : (w :: W').take (c :: X').length = c :: X'
          · have hsplit : w :: W' = (c :: X') ++ (w :: W').drop (c :: X').length :=
              take_eq_split _ _ _ hα
            have hM : matchHere (enc2 x (c :: X'))
                (enc2 x ((c :: X') ++ (w :: W').drop (c :: X').length)
                  ++ (marker x b (j' + 1 + 1) ++ itext b x ns))
                = some (enc2 x ((w :: W').drop (c :: X').length)
                  ++ (marker x b (j' + 1 + 1) ++ itext b x ns)) :=
              aligned_fire x (c :: X') ((w :: W').drop (c :: X').length)
                (marker x b (j' + 1 + 1) ++ itext b x ns)
            rw [← hsplit] at hM
            have hlen₂ : ((w :: W').drop (c :: X').length).length ≤ n := by
              have h1 : ((w :: W').drop (c :: X').length).length
                  = (w :: W').length - (c :: X').length := List.length_drop
              have h2 : 1 ≤ (c :: X').length := by simp
              omega
            rw [hcon, subst_cons_match (marker x b (i + 1)) (enc2 x (c :: X'))
                (enc2_ne_nil x (c :: X') hX) x
                (w :: (enc2 x W' ++ (marker x b (j' + 1 + 1) ++ itext b x ns)))
                (enc2 x ((w :: W').drop (c :: X').length)
                  ++ (marker x b (j' + 1 + 1) ++ itext b x ns)) hM,
              ih ((w :: W').drop (c :: X').length) hlen₂ (j' + 1) ns (by omega) hNS,
              fragGo_alpha b x i c X' w W' (j' + 1) hα]
            rfl
          · by_cases hγ : (c :: X') = (w :: W') ++ [b]
            · have hM : matchHere (enc2 x (c :: X'))
                  (enc2 x (w :: W') ++ (marker x b (j' + 1 + 1) ++ itext b x ns))
                  = some (b :: (List.replicate j' b ++ itext b x ns)) := by
                rw [hγ]
                exact gamma_fire x b (w :: W') (List.replicate j' b ++ itext b x ns)
              have hB := enc2_b_none x b hxb (c :: X') hX
              rw [hcon, subst_cons_match (marker x b (i + 1)) (enc2 x (c :: X'))
                  (enc2_ne_nil x (c :: X') hX) x
                  (w :: (enc2 x W' ++ (marker x b (j' + 1 + 1) ++ itext b x ns)))
                  (b :: (List.replicate j' b ++ itext b x ns)) hM,
                subst_cons_none (marker x b (i + 1)) (enc2 x (c :: X')) b
                  (List.replicate j' b ++ itext b x ns) (hB _),
                bpass b (marker x b (i + 1)) (enc2 x (c :: X')) hB j' (itext b x ns), hNS,
                fragGo_gamma b x i c X' w W' (j' + 1) hα hγ]
              show marker x b (i + 1) ++ (List.replicate (j' + 1) b
                  ++ itext b x (renameNF b x i (c :: X') ns))
                  = (marker x b (i + 1) ++ List.replicate (j' + 1) b)
                    ++ itext b x (renameNF b x i (c :: X') ns)
              exact (List.append_assoc _ _ _).symm
            · have hT : marker x b (j' + 1 + 1) ++ itext b x ns
                  = x :: b :: b :: (List.replicate j' b ++ itext b x ns) := rfl
              have hT2 : marker x b (j' + 1 + 1) ++ itext b x ns
                  = x :: b :: (List.replicate (j' + 1) b ++ itext b x ns) := rfl
              have hA : matchHere (enc2 x (c :: X'))
                  (enc2 x (w :: W') ++ (marker x b (j' + 1 + 1) ++ itext b x ns)) = none := by
                cases hM : matchHere (enc2 x (c :: X'))
                    (enc2 x (w :: W') ++ (marker x b (j' + 1 + 1) ++ itext b x ns)) with
                | none => rfl
                | some D =>
                    rcases aligned_class x b hxb (w :: W') (c :: X')
                      (marker x b (j' + 1 + 1) ++ itext b x ns) D
                      (Or.inr ⟨List.replicate j' b ++ itext b x ns, hT⟩) hM with
                    ⟨W₂, hsplit, _⟩ | ⟨T₃, _, hXeq, _⟩
                    · exact absurd (by rw [hsplit]; exact take_append_self (c :: X') W₂) hα
                    · exact absurd hXeq hγ
              have hβ := beta_skip x b hxb (c :: X') w W'
                (marker x b (j' + 1 + 1) ++ itext b x ns) (Or.inr ⟨_, hT2⟩) hA
              have hlen₁ : W'.length ≤ n := by
                have h1 : (w :: W').length = W'.length + 1 := by simp
                omega
              rw [hcon,
                subst_cons_none (marker x b (i + 1)) (enc2 x (c :: X')) x
                  (w :: (enc2 x W' ++ (marker x b (j' + 1 + 1) ++ itext b x ns))) hA,
                subst_cons_none (marker x b (i + 1)) (enc2 x (c :: X')) w
                  (enc2 x W' ++ (marker x b (j' + 1 + 1) ++ itext b x ns)) hβ,
                ih W' hlen₁ (j' + 1) ns (by omega) hNS,
                fragGo_skip b x i c X' w W' (j' + 1) hα hγ]
              simp only [itext_append, itext_shift, List.cons_append]

/-- Unfolding `fragEnd` at a nonempty fragment: the alpha-branch. -/
theorem fragEnd_alpha (b x : α) (i : Nat) (c : α) (X' : List α) (w : α) (W' : List α)
    (hα : (w :: W').take (c :: X').length = c :: X') :
    fragEnd b x i (c :: X') (w :: W')
      = NFItem.mark i :: fragEnd b x i (c :: X') ((w :: W').drop (c :: X').length) := by
  simp only [fragEnd]
  split
  · rfl
  · next h => exact absurd hα h

/-- Unfolding `fragEnd` at a nonempty fragment: the skip-branch. -/
theorem fragEnd_skip (b x : α) (i : Nat) (c : α) (X' : List α) (w : α) (W' : List α)
    (hα : ¬((w :: W').take (c :: X').length = c :: X')) :
    fragEnd b x i (c :: X') (w :: W') = shiftItem w (fragEnd b x i (c :: X') W') := by
  simp only [fragEnd]
  split
  · next h => exact absurd h hα
  · rfl

/-- The rename scan through the final fragment (followed by nothing):
the round-`i` substitution over the fragment text is exactly
`fragEnd`'s output.  Strong induction on the fragment: there is no
gamma-fire here because nothing follows the fragment. -/
theorem fragEnd_scan (x b : α) (hxb : x ≠ b) (i : Nat) (X : List α) (hX : X ≠ []) :
    ∀ (n : Nat) (W : List α), W.length ≤ n →
    subst (marker x b (i + 1)) (enc2 x X) (enc2 x W) = itext b x (fragEnd b x i X W) := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
  intro n
  induction n with
  | zero =>
      intro W hW
      cases W with
      | nil =>
          have hfe : fragEnd b x i (c :: X') [] = [] := by simp only [fragEnd]
          rw [hfe]
          show subst (marker x b (i + 1)) (enc2 x (c :: X')) [] = itext b x []
          rw [subst_nil]
          rfl
      | cons w W' =>
          have h1 : 1 ≤ (w :: W').length := by simp
          omega
  | succ n ih =>
      intro W hW
      cases W with
      | nil =>
          have hfe : fragEnd b x i (c :: X') [] = [] := by simp only [fragEnd]
          rw [hfe]
          show subst (marker x b (i + 1)) (enc2 x (c :: X')) [] = itext b x []
          rw [subst_nil]
          rfl
      | cons w W' =>
          have hcon : enc2 x (w :: W') = x :: (w :: enc2 x W') := enc2_head x w W'
          by_cases hα : (w :: W').take (c :: X').length = c :: X'
          · have hsplit : w :: W' = (c :: X') ++ (w :: W').drop (c :: X').length :=
              take_eq_split _ _ _ hα
            have hM : matchHere (enc2 x (c :: X')) (enc2 x (w :: W'))
                = some (enc2 x ((w :: W').drop (c :: X').length)) := by
              have h0 := aligned_fire x (c :: X') ((w :: W').drop (c :: X').length) []
              rw [← hsplit] at h0
              simp only [List.append_nil] at h0
              exact h0
            have hlen₂ : ((w :: W').drop (c :: X').length).length ≤ n := by
              have h1 : ((w :: W').drop (c :: X').length).length
                  = (w :: W').length - (c :: X').length := List.length_drop
              have h2 : 1 ≤ (c :: X').length := by simp
              omega
            rw [hcon, subst_cons_match (marker x b (i + 1)) (enc2 x (c :: X'))
                (enc2_ne_nil x (c :: X') hX) x (w :: enc2 x W')
                (enc2 x ((w :: W').drop (c :: X').length)) hM,
              ih ((w :: W').drop (c :: X').length) hlen₂,
              fragEnd_alpha b x i c X' w W' hα]
            rfl
          · have hA : matchHere (enc2 x (c :: X')) (enc2 x (w :: W')) = none := by
              cases hM : matchHere (enc2 x (c :: X')) (enc2 x (w :: W')) with
              | none => rfl
              | some D =>
                  have hM2 : matchHere (enc2 x (c :: X')) (enc2 x (w :: W') ++ [])
                      = some D := by rw [List.append_nil]; exact hM
                  rcases aligned_class x b hxb (w :: W') (c :: X') [] D (Or.inl rfl) hM2 with
                  ⟨W₂, hsplit, _⟩ | ⟨T₃, hTeq, hXeq, _⟩
                  · exact absurd (by rw [hsplit]; exact take_append_self (c :: X') W₂) hα
                  · exact nomatch hTeq
            have hA2 : matchHere (enc2 x (c :: X')) (enc2 x (w :: W') ++ []) = none := by
              rw [List.append_nil]; exact hA
            have hβ0 := beta_skip x b hxb (c :: X') w W' [] (Or.inl rfl) hA2
            have hβ : matchHere (enc2 x (c :: X')) (w :: enc2 x W') = none := by
              rw [← List.append_nil (enc2 x W')]; exact hβ0
            have hlen₁ : W'.length ≤ n := by
              have h1 : (w :: W').length = W'.length + 1 := by simp
              omega
            rw [hcon,
              subst_cons_none (marker x b (i + 1)) (enc2 x (c :: X')) x (w :: enc2 x W') hA,
              subst_cons_none (marker x b (i + 1)) (enc2 x (c :: X')) w (enc2 x W') hβ,
              ih W' hlen₁,
              fragEnd_skip b x i c X' w W' hα]
            simp only [itext_shift]

/-- Unfolding `renameNF` at a marker. -/
theorem renameNF_mark (b x : α) (i : Nat) (X : List α) (j : Nat) (ns : List (NFItem α)) :
    renameNF b x i X (NFItem.mark j :: ns)
      = if X = [b] then NFItem.dmg [] i j :: renameNF b x i X ns
        else NFItem.mark j :: renameNF b x i X ns := by
  simp only [renameNF]

/-- Unfolding `renameNF` at a fragment followed by a marker. -/
theorem renameNF_frag_mark (b x : α) (i : Nat) (X : List α) (W : List α) (j : Nat)
    (ns : List (NFItem α)) :
    renameNF b x i X (NFItem.frag W :: NFItem.mark j :: ns)
      = fragGo b x i X W j ++ renameNF b x i X ns := by
  simp only [renameNF]

/-- Unfolding `renameNF` at a final fragment. -/
theorem renameNF_frag_nil (b x : α) (i : Nat) (X : List α) (W : List α) :
    renameNF b x i X (NFItem.frag W :: []) = fragEnd b x i X W := by
  simp only [renameNF, List.append_nil]

/-- The rename pass of round `i` over a canonical item list: the
substitution over the flat text is exactly `renameNF`'s output.  The
list is processed item by item; each fragment scan is `fragGo_scan` or
`fragEnd_scan`, and each marker either passes through or -- when the
pattern is exactly `[b]` -- fires into the marker's head. -/
theorem renameNF_scan (x b : α) (hxb : x ≠ b) (i : Nat) (X : List α) (hX : X ≠ []) :
    ∀ (n : Nat) (ns : List (NFItem α)), ns.length ≤ n → CanonB (i - 1) ns →
    subst (marker x b (i + 1)) (enc2 x X) (itext b x ns)
      = itext b x (renameNF b x i X ns) := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
  intro n
  induction n with
  | zero =>
      intro ns hns hC
      cases ns with
      | nil =>
          show subst (marker x b (i + 1)) (enc2 x (c :: X')) [] = []
          rw [subst_nil]
      | cons m ns' =>
          have h1 : 1 ≤ (m :: ns').length := by simp
          omega
  | succ n ih =>
      intro ns hns hC
      cases ns with
      | nil =>
          show subst (marker x b (i + 1)) (enc2 x (c :: X')) [] = []
          rw [subst_nil]
      | cons m ns' =>
      cases m with
      | mark j =>
          obtain ⟨hj, _, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.mark j :: ns').length = ns'.length + 1 := by simp
            omega
          have hit : itext b x (NFItem.mark j :: ns')
              = marker x b (j + 1) ++ itext b x ns' := rfl
          by_cases hXb : (c :: X') = [b]
          · have hR := fragGo_end_scan x b hxb i (c :: X') hX j hj ns' (ih ns' hns' hC')
            rw [fragGo_end, ite_eq_left hXb] at hR
            rw [renameNF_mark, ite_eq_left hXb, hit]
            exact hR
          · rw [renameNF_mark, ite_eq_right hXb, hit,
              markpass x b hxb (marker x b (i + 1)) (c :: X') hX hXb j hj (itext b x ns'),
              ih ns' hns' hC']
            rfl
      | frag W =>
          cases ns' with
          | nil =>
              have hit : itext b x (NFItem.frag W :: []) = enc2 x W := by simp [itext]
              rw [renameNF_frag_nil, hit]
              exact fragEnd_scan x b hxb i (c :: X') hX W.length W (Nat.le_refl _)
          | cons m2 ns'' =>
              cases m2 with
              | frag W2 => exact hC.elim
              | dmg A i2 j2 => exact hC.elim
              | mark j =>
                  obtain ⟨hW, hj, _, hC''⟩ := hC
                  have hns'' : ns''.length ≤ n := by
                    have h1 : (NFItem.frag W :: NFItem.mark j :: ns'').length
                        = ns''.length + 2 := by simp
                    omega
                  have hit : itext b x (NFItem.frag W :: NFItem.mark j :: ns'')
                      = enc2 x W ++ (marker x b (j + 1) ++ itext b x ns'') := rfl
                  rw [renameNF_frag_mark, hit]
                  exact fragGo_scan x b hxb i (c :: X') hX W.length W (Nat.le_refl _) j ns'' hj
                    (ih ns'' hns'' hC'')
      | dmg A i2 j2 => exact hC.elim

omit [DecidableEq α] in
/-- `shiftItem` never returns an empty list. -/
theorem shiftItem_ne (w : α) : ∀ L : List (NFItem α), shiftItem w L ≠ [] := by
  intro L
  cases L with
  | nil => simp [shiftItem]
  | cons n L' =>
      cases n with
      | frag W => simp [shiftItem]
      | mark i => simp [shiftItem]
      | dmg W i j => simp [shiftItem]

omit [DecidableEq α] in
/-- `shiftItem` commutes with appending a tail, on nonempty lists. -/
theorem shiftItem_append (w : α) : ∀ (L M : List (NFItem α)), L ≠ [] →
    shiftItem w L ++ M = shiftItem w (L ++ M) := by
  intro L
  cases L with
  | nil => intro M h; exact absurd rfl h
  | cons n L' =>
      cases n with
      | frag W => intro M _; rfl
      | mark i => intro M _; rfl
      | dmg W i j => intro M _; rfl

/-- `fragGo` never returns an empty list (for nonempty patterns). -/
theorem fragGo_ne (b x : α) (i : Nat) (X : List α) (hX : X ≠ []) :
    ∀ (n : Nat) (W : List α), W.length ≤ n → ∀ j : Nat, fragGo b x i X W j ≠ [] := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
  intro n
  induction n with
  | zero =>
      intro W hW j
      cases W with
      | nil =>
          intro h
          rw [fragGo_end] at h
          split at h
          · exact nomatch h
          · exact nomatch h
      | cons w W' =>
          have h1 : 1 ≤ (w :: W').length := by simp
          omega
  | succ n ih =>
      intro W hW j
      cases W with
      | nil =>
          intro h
          rw [fragGo_end] at h
          split at h
          · exact nomatch h
          · exact nomatch h
      | cons w W' =>
          by_cases hα : (w :: W').take (c :: X').length = c :: X'
          · intro h
            rw [fragGo_alpha b x i c X' w W' j hα] at h
            exact nomatch h
          · by_cases hγ : (c :: X') = (w :: W') ++ [b]
            · intro h
              rw [fragGo_gamma b x i c X' w W' j hα hγ] at h
              exact nomatch h
            · intro h
              rw [fragGo_skip b x i c X' w W' j hα hγ] at h
              exact shiftItem_ne w _ h

omit [DecidableEq α] in
/-- Shifting a block onto a rounded list keeps it rounded. -/
theorem rounded_shift (b : α) (i : Nat) (X : List α) (w : α) : ∀ ns : List (NFItem α),
    Rounded b i X ns → Rounded b i X (shiftItem w ns) := by
  intro ns hC
  cases ns with
  | nil => exact (by simp : ([w] : List α) ≠ [])
  | cons n ns' =>
      cases n with
      | frag W =>
          cases ns' with
          | nil => exact (by simp : (w :: W : List α) ≠ [])
          | cons m ns'' =>
              cases m with
              | frag W2 => exact hC.elim
              | mark j => exact ⟨by simp, hC.2.1, hC.2.2.1, hC.2.2.2⟩
              | dmg A i2 j2 =>
                  exact ⟨by simp, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1,
                    hC.2.2.2.2.2⟩
      | mark j => exact ⟨by simp, hC.1, hC.2.1, hC.2.2⟩
      | dmg A i2 j2 =>
          exact ⟨by simp, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2⟩

/-- The rename scan through a fragment keeps the list rounded, whatever
rounded material follows; the scan always ends in the trailing marker
or a damaged marker. -/
theorem fragGo_rounded (b x : α) (i : Nat) (X : List α) (hX : X ≠ []) :
    1 ≤ i → ∀ (n : Nat) (W : List α), W.length ≤ n → ∀ (j : Nat), 1 ≤ j → j ≤ i →
    ∀ M : List (NFItem α), Rounded b i X M →
    Rounded b i X (fragGo b x i X W j ++ M) := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
  intro hi n
  induction n with
  | zero =>
      intro W hW j hj hjm M hM
      cases W with
      | nil =>
          rw [fragGo_end]
          split
          · next h => exact ⟨rfl, hj, hjm, h, hM⟩
          · exact ⟨hj, hjm, hM⟩
      | cons w W' =>
          have h1 : 1 ≤ (w :: W').length := by simp
          omega
  | succ n ih =>
      intro W hW j hj hjm M hM
      cases W with
      | nil =>
          rw [fragGo_end]
          split
          · next h => exact ⟨rfl, hj, hjm, h, hM⟩
          · exact ⟨hj, hjm, hM⟩
      | cons w W' =>
          by_cases hα : (w :: W').take (c :: X').length = c :: X'
          · rw [fragGo_alpha b x i c X' w W' j hα, List.cons_append]
            exact ⟨hi, Nat.le_refl i,
              ih ((w :: W').drop (c :: X').length) (by
                    have h1 : ((w :: W').drop (c :: X').length).length
                        = (w :: W').length - (c :: X').length := List.length_drop
                    have h2 : 1 ≤ (c :: X').length := by simp
                    omega) j hj hjm M hM⟩
          · by_cases hγ : (c :: X') = (w :: W') ++ [b]
            · rw [fragGo_gamma b x i c X' w W' j hα hγ, List.cons_append]
              exact ⟨rfl, hj, hjm, hγ, hM⟩
            · rw [fragGo_skip b x i c X' w W' j hα hγ,
                shiftItem_append w _ _ (fragGo_ne b x i (c :: X') hX W'.length W'
                  (by
                    have h1 : (w :: W').length = W'.length + 1 := by simp
                    omega) j)]
              exact rounded_shift b i (c :: X') w _ (ih W' (by
                have h1 : (w :: W').length = W'.length + 1 := by simp
                omega) j hj hjm M hM)

/-- The rename scan through a final fragment keeps the list rounded. -/
theorem fragEnd_rounded (b x : α) (i : Nat) (X : List α) (hX : X ≠ []) :
    1 ≤ i → ∀ (n : Nat) (W : List α), W.length ≤ n →
    Rounded b i X (fragEnd b x i X W) := by
  cases X with
  | nil => exact absurd rfl hX
  | cons c X' =>
  intro hi n
  induction n with
  | zero =>
      intro W hW
      cases W with
      | nil =>
          have hfe : fragEnd b x i (c :: X') [] = [] := by simp only [fragEnd]
          rw [hfe]
          exact (by trivial : Rounded b i (c :: X') [])
      | cons w W' =>
          have h1 : 1 ≤ (w :: W').length := by simp
          omega
  | succ n ih =>
      intro W hW
      cases W with
      | nil =>
          have hfe : fragEnd b x i (c :: X') [] = [] := by simp only [fragEnd]
          rw [hfe]
          exact (by trivial : Rounded b i (c :: X') [])
      | cons w W' =>
          by_cases hα : (w :: W').take (c :: X').length = c :: X'
          · rw [fragEnd_alpha b x i c X' w W' hα]
            exact ⟨hi, Nat.le_refl i,
              ih ((w :: W').drop (c :: X').length) (by
                have h1 : ((w :: W').drop (c :: X').length).length
                    = (w :: W').length - (c :: X').length := List.length_drop
                have h2 : 1 ≤ (c :: X').length := by simp
                omega)⟩
          · rw [fragEnd_skip b x i c X' w W' hα]
            exact rounded_shift b i (c :: X') w _ (ih W' (by
              have h1 : (w :: W').length = W'.length + 1 := by simp
              omega))

/-- The rename pass of round `i` turns a canonical list (markers at
most `i - 1`) into a rounded one (markers at most `i`, damaged markers
of round `i`). -/
theorem renameNF_rounded (b x : α) (i : Nat) (X : List α) (hX : X ≠ []) :
    1 ≤ i → ∀ (n : Nat) (ns : List (NFItem α)), ns.length ≤ n → CanonB (i - 1) ns →
    Rounded b i X (renameNF b x i X ns) := by
  intro hi n
  induction n with
  | zero =>
      intro ns hns hC
      cases ns with
      | nil => exact (by trivial : Rounded b i X [])
      | cons m ns' =>
          have h1 : 1 ≤ (m :: ns').length := by simp
          omega
  | succ n ih =>
      intro ns hns hC
      cases ns with
      | nil => exact (by trivial : Rounded b i X [])
      | cons m ns' =>
      cases m with
      | mark j =>
          obtain ⟨hj, hjm, hC'⟩ := hC
          have hji : j ≤ i := by omega
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.mark j :: ns').length = ns'.length + 1 := by simp
            omega
          rw [renameNF_mark]
          split
          · next h => exact ⟨rfl, hj, hji, h, ih ns' hns' hC'⟩
          · exact ⟨hj, hji, ih ns' hns' hC'⟩
      | frag W =>
          cases ns' with
          | nil =>
              rw [renameNF_frag_nil]
              exact fragEnd_rounded b x i X hX hi W.length W (Nat.le_refl _)
          | cons m2 ns'' =>
              cases m2 with
              | frag W2 => exact hC.elim
              | dmg A i2 j2 => exact hC.elim
              | mark j =>
                  obtain ⟨hW, hj, hjm, hC''⟩ := hC
                  have hji : j ≤ i := by omega
                  have hns'' : ns''.length ≤ n := by
                    have h1 : (NFItem.frag W :: NFItem.mark j :: ns'').length
                        = ns''.length + 2 := by simp
                    omega
                  rw [renameNF_frag_mark]
                  exact fragGo_rounded b x i X hX hi W.length W (Nat.le_refl _) j hj hji
                    (renameNF b x i X ns'') (ih ns'' hns'' hC'')
      | dmg A i2 j2 => exact hC.elim

/-- A shorter run of `a`'s cannot match a longer run followed by an
empty or differently-headed text. -/
theorem mh_brun (a c : α) (hac : a ≠ c) : ∀ (K M : Nat), M < K → ∀ (T : List α),
    (T = [] ∨ ∃ T', T = c :: T') →
    matchHere (List.replicate K a) (List.replicate M a ++ T) = none := by
  intro K
  induction K with
  | zero => intro M hM T hT; omega
  | succ K ih =>
      intro M hM T hT
      match M, hM with
      | 0, _ =>
          have h1 : 1 ≤ K + 1 := by omega
          exact mh_rep_none a c hac (K + 1) h1 T hT
      | M + 1, _ =>
          have hstep : matchHere (List.replicate (K + 1) a) (List.replicate (M + 1) a ++ T)
              = matchHere (List.replicate K a) (List.replicate M a ++ T) := by
            show matchHere (a :: List.replicate K a) (a :: (List.replicate M a ++ T))
                = matchHere (List.replicate K a) (List.replicate M a ++ T)
            rw [matchHere_cons_self]
          rw [hstep]
          exact ih M (by omega) T hT

/-- A run of `a`'s matches a longer run, leaving the difference. -/
theorem mh_run_fire (a : α) : ∀ (K N : Nat), K ≤ N → ∀ (T : List α),
    matchHere (List.replicate K a) (List.replicate N a ++ T)
      = some (List.replicate (N - K) a ++ T) := by
  intro K
  induction K with
  | zero => intro N _ T; rfl
  | succ K ih =>
      intro N hN T
      cases N with
      | zero => omega
      | succ N =>
          have hstep : matchHere (List.replicate (K + 1) a) (List.replicate (N + 1) a ++ T)
              = matchHere (List.replicate K a) (List.replicate N a ++ T) := by
            show matchHere (a :: List.replicate K a) (a :: (List.replicate N a ++ T))
                = matchHere (List.replicate K a) (List.replicate N a ++ T)
            rw [matchHere_cons_self]
          rw [hstep, ih N (by omega) T]
          have hsub : N + 1 - (K + 1) = N - K := by omega
          rw [hsub]

omit [DecidableEq α] in
/-- If a tail is empty or `x`-headed, so is an `enc2`-image followed by
it. -/
theorem enc2_T_cond (x : α) : ∀ (W' T : List α), (T = [] ∨ ∃ T', T = x :: T') →
    (enc2 x W' ++ T = [] ∨ ∃ R, enc2 x W' ++ T = x :: R) := by
  intro W' T hT
  cases W' with
  | nil => exact hT
  | cons w W'' =>
      refine Or.inr ⟨w :: (enc2 x W'' ++ T), ?_⟩
      show (x :: w :: enc2 x W'') ++ T = _
      rfl

omit [DecidableEq α] in
/-- A rounded list headed by a fragment keeps a rounded tail and a
nonempty fragment. -/
theorem rounded_frag_tail {b : α} {i : Nat} {X W : List α} {ns : List (NFItem α)}
    (hC : Rounded b i X (NFItem.frag W :: ns)) : W ≠ [] ∧ Rounded b i X ns := by
  cases ns with
  | nil => exact ⟨hC, trivial⟩
  | cons m ns' =>
      cases m with
      | frag W2 => exact hC.elim
      | mark j => exact ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2⟩
      | dmg A i2 j2 =>
          exact ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1, hC.2.2.2.2.2⟩

omit [DecidableEq α] in
/-- Every fragment of a rounded list is nonempty. -/
theorem rounded_fragsNE (b : α) (i : Nat) (X : List α) : ∀ ns : List (NFItem α),
    Rounded b i X ns → fragsNE ns := by
  intro ns
  induction ns with
  | nil => intro _; exact trivial
  | cons m ns' ih =>
      intro hC
      cases m with
      | frag W =>
          obtain ⟨hW, hC'⟩ := rounded_frag_tail hC
          exact ⟨hW, ih hC'⟩
      | mark j => exact ih hC.2.2
      | dmg A i2 j2 => exact ih hC.2.2.2.2

omit [DecidableEq α] in
/-- The flat text of a list with nonempty fragments is empty or
`x`-headed. -/
theorem itext_head (b x : α) : ∀ ns : List (NFItem α), fragsNE ns →
    itext b x ns = [] ∨ ∃ T, itext b x ns = x :: T := by
  intro ns
  induction ns with
  | nil => intro _; exact Or.inl rfl
  | cons m ns' ih =>
      intro hF
      cases m with
      | frag W =>
          obtain ⟨hW, hF'⟩ := hF
          cases W with
          | nil => exact absurd rfl hW
          | cons w W'' =>
              refine Or.inr ⟨w :: (enc2 x W'' ++ itext b x ns'), ?_⟩
              show (x :: w :: enc2 x W'') ++ itext b x ns' = _
              rfl
      | mark j => exact Or.inr ⟨_, rfl⟩
      | dmg A i2 j2 => exact Or.inr ⟨_, rfl⟩

/-- A marker `mark j` with `j ≤ i` passes through the repair scan
(pattern `x b^{i+2}`) untouched. -/
theorem markpass2 (x b : α) (hxb : x ≠ b) (A : List α) (K M : Nat)
    (hKM : M < K) (T : List α) (hT : T = [] ∨ ∃ T', T = x :: T') :
    subst A (marker x b K) (marker x b M ++ T)
      = marker x b M ++ subst A (marker x b K) T := by
  have hB : ∀ C, matchHere (marker x b K) (b :: C) = none := by
    intro C
    show matchHere (x :: List.replicate K b) (b :: C) = none
    exact matchHere_ne x _ b C hxb
  have hM1 : matchHere (marker x b K) (x :: (List.replicate M b ++ T)) = none := by
    show matchHere (x :: List.replicate K b) (x :: (List.replicate M b ++ T)) = none
    rw [matchHere_cons_self]
    exact mh_brun b x (Ne.symm hxb) K M hKM T hT
  show subst A (marker x b K) (x :: (List.replicate M b ++ T))
      = (x :: List.replicate M b) ++ subst A (marker x b K) T
  rw [subst_cons_none A (marker x b K) x _ hM1, bpass b A (marker x b K) hB]
  rfl

/-- A fragment passes through the repair and instantiation scans
(pattern `x b^K` with `K ≥ 2`) untouched: no `b`-run inside an `enc2`
image or before an `x`-headed tail is long enough. -/
theorem fragpass2 (x b : α) (hxb : x ≠ b) (A : List α) (K : Nat) (hK : 2 ≤ K) :
    ∀ (W T : List α), (T = [] ∨ ∃ T', T = x :: T') →
    subst A (marker x b K) (enc2 x W ++ T) = enc2 x W ++ subst A (marker x b K) T := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 + 1 := ⟨K - 2, by omega⟩
  intro W
  induction W with
  | nil => intro T hT; rfl
  | cons w W' ih =>
      intro T hT
      have hcond := enc2_T_cond x W' T hT
      have hA1 : matchHere (marker x b (K' + 1 + 1)) (x :: (w :: (enc2 x W' ++ T))) = none := by
        show matchHere (x :: List.replicate (K' + 1 + 1) b) (x :: (w :: (enc2 x W' ++ T))) = none
        rw [matchHere_cons_self]
        by_cases hwb : b = w
        · subst hwb
          show matchHere (b :: List.replicate (K' + 1) b) (b :: (enc2 x W' ++ T)) = none
          rw [matchHere_cons_self]
          exact mh_rep_none b x (Ne.symm hxb) (K' + 1) (by omega) (enc2 x W' ++ T) hcond
        · exact matchHere_ne b _ w _ hwb
      have hA2 : matchHere (marker x b (K' + 1 + 1)) (w :: (enc2 x W' ++ T)) = none := by
        by_cases hwx : x = w
        · subst hwx
          show matchHere (x :: List.replicate (K' + 1 + 1) b) (x :: (enc2 x W' ++ T)) = none
          rw [matchHere_cons_self]
          exact mh_rep_none b x (Ne.symm hxb) (K' + 1 + 1) (by omega) (enc2 x W' ++ T) hcond
        · show matchHere (x :: List.replicate (K' + 1 + 1) b) (w :: (enc2 x W' ++ T)) = none
          exact matchHere_ne x _ w _ hwx
      show subst A (marker x b (K' + 1 + 1)) (x :: (w :: (enc2 x W' ++ T)))
          = (x :: w :: enc2 x W') ++ subst A (marker x b (K' + 1 + 1)) T
      rw [subst_cons_none A (marker x b (K' + 1 + 1)) x _ hA1,
        subst_cons_none A (marker x b (K' + 1 + 1)) w _ hA2, ih T hT]
      rfl

omit [DecidableEq α] in
/-- Unfolding `repairNF` on a marker head. -/
theorem repairNF_mark (b x : α) (i : Nat) (X : List α) (j : Nat) (ns : List (NFItem α)) :
    repairNF b x i X (NFItem.mark j :: ns) = NFItem.mark j :: repairNF b x i X ns := by
  simp only [repairNF]

omit [DecidableEq α] in
/-- Unfolding `repairNF` on a damaged-marker head. -/
theorem repairNF_dmg (b x : α) (i : Nat) (X A : List α) (i2 j : Nat) (ns : List (NFItem α)) :
    repairNF b x i X (NFItem.dmg A i2 j :: ns)
      = pushFrag A (NFItem.mark j :: repairNF b x i X ns) := by
  simp only [repairNF]

omit [DecidableEq α] in
/-- Unfolding `repairNF` on a fragment before a damaged marker. -/
theorem repairNF_frag_dmg (b x : α) (i : Nat) (X W A : List α) (i2 j : Nat)
    (ns : List (NFItem α)) :
    repairNF b x i X (NFItem.frag W :: NFItem.dmg A i2 j :: ns)
      = NFItem.frag (W ++ A) :: NFItem.mark j :: repairNF b x i X ns := by
  simp only [repairNF]

omit [DecidableEq α] in
/-- Unfolding `repairNF` on a fragment before a marker. -/
theorem repairNF_frag_mark (b x : α) (i : Nat) (X W : List α) (j : Nat) (ns : List (NFItem α)) :
    repairNF b x i X (NFItem.frag W :: NFItem.mark j :: ns)
      = NFItem.frag W :: NFItem.mark j :: repairNF b x i X ns := by
  simp only [repairNF]

omit [DecidableEq α] in
/-- Unfolding `repairNF` on a final fragment. -/
theorem repairNF_frag_nil (b x : α) (i : Nat) (X W : List α) :
    repairNF b x i X (NFItem.frag W :: []) = NFItem.frag W :: [] := by
  simp only [repairNF]

omit [DecidableEq α] in
/-- The restoration algebra of the repair pass: the fired damaged
marker `x b^{i+1} b^j` is restored to `enc2 x A` followed by the marker
`x b^{j+1}`. -/
theorem repair_algebra (x b : α) (A : List α) (j : Nat) (Y : List α) :
    (enc2 x (A ++ [b]) ++ [b]) ++ (List.replicate j b ++ Y)
      = enc2 x A ++ (marker x b (j + 2) ++ Y) := by
  simp [enc2, marker, List.replicate_succ]

/-- The repair scan at a damaged marker: the pattern `x b^{i+2}` fires
exactly at the damaged marker's head, restoring the fragment `A` and
the marker. -/
theorem dmg_pass (x b : α) (hxb : x ≠ b) (i : Nat) (X A : List α) (j : Nat) (T : List α)
    (hX : X = A ++ [b]) (hj : 1 ≤ j) :
    subst (enc2 x X ++ [b]) (marker x b (i + 2))
        ((marker x b (i + 1) ++ List.replicate j b) ++ T)
      = enc2 x A ++ (marker x b (j + 1)
          ++ subst (enc2 x X ++ [b]) (marker x b (i + 2)) T) := by
  have hB : marker x b (i + 2) ≠ [] := by simp [marker]
  have hsplit : List.replicate (i + 1) b ++ List.replicate j b
      = List.replicate (i + 1 + j) b := replicate_append b (i + 1) j
  have hfire : matchHere (marker x b (i + 2))
      ((marker x b (i + 1) ++ List.replicate j b) ++ T)
      = some (List.replicate (j - 1) b ++ T) := by
    show matchHere (x :: List.replicate (i + 2) b)
        (x :: ((List.replicate (i + 1) b ++ List.replicate j b) ++ T)) = _
    rw [matchHere_cons_self, hsplit, mh_run_fire b (i + 2) (i + 1 + j) (by omega) T]
    have hsub : i + 1 + j - (i + 2) = j - 1 := by omega
    rw [hsub]
  have hcon : (marker x b (i + 1) ++ List.replicate j b) ++ T
      = x :: ((List.replicate (i + 1) b ++ List.replicate j b) ++ T) := rfl
  have hBb : ∀ C, matchHere (marker x b (i + 2)) (b :: C) = none := by
    intro C
    show matchHere (x :: List.replicate (i + 2) b) (b :: C) = none
    exact matchHere_ne x _ b C hxb
  rw [hcon, subst_cons_match (enc2 x X ++ [b]) (marker x b (i + 2)) hB x
    ((List.replicate (i + 1) b ++ List.replicate j b) ++ T)
    (List.replicate (j - 1) b ++ T) hfire,
    bpass b (enc2 x X ++ [b]) (marker x b (i + 2)) hBb (j - 1) T]
  cases j with
  | zero => omega
  | succ j' =>
      have hjm : j' + 1 - 1 = j' := by omega
      rw [hjm, hX]
      exact repair_algebra x b A j' _

/-- The repair pass `i` on the item layer: over the flat text of a
rounded list, the repair scan replaces exactly the damaged markers. -/
theorem repairNF_scan (x b : α) (hxb : x ≠ b) (i : Nat) (X : List α) :
    ∀ (n : Nat) (ns : List (NFItem α)), ns.length ≤ n → Rounded b i X ns →
    subst (enc2 x X ++ [b]) (marker x b (i + 2)) (itext b x ns)
      = itext b x (repairNF b x i X ns) := by
  intro n
  induction n with
  | zero =>
      intro ns hns hC
      cases ns with
      | nil =>
          show subst (enc2 x X ++ [b]) (marker x b (i + 2)) [] = []
          rw [subst_nil]
      | cons m ns' =>
          have h1 : 1 ≤ (m :: ns').length := by simp
          omega
  | succ n ih =>
      intro ns hns hC
      cases ns with
      | nil =>
          show subst (enc2 x X ++ [b]) (marker x b (i + 2)) [] = []
          rw [subst_nil]
      | cons m ns' =>
      cases m with
      | mark j =>
          obtain ⟨hj, hji, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.mark j :: ns').length = ns'.length + 1 := by simp
            omega
          have hit : itext b x (NFItem.mark j :: ns')
              = marker x b (j + 1) ++ itext b x ns' := rfl
          rw [hit, repairNF_mark,
            markpass2 x b hxb (enc2 x X ++ [b]) (i + 2) (j + 1) (by omega) (itext b x ns')
              (itext_head b x ns' (rounded_fragsNE b i X ns' hC')),
            ih ns' hns' hC']
          rfl
      | dmg A i2 j2 =>
          obtain ⟨hi2, hj2, _, hXeq, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.dmg A i2 j2 :: ns').length = ns'.length + 1 := by simp
            omega
          have hit : itext b x (NFItem.dmg A i2 j2 :: ns')
              = (marker x b (i2 + 1) ++ List.replicate j2 b) ++ itext b x ns' := rfl
          rw [hit, hi2, dmg_pass x b hxb i X A j2 (itext b x ns') hXeq hj2,
            ih ns' hns' hC', repairNF_dmg, itext_push]
          rfl
      | frag W =>
          cases ns' with
          | nil =>
              have hit : itext b x (NFItem.frag W :: []) = enc2 x W ++ [] := rfl
              rw [hit, repairNF_frag_nil,
                fragpass2 x b hxb (enc2 x X ++ [b]) (i + 2) (by omega) W [] (Or.inl rfl),
                subst_nil, hit]
          | cons m2 ns'' =>
              cases m2 with
              | frag W2 => exact hC.elim
              | dmg A i2 j2 =>
                  obtain ⟨hW, hi2, hj2, _, hXeq, hC''⟩ := hC
                  have hns'' : ns''.length ≤ n := by
                    have h1 : (NFItem.frag W :: NFItem.dmg A i2 j2 :: ns'').length
                        = ns''.length + 2 := by simp
                    omega
                  have hit : itext b x (NFItem.frag W :: NFItem.dmg A i2 j2 :: ns'')
                      = enc2 x W ++ ((marker x b (i2 + 1) ++ List.replicate j2 b)
                          ++ itext b x ns'') := rfl
                  rw [hit, hi2, repairNF_frag_dmg,
                    fragpass2 x b hxb (enc2 x X ++ [b]) (i + 2) (by omega) W
                      ((marker x b (i + 1) ++ List.replicate j2 b) ++ itext b x ns'')
                      (Or.inr ⟨_, rfl⟩),
                    dmg_pass x b hxb i X A j2 (itext b x ns'') hXeq hj2,
                    ih ns'' hns'' hC'']
                  have hR : itext b x (NFItem.frag (W ++ A) :: NFItem.mark j2
                      :: repairNF b x i X ns'')
                      = enc2 x (W ++ A) ++ (marker x b (j2 + 1)
                          ++ itext b x (repairNF b x i X ns'')) := rfl
                  rw [hR, enc2_append]
                  simp only [List.append_assoc]
              | mark j =>
                  obtain ⟨hW, hj, hji, hC''⟩ := hC
                  have hns'' : ns''.length ≤ n := by
                    have h1 : (NFItem.frag W :: NFItem.mark j :: ns'').length
                        = ns''.length + 2 := by simp
                    omega
                  have hit : itext b x (NFItem.frag W :: NFItem.mark j :: ns'')
                      = enc2 x W ++ (marker x b (j + 1) ++ itext b x ns'') := rfl
                  rw [hit, repairNF_frag_mark,
                    fragpass2 x b hxb (enc2 x X ++ [b]) (i + 2) (by omega) W
                      (marker x b (j + 1) ++ itext b x ns'') (Or.inr ⟨_, rfl⟩),
                    markpass2 x b hxb (enc2 x X ++ [b]) (i + 2) (j + 1) (by omega)
                      (itext b x ns'') (itext_head b x ns'' (rounded_fragsNE b i X ns'' hC'')),
                    ih ns'' hns'' hC'']
                  rfl

omit [DecidableEq α] in
/-- The repair pass of round `i` turns a rounded list back into a
canonical one with markers at most `i`. -/
theorem repairNF_canon (b x : α) (i : Nat) (X : List α) :
    ∀ (n : Nat) (ns : List (NFItem α)), ns.length ≤ n → Rounded b i X ns →
    CanonB i (repairNF b x i X ns) := by
  intro n
  induction n with
  | zero =>
      intro ns hns hC
      cases ns with
      | nil => exact (by trivial : CanonB i (repairNF b x i X []))
      | cons m ns' =>
          have h1 : 1 ≤ (m :: ns').length := by simp
          omega
  | succ n ih =>
      intro ns hns hC
      cases ns with
      | nil => exact (by trivial : CanonB i (repairNF b x i X []))
      | cons m ns' =>
      cases m with
      | mark j =>
          obtain ⟨hj, hji, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.mark j :: ns').length = ns'.length + 1 := by simp
            omega
          rw [repairNF_mark]
          exact ⟨hj, hji, ih ns' hns' hC'⟩
      | dmg A i2 j2 =>
          obtain ⟨hi2, hj2, hjm, hXeq, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.dmg A i2 j2 :: ns').length = ns'.length + 1 := by simp
            omega
          rw [repairNF_dmg]
          have hp : pushFrag A (NFItem.mark j2 :: repairNF b x i X ns')
              = if A = [] then NFItem.mark j2 :: repairNF b x i X ns'
                else NFItem.frag A :: NFItem.mark j2 :: repairNF b x i X ns' := by
            simp only [pushFrag]
          rw [hp]
          by_cases hA : A = []
          · rw [ite_eq_left hA]
            exact ⟨hj2, hjm, ih ns' hns' hC'⟩
          · rw [ite_eq_right hA]
            exact ⟨hA, hj2, hjm, ih ns' hns' hC'⟩
      | frag W =>
          cases ns' with
          | nil =>
              rw [repairNF_frag_nil]
              exact hC
          | cons m2 ns'' =>
              cases m2 with
              | frag W2 => exact hC.elim
              | dmg A i2 j2 =>
                  obtain ⟨hW, hi2, hj2, hjm, hXeq, hC''⟩ := hC
                  have hns'' : ns''.length ≤ n := by
                    have h1 : (NFItem.frag W :: NFItem.dmg A i2 j2 :: ns'').length
                        = ns''.length + 2 := by simp
                    omega
                  rw [repairNF_frag_dmg]
                  exact ⟨by simp [hW], hj2, hjm, ih ns'' hns'' hC''⟩
              | mark j =>
                  obtain ⟨hW, hj, hji, hC''⟩ := hC
                  have hns'' : ns''.length ≤ n := by
                    have h1 : (NFItem.frag W :: NFItem.mark j :: ns'').length
                        = ns''.length + 2 := by simp
                    omega
                  rw [repairNF_frag_mark]
                  exact ⟨hW, hj, hji, ih ns'' hns'' hC''⟩


/-- The shape needed by the instantiation passes: fragments nonempty,
markers indexed `1..k`, no damaged markers; adjacent fragments are
allowed (a fired marker merges its neighbours). -/
def InstOK (k : Nat) : List (NFItem α) → Prop
  | [] => True
  | NFItem.mark j :: ns => 1 ≤ j ∧ j ≤ k ∧ InstOK k ns
  | NFItem.dmg _ _ _ :: _ => False
  | NFItem.frag W :: ns => W ≠ [] ∧ InstOK k ns

omit [DecidableEq α] in
/-- A canonical list is instantiable. -/
theorem canonB_instOK (m : Nat) : ∀ ns : List (NFItem α), CanonB m ns → InstOK m ns := by
  intro ns
  induction ns with
  | nil => intro _; exact trivial
  | cons n ns' ih =>
      intro hC
      cases n with
      | frag W =>
          cases ns' with
          | nil => exact ⟨hC, trivial⟩
          | cons n2 ns'' =>
              cases n2 with
              | frag W2 => exact hC.elim
              | mark j => exact ⟨hC.1, ih ⟨hC.2.1, hC.2.2.1, hC.2.2.2⟩⟩
              | dmg A i2 j2 => exact hC.elim
      | mark j => exact ⟨hC.1, hC.2.1, ih hC.2.2⟩
      | dmg A i2 j2 => exact hC.elim

omit [DecidableEq α] in
/-- An instantiable list has nonempty fragments. -/
theorem instOK_fragsNE (k : Nat) : ∀ ns : List (NFItem α), InstOK k ns → fragsNE ns := by
  intro ns
  induction ns with
  | nil => intro _; exact trivial
  | cons n ns' ih =>
      intro hC
      cases n with
      | frag W => exact ⟨hC.1, ih hC.2⟩
      | mark j => exact ih hC.2.2
      | dmg A i2 j2 => exact hC.elim

omit [DecidableEq α] in
/-- Pushing a fragment onto an instantiable list keeps it so. -/
theorem pushFrag_instOK (Y : List α) (k : Nat) : ∀ ns : List (NFItem α),
    InstOK k ns → InstOK k (pushFrag Y ns) := by
  intro ns
  cases ns with
  | nil =>
      intro _
      simp only [pushFrag]
      split
      · exact trivial
      · exact ⟨by assumption, trivial⟩
  | cons n ns' =>
      intro hC
      cases n with
      | frag W => exact ⟨by simp [hC.1], hC.2⟩
      | mark j =>
          simp only [pushFrag]
          split
          · exact hC
          · exact ⟨by assumption, hC.1, hC.2.1, hC.2.2⟩
      | dmg A i2 j2 => exact hC.elim

omit [DecidableEq α] in
/-- Unfolding `instNF` on a fired marker. -/
theorem instNF_mark_fire (b x : α) (k : Nat) (Y : List α) (ns : List (NFItem α)) :
    instNF b x k Y (NFItem.mark k :: ns) = pushFrag Y (instNF b x k Y ns) := by
  simp [instNF]

omit [DecidableEq α] in
/-- Unfolding `instNF` on a passed marker. -/
theorem instNF_mark_pass (b x : α) (k : Nat) (Y : List α) (j : Nat) (ns : List (NFItem α))
    (hjk : ¬ j = k) :
    instNF b x k Y (NFItem.mark j :: ns) = NFItem.mark j :: instNF b x k Y ns := by
  simp [instNF, hjk]

omit [DecidableEq α] in
/-- Unfolding `instNF` on a fragment head. -/
theorem instNF_frag_cons (b x : α) (k : Nat) (Y W : List α) (ns : List (NFItem α)) :
    instNF b x k Y (NFItem.frag W :: ns) = NFItem.frag W :: instNF b x k Y ns := rfl

/-- The instantiation pass `k` on the item layer: over the flat text,
the scan replaces exactly the markers of round `k` by the code of `Y`. -/
theorem instNF_scan (x b : α) (hxb : x ≠ b) (k : Nat) (hk : 1 ≤ k) (Y : List α) :
    ∀ (n : Nat) (ns : List (NFItem α)), ns.length ≤ n → InstOK k ns →
    subst (enc2 x Y) (marker x b (k + 1)) (itext b x ns)
      = itext b x (instNF b x k Y ns) := by
  intro n
  induction n with
  | zero =>
      intro ns hns hC
      cases ns with
      | nil =>
          show subst (enc2 x Y) (marker x b (k + 1)) [] = []
          rw [subst_nil]
      | cons m ns' =>
          have h1 : 1 ≤ (m :: ns').length := by simp
          omega
  | succ n ih =>
      intro ns hns hC
      cases ns with
      | nil =>
          show subst (enc2 x Y) (marker x b (k + 1)) [] = []
          rw [subst_nil]
      | cons m ns' =>
      cases m with
      | mark j =>
          obtain ⟨hj, hjk, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.mark j :: ns').length = ns'.length + 1 := by simp
            omega
          have hit : itext b x (NFItem.mark j :: ns')
              = marker x b (j + 1) ++ itext b x ns' := rfl
          rw [hit]
          by_cases hjk' : j = k
          · rw [hjk']
            have hcon : marker x b (k + 1) ++ itext b x ns'
                = x :: (List.replicate (k + 1) b ++ itext b x ns') := rfl
            have hfire : matchHere (marker x b (k + 1))
                (x :: (List.replicate (k + 1) b ++ itext b x ns'))
                = some (itext b x ns') :=
              matchHere_prefix (marker x b (k + 1)) (itext b x ns')
            have hB : marker x b (k + 1) ≠ [] := by simp [marker]
            rw [hcon, subst_cons_match (enc2 x Y) (marker x b (k + 1)) hB x
              (List.replicate (k + 1) b ++ itext b x ns') (itext b x ns') hfire,
              ih ns' hns' hC', instNF_mark_fire, itext_push]
          · have hT := itext_head b x ns' (instOK_fragsNE k ns' hC')
            rw [markpass2 x b hxb (enc2 x Y) (k + 1) (j + 1) (by omega)
              (itext b x ns') hT, ih ns' hns' hC', instNF_mark_pass b x k Y j ns' hjk']
            rfl
      | frag W =>
          obtain ⟨hW, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.frag W :: ns').length = ns'.length + 1 := by simp
            omega
          have hit : itext b x (NFItem.frag W :: ns') = enc2 x W ++ itext b x ns' := rfl
          have hT := itext_head b x ns' (instOK_fragsNE k ns' hC')
          rw [hit, instNF_frag_cons,
            fragpass2 x b hxb (enc2 x Y) (k + 1) (by omega) W (itext b x ns') hT,
            ih ns' hns' hC']
          rfl
      | dmg A i2 j2 => exact hC.elim

omit [DecidableEq α] in
/-- The instantiation pass `k` leaves an instantiable list for the
earlier rounds. -/
theorem instNF_canon (b x : α) (k : Nat) (Y : List α) :
    ∀ (n : Nat) (ns : List (NFItem α)), ns.length ≤ n → InstOK k ns →
    InstOK (k - 1) (instNF b x k Y ns) := by
  intro n
  induction n with
  | zero =>
      intro ns hns hC
      cases ns with
      | nil => exact trivial
      | cons m ns' =>
          have h1 : 1 ≤ (m :: ns').length := by simp
          omega
  | succ n ih =>
      intro ns hns hC
      cases ns with
      | nil => exact trivial
      | cons m ns' =>
      cases m with
      | mark j =>
          obtain ⟨hj, hjk, hC'⟩ := hC
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.mark j :: ns').length = ns'.length + 1 := by simp
            omega
          by_cases hjk' : j = k
          · rw [hjk', instNF_mark_fire]
            exact pushFrag_instOK Y (k - 1) (instNF b x k Y ns') (ih ns' hns' hC')
          · rw [instNF_mark_pass b x k Y j ns' hjk']
            exact ⟨hj, by omega, ih ns' hns' hC'⟩
      | frag W =>
          have hns' : ns'.length ≤ n := by
            have h1 : (NFItem.frag W :: ns').length = ns'.length + 1 := by simp
            omega
          rw [instNF_frag_cons]
          exact ⟨hC.1, ih ns' hns' hC.2⟩
      | dmg A i2 j2 => exact hC.elim

/-- The length of the pattern of round `j`. -/
def xlen (pairs : List (List α × List α)) (j : Nat) : Nat :=
  (pairs.getD (j - 1) ([], [])).1.length

/-- Drop the first `k` entries of an annotated list. -/
def dropN : Nat → List (α × Option Nat) → List (α × Option Nat)
  | 0, T => T
  | _ + 1, [] => []
  | k + 1, _ :: T' => dropN k T'

omit [DecidableEq α] in
/-- Dropping the length of a prefix. -/
theorem dropN_length (U : List (α × Option Nat)) :
    ∀ (k : Nat) (T : List (α × Option Nat)), T.length = k → dropN k (T ++ U) = U := by
  intro k T
  induction T generalizing k with
  | nil => intro h; cases k with
    | zero => rfl
    | succ k' => simp at h
  | cons t T' ih =>
      intro h
      cases k with
      | zero => simp at h
      | succ k' =>
          rw [List.length_cons] at h
          show dropN k' (T' ++ U) = U
          exact ih k' (by omega)

omit [DecidableEq α] in
/-- Dropping past the end of a list gives `[]`. -/
theorem dropN_all (T : List (α × Option Nat)) (k : Nat) (hk : T.length ≤ k) :
    dropN k T = [] := by
  induction T generalizing k with
  | nil => cases k with
    | zero => rfl
    | succ k' => rfl
  | cons t T' ih =>
      cases k with
      | zero => simp at hk
      | succ k' =>
          rw [List.length_cons] at hk
          show dropN k' T' = []
          exact ih k' (by omega)

omit [DecidableEq α] in
/-- Dropping entries never lengthens the list. -/
theorem dropN_length_le (k : Nat) : ∀ T : List (α × Option Nat),
    (dropN k T).length ≤ T.length := by
  induction k with
  | zero => intro T; exact Nat.le_refl _
  | succ k' ih =>
      intro T
      cases T with
      | nil => exact Nat.le_refl 0
      | cons t T' =>
          show (dropN k' T').length ≤ (t :: T').length
          rw [List.length_cons]
          have h := ih T'
          omega

/-- The item-level reading of an annotated list: an unfrozen entry
extends the current fragment, and each `|X_j|`-sized chunk of round-`j`
entries becomes one marker. -/
def pieces (pairs : List (List α × List α)) : List (α × Option Nat) → List (NFItem α)
  | [] => []
  | (t, none) :: T' => pushFrag [t] (pieces pairs T')
  | (t, some j) :: T' =>
      NFItem.mark j :: pieces pairs (dropN (xlen pairs j - 1) T')
termination_by T => T.length
decreasing_by
  · simp only [List.length_cons]; omega
  · have h := dropN_length_le (xlen pairs j - 1) T'
    simp only [List.length_cons] at h ⊢
    omega

omit [DecidableEq α] in
/-- Unfolding `pieces` on an unfrozen entry. -/
theorem pieces_none (pairs : List (List α × List α)) (t : α) (T : List (α × Option Nat)) :
    pieces pairs ((t, none) :: T) = pushFrag [t] (pieces pairs T) := by
  simp only [pieces]

omit [DecidableEq α] in
/-- Unfolding `pieces` on a frozen entry. -/
theorem pieces_some (pairs : List (List α × List α)) (t : α) (j : Nat)
    (T : List (α × Option Nat)) :
    pieces pairs ((t, some j) :: T)
      = NFItem.mark j :: pieces pairs (dropN (xlen pairs j - 1) T) := by
  simp only [pieces]

omit [DecidableEq α] in
/-- Pushing a single character is shifting it. -/
theorem pushFrag_single (w : α) : ∀ ns : List (NFItem α),
    pushFrag [w] ns = shiftItem w ns := by
  intro ns
  cases ns with
  | nil => rfl
  | cons n ns' =>
      cases n with
      | frag W => rfl
      | mark j => rfl
      | dmg A i2 j2 => rfl

omit [DecidableEq α] in
/-- Pushing an empty fragment is the identity. -/
theorem pushFrag_nil : ∀ ns : List (NFItem α), pushFrag [] ns = ns := by
  intro ns
  cases ns with
  | nil => rfl
  | cons n ns' =>
      cases n with
      | frag W => show NFItem.frag ([] ++ W) :: ns' = NFItem.frag W :: ns'; rfl
      | mark j => rfl
      | dmg A i2 j2 => rfl

omit [DecidableEq α] in
/-- Unfolding `repairNF` on a fragment before a fragment. -/
theorem repairNF_frag_frag (b x : α) (i : Nat) (X W W2 : List α) (ns : List (NFItem α)) :
    repairNF b x i X (NFItem.frag W :: NFItem.frag W2 :: ns)
      = NFItem.frag W :: repairNF b x i X (NFItem.frag W2 :: ns) := by
  simp only [repairNF]

omit [DecidableEq α] in
/-- The repair pass commutes with shifting a character onto the list. -/
theorem repairNF_shift (b x : α) (i : Nat) (X : List α) (w : α) :
    ∀ ns : List (NFItem α),
    repairNF b x i X (shiftItem w ns) = shiftItem w (repairNF b x i X ns) := by
  intro ns
  cases ns with
  | nil =>
      show repairNF b x i X (NFItem.frag [w] :: [])
        = shiftItem w (repairNF b x i X [])
      rw [repairNF_frag_nil]
      rfl
  | cons n ns' =>
      cases n with
      | mark j =>
          show repairNF b x i X (NFItem.frag [w] :: NFItem.mark j :: ns')
            = shiftItem w (repairNF b x i X (NFItem.mark j :: ns'))
          rw [repairNF_frag_mark, repairNF_mark]
          rfl
      | frag W =>
          cases ns' with
          | nil =>
              show repairNF b x i X (NFItem.frag (w :: W) :: [])
                = shiftItem w (repairNF b x i X (NFItem.frag W :: []))
              rw [repairNF_frag_nil, repairNF_frag_nil]
              rfl
          | cons n2 ns'' =>
              cases n2 with
              | frag W2 =>
                  show repairNF b x i X (NFItem.frag (w :: W) :: NFItem.frag W2 :: ns'')
                    = shiftItem w (repairNF b x i X (NFItem.frag W :: NFItem.frag W2 :: ns''))
                  rw [repairNF_frag_frag, repairNF_frag_frag]
                  rfl
              | dmg A i2 j2 =>
                  show repairNF b x i X (NFItem.frag (w :: W) :: NFItem.dmg A i2 j2 :: ns'')
                    = shiftItem w (repairNF b x i X (NFItem.frag W :: NFItem.dmg A i2 j2 :: ns''))
                  rw [repairNF_frag_dmg, repairNF_frag_dmg]
                  show NFItem.frag ((w :: W) ++ A) :: NFItem.mark j2 :: repairNF b x i X ns''
                    = NFItem.frag (w :: (W ++ A)) :: NFItem.mark j2 :: repairNF b x i X ns''
                  rw [List.cons_append]
              | mark j =>
                  show repairNF b x i X (NFItem.frag (w :: W) :: NFItem.mark j :: ns'')
                    = shiftItem w (repairNF b x i X (NFItem.frag W :: NFItem.mark j :: ns''))
                  rw [repairNF_frag_mark, repairNF_frag_mark]
                  rfl
      | dmg A i2 j2 =>
          cases A with
          | nil =>
              show repairNF b x i X (NFItem.frag [w] :: NFItem.dmg [] i2 j2 :: ns')
                = shiftItem w (repairNF b x i X (NFItem.dmg [] i2 j2 :: ns'))
              rw [repairNF_frag_dmg, repairNF_dmg, pushFrag_nil]
              show NFItem.frag ([w] ++ []) :: NFItem.mark j2 :: repairNF b x i X ns'
                = shiftItem w (NFItem.mark j2 :: repairNF b x i X ns')
              rw [List.append_nil]
              rfl
          | cons a A' =>
              show repairNF b x i X (NFItem.frag [w] :: NFItem.dmg (a :: A') i2 j2 :: ns')
                = shiftItem w (repairNF b x i X (NFItem.dmg (a :: A') i2 j2 :: ns'))
              rw [repairNF_frag_dmg, repairNF_dmg]
              show NFItem.frag ([w] ++ (a :: A')) :: NFItem.mark j2 :: repairNF b x i X ns'
                = shiftItem w (pushFrag (a :: A') (NFItem.mark j2 :: repairNF b x i X ns'))
              have h3 : pushFrag (a :: A') (NFItem.mark j2 :: repairNF b x i X ns')
                  = NFItem.frag (a :: A') :: NFItem.mark j2 :: repairNF b x i X ns' := by
                simp [pushFrag]
              rw [h3]
              show NFItem.frag ([w] ++ (a :: A')) :: NFItem.mark j2 :: repairNF b x i X ns'
                = NFItem.frag (w :: (a :: A')) :: NFItem.mark j2 :: repairNF b x i X ns'
              simp only [List.cons_append, List.nil_append]

/-! ### The bridge to the annotated semantics

  The item-level rounds correspond to the freezing passes over the
  annotated representation: an unfrozen entry extends a fragment, and a
  `|X_j|`-sized chunk of round-`j` entries is one marker.  The invariant
  `Chunked` records that frozen runs are aligned to their chunk size.
-/

/-- One full round at the item level: the rename pass followed by the
repair pass. -/
def roundNF (b x : α) (i : Nat) (X : List α) (ns : List (NFItem α)) : List (NFItem α) :=
  repairNF b x i X (renameNF b x i X ns)

/-- A fragment written as unfrozen entries. -/
def runE (W : List α) : List (α × Option Nat) := W.map (fun w => (w, none))

omit [DecidableEq α] in
/-- The characters of the maximal unfrozen prefix. -/
def runOf : List (α × Option Nat) → List α
  | (t, none) :: T' => t :: runOf T'
  | _ => []

omit [DecidableEq α] in
/-- The annotated list after the maximal unfrozen prefix. -/
def afterRun : List (α × Option Nat) → List (α × Option Nat)
  | (_, none) :: T' => afterRun T'
  | T => T

omit [DecidableEq α] in
/-- Unfolding `runOf` and `afterRun` on an unfrozen entry. -/
theorem runOf_afterRun_none (t : α) (T : List (α × Option Nat)) :
    runOf ((t, none) :: T) = t :: runOf T ∧ afterRun ((t, none) :: T) = afterRun T :=
  ⟨rfl, rfl⟩

omit [DecidableEq α] in
/-- An annotated list is its unfrozen run followed by its frozen tail. -/
theorem run_decomp : ∀ T : List (α × Option Nat),
    T = runE (runOf T) ++ afterRun T := by
  intro T
  induction T with
  | nil => rfl
  | cons t T' ih =>
      obtain ⟨c, o⟩ := t
      cases o with
      | none => show (c, none) :: T' = (c, none) :: (runE (runOf T') ++ afterRun T'); rw [← ih]
      | some j => rfl

omit [DecidableEq α] in
/-- The tail after the unfrozen run is empty or frozen-headed. -/
theorem afterRun_cases : ∀ T : List (α × Option Nat),
    afterRun T = [] ∨ ∃ (c : α) (j : Nat) (T' : List (α × Option Nat)),
      afterRun T = (c, some j) :: T' := by
  intro T
  cases T with
  | nil => exact Or.inl rfl
  | cons t T' =>
      obtain ⟨c, o⟩ := t
      cases o with
      | none =>
          rcases afterRun_cases T' with h | ⟨c2, j, T''⟩
          · exact Or.inl (by
              show afterRun ((c, none) :: T') = []
              rw [show afterRun ((c, none) :: T') = afterRun T' from rfl]
              exact h)
          · exact Or.inr ⟨c2, j, T''⟩
      | some j => exact Or.inr ⟨c, j, T', rfl⟩

/-- A round leaves a leading marker unchanged. -/
theorem roundNF_mark (b x : α) (i : Nat) (X : List α) (j : Nat) (ns : List (NFItem α)) :
    roundNF b x i X (NFItem.mark j :: ns) = NFItem.mark j :: roundNF b x i X ns := by
  show repairNF b x i X (renameNF b x i X (NFItem.mark j :: ns))
    = NFItem.mark j :: repairNF b x i X (renameNF b x i X ns)
  rw [renameNF_mark]
  split
  · show repairNF b x i X (NFItem.dmg [] i j :: renameNF b x i X ns) = _
    rw [repairNF_dmg, pushFrag_nil]
  · rw [repairNF_mark]

omit [DecidableEq α] in
/-- Pushing a one-character fragment onto a pushed fragment. -/
theorem pushFrag_cons (v : α) : ∀ (V : List α) (ns : List (NFItem α)),
    pushFrag [v] (pushFrag V ns) = pushFrag (v :: V) ns := by
  intro V ns
  cases ns with
  | nil => cases V with
    | nil => rfl
    | cons v' V' => rfl
  | cons n ns' =>
      cases n with
      | frag W => cases V with
        | nil => show NFItem.frag ([v] ++ W) :: ns' = NFItem.frag (v :: W) :: ns'; rfl
        | cons v' V' => show NFItem.frag ([v] ++ (v' :: V' ++ W)) :: ns' = NFItem.frag (v :: v' :: V' ++ W) :: ns'; simp
      | mark j => cases V with
        | nil => rfl
        | cons v' V' => rfl
      | dmg A i2 j2 => cases V with
        | nil => rfl
        | cons v' V' => rfl

omit [DecidableEq α] in
/-- `pieces` over a run of unfrozen entries. -/
theorem pieces_run (pairs : List (List α × List α)) : ∀ (V : List α) (T : List (α × Option Nat)),
    pieces pairs (runE V ++ T) = pushFrag V (pieces pairs T) := by
  intro V
  induction V with
  | nil => intro T; show pieces pairs T = pushFrag [] (pieces pairs T); rw [pushFrag_nil]
  | cons v V' ih =>
      intro T
      show pieces pairs ((v, none) :: (runE V' ++ T))
        = pushFrag (v :: V') (pieces pairs T)
      rw [pieces_none, ih T]
      exact pushFrag_cons v V' (pieces pairs T)

omit [DecidableEq α] in
/-- Taking at least the whole list takes the whole list. -/
theorem take_of_le : ∀ (L : List α) (n : Nat), L.length ≤ n → L.take n = L := by
  intro L
  induction L with
  | nil => intro n _; cases n with
    | zero => rfl
    | succ n' => rfl
  | cons a L' ih =>
      intro n h
      cases n with
      | zero => simp at h
      | succ n' =>
          show a :: L'.take n' = a :: L'
          exact congrArg (a :: ·) (ih n' (by simp at h; omega))

omit [DecidableEq α] in
/-- Taking one more character. -/
theorem take_succ_cons (a : α) (l : List α) (n : Nat) :
    (a :: l).take (n + 1) = a :: l.take n := rfl

omit [DecidableEq α] in
/-- An annotated list whose head is frozen. -/
def FrozenHead : List (α × Option Nat) → Prop
  | (_, some _) :: _ => True
  | _ => False

omit [DecidableEq α] in
/-- An annotated list of only frozen entries. -/
def AllFrozen : List (α × Option Nat) → Prop
  | [] => True
  | (_, some _) :: T' => AllFrozen T'
  | (_, none) :: _ => False

omit [DecidableEq α] in
/-- The first `k` entries are frozen. -/
def frozenPrefix : Nat → List (α × Option Nat) → Prop
  | 0, _ => True
  | _ + 1, [] => False
  | k + 1, (_, some _) :: T' => frozenPrefix k T'
  | _ + 1, (_, none) :: _ => False

/-- The frozen runs are aligned: at a round-`j` frozen entry, the rest of
the current `|X_j|`-sized chunk is frozen too. -/
def Chunked (pairs : List (List α × List α)) : List (α × Option Nat) → Prop
  | [] => True
  | (_t, none) :: T' => Chunked pairs T'
  | (_t, some j) :: T' =>
      frozenPrefix (xlen pairs j - 1) T' ∧ Chunked pairs (dropN (xlen pairs j - 1) T')
termination_by T => T.length
decreasing_by
  · simp only [List.length_cons]; omega
  · have h := dropN_length_le (xlen pairs j - 1) T'
    simp only [List.length_cons] at h ⊢
    omega

/-- Unfolding `dropU?` at an unfrozen entry. -/
theorem dropU?_cons_none (c : α) (X' : List α) (d : α) (T' : List (α × Option Nat)) :
    dropU? (c :: X') ((d, none) :: T') = if c = d then dropU? X' T' else none := rfl

/-- Unfolding `dropU?` at a frozen entry. -/
theorem dropU?_cons_some (c : α) (X' : List α) (d : α) (j : Nat)
    (T' : List (α × Option Nat)) :
    dropU? (c :: X') ((d, some j) :: T') = none := rfl

/-- Unfolding `freezePass` at an unmatched head. -/
theorem freezePass_cons_none (X : List α) (hX : X ≠ []) (i : Nat) (t : α × Option Nat)
    (T' : List (α × Option Nat)) (hd : dropU? X (t :: T') = none) :
    freezePass X hX i (t :: T') = t :: freezePass X hX i T' := by
  simp only [freezePass]
  split
  · next hU => exact absurd hU (by rw [hd]; simp)
  · rfl

/-- Unfolding `freezePass` at a matched head. -/
theorem freezePass_cons_some (X : List α) (hX : X ≠ []) (i : Nat) (t : α × Option Nat)
    (T' : List (α × Option Nat)) (U : List (α × Option Nat))
    (hd : dropU? X (t :: T') = some U) :
    freezePass X hX i (t :: T')
      = freezeBlock i X.length (t :: T') ++ freezePass X hX i U := by
  simp only [freezePass]
  split
  · next hU =>
      rw [hd] at hU
      injection hU with hU'
      subst hU'
      rfl
  · next h => exact absurd hd (by rw [h]; simp)

/-- The freezing pass skips frozen entries unchanged. -/
theorem freezePass_frozen (X : List α) (hX : X ≠ []) (i : Nat) :
    ∀ (F T : List (α × Option Nat)), AllFrozen F →
    freezePass X hX i (F ++ T) = F ++ freezePass X hX i T := by
  intro F
  induction F with
  | nil => intro T _; rfl
  | cons f F' ih =>
      intro T hF
      obtain ⟨c, o⟩ := f
      cases o with
      | none => exact absurd hF (by cases hF <;> simp [AllFrozen])
      | some j =>
          have hd : dropU? X ((c, some j) :: (F' ++ T)) = none := by
            cases X with
            | nil => exact absurd rfl hX
            | cons c' X' => rfl
          have hF' : AllFrozen F' := hF
          show freezePass X hX i ((c, some j) :: (F' ++ T)) = _
          rw [freezePass_cons_none X hX i (c, some j) (F' ++ T) hd]
          show (c, some j) :: freezePass X hX i (F' ++ T) = _
          rw [ih T hF']
          show (c, some j) :: (F' ++ freezePass X hX i T)
            = ((c, some j) :: F') ++ freezePass X hX i T
          rfl

omit [DecidableEq α] in
/-- A frozen prefix splits off. -/
theorem frozenPrefix_split : ∀ (k : Nat) (T : List (α × Option Nat)), frozenPrefix k T →
    ∃ F U : List (α × Option Nat), T = F ++ U ∧ F.length = k ∧ AllFrozen F := by
  intro k
  induction k with
  | zero => intro T _; exact ⟨[], T, rfl, rfl, trivial⟩
  | succ k' ih =>
      intro T h
      cases T with
      | nil => exact absurd h (by cases h <;> simp [frozenPrefix])
      | cons t T' =>
          obtain ⟨c, o⟩ := t
          cases o with
          | none => exact absurd h (by cases h <;> simp [frozenPrefix])
          | some j =>
              obtain ⟨F, U, h1, h2, h3⟩ := ih T' h
              exact ⟨(c, some j) :: F, U, by rw [h1]; rfl, by simp [h2], h3⟩

/-- Dropping a frozen prefix commutes with the freezing pass. -/
theorem freezePass_dropN_frozen (X : List α) (hX : X ≠ []) (i : Nat) (k : Nat)
    (T : List (α × Option Nat)) (hFP : frozenPrefix k T) :
    dropN k (freezePass X hX i T) = freezePass X hX i (dropN k T) := by
  obtain ⟨F, U, h1, h2, h3⟩ := frozenPrefix_split k T hFP
  rw [h1, freezePass_frozen X hX i F U h3]
  show dropN k (F ++ freezePass X hX i U) = freezePass X hX i (dropN k (F ++ U))
  rw [dropN_length (freezePass X hX i U) k F h2, dropN_length U k F h2]

omit [DecidableEq α] in
/-- A full block freezes exactly `k` entries. -/
theorem freezeBlock_length (i : Nat) : ∀ (k : Nat) (T : List (α × Option Nat)),
    k ≤ T.length → (freezeBlock i k T).length = k := by
  intro k
  induction k with
  | zero => intro T _; rfl
  | succ k' ih =>
      intro T h
      cases T with
      | nil => simp at h
      | cons t T' =>
          obtain ⟨d, o⟩ := t
          show ((d, some i) :: freezeBlock i k' T').length = k' + 1
          rw [List.length_cons]
          rw [ih T' (by rw [List.length_cons] at h; omega)]

omit [DecidableEq α] in
/-- A freshly frozen block reads as one marker. -/
theorem pieces_freezeBlock (pairs : List (List α × List α)) (i : Nat) (k : Nat)
    (hxl : xlen pairs i = k) (hk : 1 ≤ k) :
    ∀ (T T2 : List (α × Option Nat)), k ≤ T.length →
    pieces pairs (freezeBlock i k T ++ T2) = NFItem.mark i :: pieces pairs T2 := by
  induction k with
  | zero => intro T T2 _; exact absurd hk (by omega)
  | succ k' ih =>
      intro T T2 h
      cases T with
      | nil => simp at h
      | cons t T' =>
          obtain ⟨d, o⟩ := t
          have hlen : k' ≤ T'.length := by rw [List.length_cons] at h; omega
          have hdrop : xlen pairs i - 1 = k' := by omega
          show pieces pairs ((d, some i) :: (freezeBlock i k' T' ++ T2)) = _
          rw [pieces_some, hdrop,
              dropN_length T2 k' (freezeBlock i k' T') (freezeBlock_length i k' T' hlen)]

omit [DecidableEq α] in
/-- Unfolding `Chunked` at an unfrozen entry. -/
theorem Chunked_none (pairs : List (List α × List α)) (t : α)
    (T : List (α × Option Nat)) :
    Chunked pairs ((t, none) :: T) = Chunked pairs T := by
  simp only [Chunked]

omit [DecidableEq α] in
/-- Unfolding `Chunked` at a frozen entry. -/
theorem Chunked_some (pairs : List (List α × List α)) (t : α) (j : Nat)
    (T : List (α × Option Nat)) :
    Chunked pairs ((t, some j) :: T)
      = (frozenPrefix (xlen pairs j - 1) T
          ∧ Chunked pairs (dropN (xlen pairs j - 1) T)) := by
  simp only [Chunked]

omit [DecidableEq α] in
/-- `Chunked` only depends on the frozen tail. -/
theorem Chunked_runE (pairs : List (List α × List α)) :
    ∀ (V : List α) (T : List (α × Option Nat)),
    Chunked pairs (runE V ++ T) → Chunked pairs T := by
  intro V
  induction V with
  | nil => intro T h; exact h
  | cons v V' ih =>
      intro T h
      have h' : Chunked pairs ((v, none) :: (runE V' ++ T)) := h
      rw [Chunked_none] at h'
      exact ih T h'

/-- A matching unfrozen run is consumed by `dropU?`. -/
theorem dropU?_runE_take : ∀ (X V : List α) (T2 : List (α × Option Nat)),
    V.take X.length = X → dropU? X (runE V ++ T2) = some (runE (V.drop X.length) ++ T2) := by
  intro X
  induction X with
  | nil => intro V T2 _; cases V with
    | nil => rfl
    | cons v V' => rfl
  | cons c X' ih =>
      intro V T2 h
      cases V with
      | nil => exact absurd h (by simp)
      | cons v V' =>
          have h1 : (v :: V').take (c :: X').length = v :: V'.take X'.length :=
            take_succ_cons v V' X'.length
          rw [h1] at h
          have hV : V'.take X'.length = X' := by injection h
          have hv : v = c := by injection h
          show dropU? (c :: X') ((v, none) :: (runE V' ++ T2)) = _
          rw [dropU?_cons_none, ite_eq_left hv.symm]
          exact ih V' T2 hV

/-- A pattern longer than the unfrozen run cannot match it. -/
theorem dropU?_runE_short : ∀ (X V : List α) (T2 : List (α × Option Nat)),
    V.length < X.length → (T2 = [] ∨ FrozenHead T2) →
    dropU? X (runE V ++ T2) = none := by
  intro X
  induction X with
  | nil => intro V T2 hlen _; simp only [List.length_nil] at hlen; omega
  | cons c X' ih =>
      intro V T2 hlen hT2
      cases V with
      | nil =>
          cases T2 with
          | nil => rfl
          | cons t T' =>
              obtain ⟨d, o⟩ := t
              cases o with
              | none =>
                  rcases hT2 with h | h
                  · exact absurd h (by simp)
                  · exact absurd h (by simp [FrozenHead])
              | some j => rfl
      | cons v V' =>
          have hlen' : V'.length < X'.length := by simp at hlen; omega
          show dropU? (c :: X') ((v, none) :: (runE V' ++ T2)) = none
          rw [dropU?_cons_none]
          split
          · exact ih V' T2 hlen' hT2
          · rfl

/-- The freezing pass passes a too-short unfrozen run through. -/
theorem freezePass_short (X : List α) (hX : X ≠ []) (i : Nat) :
    ∀ (V : List α) (T2 : List (α × Option Nat)), V.length < X.length →
    (T2 = [] ∨ FrozenHead T2) →
    freezePass X hX i (runE V ++ T2) = runE V ++ freezePass X hX i T2 := by
  intro V
  induction V with
  | nil => intro T2 _ _; rfl
  | cons v V' ih =>
      intro T2 hlen hT2
      have hlen' : V'.length < X.length := by simp at hlen; omega
      have hd : dropU? X ((v, none) :: (runE V' ++ T2)) = none :=
        dropU?_runE_short X (v :: V') T2 hlen hT2
      show freezePass X hX i ((v, none) :: (runE V' ++ T2)) = _
      rw [freezePass_cons_none X hX i (v, none) (runE V' ++ T2) hd]
      show (v, none) :: freezePass X hX i (runE V' ++ T2) = _
      rw [ih T2 hlen' hT2]
      rfl

/-- Unfolding `fragEnd` at an exhausted fragment. -/
theorem fragEnd_nil (b x : α) (i : Nat) (c : α) (X' : List α) :
    fragEnd b x i (c :: X') [] = [] := by
  simp only [fragEnd]

/-- The round of a fragment pushed before a marker. -/
theorem round_descend (b x : α) (i : Nat) (X : List α) (hX : X ≠ []) :
    ∀ (W : List α) (j : Nat) (ns : List (NFItem α)),
    roundNF b x i X (pushFrag W (NFItem.mark j :: ns))
      = repairNF b x i X (fragGo b x i X W j ++ renameNF b x i X ns) := by
  intro W
  cases W with
  | nil =>
      intro j ns
      show roundNF b x i X (pushFrag [] (NFItem.mark j :: ns)) = _
      rw [pushFrag_nil, roundNF_mark]
      cases X with
      | nil => exact absurd rfl hX
      | cons c X' =>
          rw [fragGo_end]
          split
          · show NFItem.mark j :: repairNF b x i (c :: X') (renameNF b x i (c :: X') ns)
                = repairNF b x i (c :: X') ([NFItem.dmg [] i j] ++ renameNF b x i (c :: X') ns)
            rw [show [NFItem.dmg [] i j] ++ renameNF b x i (c :: X') ns
                  = NFItem.dmg [] i j :: renameNF b x i (c :: X') ns from rfl,
                repairNF_dmg, pushFrag_nil]
          · show NFItem.mark j :: repairNF b x i (c :: X') (renameNF b x i (c :: X') ns)
                = repairNF b x i (c :: X') ([NFItem.mark j] ++ renameNF b x i (c :: X') ns)
            rw [show [NFItem.mark j] ++ renameNF b x i (c :: X') ns
                  = NFItem.mark j :: renameNF b x i (c :: X') ns from rfl,
                repairNF_mark]
  | cons w W' =>
      intro j ns
      show repairNF b x i X (renameNF b x i X (NFItem.frag (w :: W') :: NFItem.mark j :: ns)) = _
      rw [renameNF_frag_mark]

/-- The round of a final fragment. -/
theorem round_descend_end (b x : α) (i : Nat) (X : List α) (hX : X ≠ []) :
    ∀ (W : List α),
    roundNF b x i X (pushFrag W []) = repairNF b x i X (fragEnd b x i X W) := by
  intro W
  cases W with
  | nil =>
      show roundNF b x i X (pushFrag [] []) = _
      rw [pushFrag_nil]
      show repairNF b x i X (renameNF b x i X ([] : List (NFItem α))) = _
      cases X with
      | nil => exact absurd rfl hX
      | cons c X' => rw [fragEnd_nil]; rfl
  | cons w W' =>
      show repairNF b x i X (renameNF b x i X (NFItem.frag (w :: W') :: [])) = _
      rw [renameNF_frag_nil]

omit [DecidableEq α] in
/-- A nonempty list has positive length. -/
theorem length_pos_of_ne_nil : ∀ L : List α, L ≠ [] → 1 ≤ L.length := by
  intro L
  cases L with
  | nil => intro h; exact absurd rfl h
  | cons a L' => intro _; simp

omit [DecidableEq α] in
/-- Pushing a nonempty fragment onto an empty list. -/
theorem pushFrag_cons_nil (v : α) (V : List α) :
    pushFrag (v :: V) [] = NFItem.frag (v :: V) :: [] := rfl

omit [DecidableEq α] in
/-- Pushing a nonempty fragment onto a marker. -/
theorem pushFrag_cons_mark (v : α) (V : List α) (j : Nat) (ns : List (NFItem α)) :
    pushFrag (v :: V) (NFItem.mark j :: ns)
      = NFItem.frag (v :: V) :: NFItem.mark j :: ns := rfl

omit [DecidableEq α] in
/-- The length of a run written as entries. -/
theorem runE_length (V : List α) : (runE V).length = V.length := by
  simp [runE]

omit [DecidableEq α] in
/-- `pieces` of the empty annotated list. -/
theorem pieces_nil (pairs : List (List α × List α)) :
    pieces pairs ([] : List (α × Option Nat)) = [] := by
  simp only [pieces]

/-- A frozen head blocks the matcher at any pattern. -/
theorem dropU?_tail (c : α) (X' : List α) (T2 : List (α × Option Nat))
    (hT2 : T2 = [] ∨ FrozenHead T2) : dropU? (c :: X') T2 = none := by
  rcases hT2 with h | h
  · rw [h]; rfl
  · cases T2 with
    | nil => exact absurd h (by simp [FrozenHead])
    | cons t T'' =>
        obtain ⟨d, o⟩ := t
        cases o with
        | none => exact absurd h (by simp [FrozenHead])
        | some j => rfl

omit [DecidableEq α] in
/-- Introducing a run preserves `Chunked`. -/
theorem Chunked_runE_intro (pairs : List (List α × List α)) :
    ∀ (V : List α) (T : List (α × Option Nat)),
    Chunked pairs T → Chunked pairs (runE V ++ T) := by
  intro V
  induction V with
  | nil => intro T h; exact h
  | cons v V' ih =>
      intro T h
      show Chunked pairs ((v, none) :: (runE V' ++ T))
      rw [Chunked_none]
      exact ih T h

/-- A failed take means no match in the run. -/
theorem dropU?_runE_none : ∀ (X V : List α) (T2 : List (α × Option Nat)),
    (T2 = [] ∨ FrozenHead T2) → ¬(V.take X.length = X) →
    dropU? X (runE V ++ T2) = none := by
  intro X
  induction X with
  | nil => intro V T2 _ h; exact absurd rfl h
  | cons c X' ih =>
      intro V T2 hT2 h
      cases V with
      | nil => exact dropU?_tail c X' T2 hT2
      | cons v V' =>
          have h1 : (v :: V').take (c :: X').length = v :: V'.take X'.length :=
            take_succ_cons v V' X'.length
          show dropU? (c :: X') ((v, none) :: (runE V' ++ T2)) = none
          rw [dropU?_cons_none]
          split
          · next hcv =>
              refine ih V' T2 hT2 ?_
              intro hV
              apply h
              show (v :: V').take (c :: X').length = c :: X'
              rw [h1, hV, hcv]
          · rfl

/-- The pieces of a head match of the freezing pass. -/
theorem pieces_freeze_match (pairs : List (List α × List α)) (i : Nat) (X : List α)
    (hX : X ≠ []) (hxl : xlen pairs i = X.length) (t : α × Option Nat)
    (T' U : List (α × Option Nat)) (hd : dropU? X (t :: T') = some U) :
    pieces pairs (freezePass X hX i (t :: T'))
      = NFItem.mark i :: pieces pairs (freezePass X hX i U) := by
  rw [freezePass_cons_some X hX i t T' U hd]
  refine pieces_freezeBlock pairs i X.length hxl (length_pos_of_ne_nil X hX) (t :: T')
    (freezePass X hX i U) ?_
  have h := dropU?_length X (t :: T') U hd
  have h2 : (t :: T').length = T'.length + 1 := List.length_cons
  omega

/-- The pieces of an unmatched unfrozen head. -/
theorem pieces_freeze_skip (pairs : List (List α × List α)) (X : List α) (hX : X ≠ [])
    (i : Nat) (c : α) (T' : List (α × Option Nat))
    (hd : dropU? X ((c, none) :: T') = none) :
    pieces pairs (freezePass X hX i ((c, none) :: T'))
      = shiftItem c (pieces pairs (freezePass X hX i T')) := by
  rw [freezePass_cons_none X hX i (c, none) T' hd, pieces_none, pushFrag_single]

/-- `freezePass` of the empty annotated list. -/
theorem freezePass_nil (X : List α) (hX : X ≠ []) (i : Nat) :
    freezePass X hX i ([] : List (α × Option Nat)) = [] := by
  simp only [freezePass]

omit [DecidableEq α] in
/-- `Chunked` of the empty annotated list. -/
theorem Chunked_nil (pairs : List (List α × List α)) :
    Chunked pairs ([] : List (α × Option Nat)) := by
  simp only [Chunked]

omit [DecidableEq α] in
/-- Pushing a nonempty fragment before a marker is shifting its head
into the pushed fragment. -/
theorem pushFrag_shiftItem_mark (c : α) (W : List α) (j : Nat) (ns : List (NFItem α)) :
    pushFrag (c :: W) (NFItem.mark j :: ns)
      = shiftItem c (pushFrag W (NFItem.mark j :: ns)) := by
  cases W with
  | nil => rfl
  | cons w W' => rfl

/-- The item-level round `i` over the pieces of an annotated list is the
freezing pass of round `i`, read back as pieces. -/
theorem round_pieces (x b : α) (pairs : List (List α × List α)) (i : Nat)
    (X : List α) (hX : X ≠ []) (hxl : xlen pairs i = X.length) :
    ∀ (n : Nat) (T : List (α × Option Nat)), T.length ≤ n → Chunked pairs T →
    roundNF b x i X (pieces pairs T) = pieces pairs (freezePass X hX i T) := by
  intro n
  induction n with
  | zero =>
      intro T hT hC
      cases T with
      | nil => rw [pieces_nil, freezePass_nil, pieces_nil]; rfl
      | cons t T' => rw [List.length_cons] at hT; omega
  | succ n' ih =>
      intro T hT hC
      cases T with
      | nil => rw [pieces_nil, freezePass_nil, pieces_nil]; rfl
      | cons t T' =>
          rw [List.length_cons] at hT
          obtain ⟨c, o⟩ := t
          cases o with
          | some j =>
              rw [Chunked_some] at hC
              obtain ⟨hFP, hCD⟩ := hC
              have hdn : dropU? X ((c, some j) :: T') = none := by
                cases X with
                | nil => exact absurd rfl hX
                | cons c₀ X₀ => rfl
              rw [pieces_some, roundNF_mark, freezePass_cons_none _ _ _ _ _ hdn,
                  pieces_some, freezePass_dropN_frozen X hX i (xlen pairs j - 1) T' hFP]
              have hlen := dropN_length_le (xlen pairs j - 1) T'
              rw [ih (dropN (xlen pairs j - 1) T') (by omega) hCD]
          | none =>
              obtain ⟨W, T2, hdec, hT2⟩ :
                  ∃ (W : List α) (T2 : List (α × Option Nat)),
                    T' = runE W ++ T2
                      ∧ (T2 = []
                        ∨ ∃ (d : α) (j : Nat) (T'' : List (α × Option Nat)),
                            T2 = (d, some j) :: T'') :=
                ⟨runOf T', afterRun T', run_decomp T', afterRun_cases T'⟩
              rw [hdec] at hT ⊢
              rw [Chunked_none] at hC
              rw [hdec] at hC
              have hC2 : Chunked pairs T2 := Chunked_runE pairs W T2 hC
              have hL1 : (runE W ++ T2).length = W.length + T2.length := by
                rw [List.length_append, runE_length]
              show roundNF b x i X (pieces pairs (runE (c :: W) ++ T2))
                = pieces pairs (freezePass X hX i ((c, none) :: (runE W ++ T2)))
              rw [pieces_run]
              cases X with
              | nil => exact absurd rfl hX
              | cons c₀ X₀ =>
                  have hX1 : 1 ≤ (c₀ :: X₀).length := length_pos_of_ne_nil _ (by simp)
                  rcases hT2 with hT2nil | ⟨d, j, T'', hT2⟩
                  · -- the final fragment: `fragEnd`
                      rw [hT2nil] at hT hL1 ⊢
                      rw [pieces_nil]
                      show roundNF b x i (c₀ :: X₀) (pushFrag (c :: W)
                          ([] : List (NFItem α)))
                        = pieces pairs (freezePass (c₀ :: X₀) hX i
                            ((c, none) :: (runE W ++ ([] : List (α × Option Nat)))))
                      rw [round_descend_end b x i (c₀ :: X₀) hX (c :: W)]
                      by_cases hα : (c :: W).take (c₀ :: X₀).length = c₀ :: X₀
                      · -- alpha
                          have hdU : dropU? (c₀ :: X₀)
                              ((c, none) :: (runE W ++ ([] : List (α × Option Nat))))
                              = some (runE ((c :: W).drop (c₀ :: X₀).length)
                                  ++ ([] : List (α × Option Nat))) :=
                            dropU?_runE_take (c₀ :: X₀) (c :: W) [] hα
                          have hRlen : (c₀ :: X₀).length
                              + ((c :: W).drop (c₀ :: X₀).length).length
                              = W.length + 1 := by
                            have h1 := List.take_append_drop (c₀ :: X₀).length (c :: W)
                            rw [hα] at h1
                            have h2 := congrArg List.length h1
                            simp only [List.length_append] at h2
                            exact h2
                          rw [fragEnd_alpha b x i c₀ X₀ c W hα, repairNF_mark,
                              ← round_descend_end b x i (c₀ :: X₀) hX
                                ((c :: W).drop (c₀ :: X₀).length)]
                          have halg : pieces pairs
                              (runE ((c :: W).drop (c₀ :: X₀).length)
                                ++ ([] : List (α × Option Nat)))
                              = pushFrag ((c :: W).drop (c₀ :: X₀).length)
                                  ([] : List (NFItem α)) := by
                            rw [pieces_run, pieces_nil]
                          rw [← halg,
                              pieces_freeze_match pairs i (c₀ :: X₀) hX hxl (c, none)
                                (runE W ++ ([] : List (α × Option Nat)))
                                (runE ((c :: W).drop (c₀ :: X₀).length)
                                  ++ ([] : List (α × Option Nat))) hdU,
                              ih (runE ((c :: W).drop (c₀ :: X₀).length)
                                ++ ([] : List (α × Option Nat)))
                                (by
                                  simp only [List.length_append, runE_length]
                                  omega)
                                (Chunked_runE_intro pairs
                                  ((c :: W).drop (c₀ :: X₀).length)
                                  ([] : List (α × Option Nat)) (Chunked_nil pairs))]
                      · -- skip
                          have hdn : dropU? (c₀ :: X₀)
                              ((c, none) :: (runE W ++ ([] : List (α × Option Nat))))
                              = none :=
                            dropU?_runE_none (c₀ :: X₀) (c :: W) [] (Or.inl rfl) hα
                          rw [fragEnd_skip b x i c₀ X₀ c W hα, repairNF_shift,
                              ← round_descend_end b x i (c₀ :: X₀) hX W]
                          have halg : pieces pairs
                              (runE W ++ ([] : List (α × Option Nat)))
                              = pushFrag W ([] : List (NFItem α)) := by
                            rw [pieces_run, pieces_nil]
                          rw [← halg,
                              pieces_freeze_skip pairs (c₀ :: X₀) hX i c
                                (runE W ++ ([] : List (α × Option Nat))) hdn,
                              ih (runE W ++ ([] : List (α × Option Nat))) (by omega)
                                (Chunked_runE_intro pairs W
                                  ([] : List (α × Option Nat)) (Chunked_nil pairs))]
                  · -- a frozen head follows: `fragGo`
                      have hL3 : T2.length = T''.length + 1 := by rw [hT2]; simp
                      rw [hT2] at hC2
                      rw [Chunked_some] at hC2
                      obtain ⟨hFP, hCD⟩ := hC2
                      rw [hT2, pieces_some]
                      rw [round_descend b x i (c₀ :: X₀) hX (c :: W) j
                        (pieces pairs (dropN (xlen pairs j - 1) T''))]
                      by_cases hα : (c :: W).take (c₀ :: X₀).length = c₀ :: X₀
                      · -- alpha
                          have hdU : dropU? (c₀ :: X₀)
                              ((c, none) :: (runE W ++ ((d, some j) :: T'')))
                              = some (runE ((c :: W).drop (c₀ :: X₀).length)
                                  ++ ((d, some j) :: T'')) :=
                            dropU?_runE_take (c₀ :: X₀) (c :: W) ((d, some j) :: T'') hα
                          have hRlen : (c₀ :: X₀).length
                              + ((c :: W).drop (c₀ :: X₀).length).length
                              = W.length + 1 := by
                            have h1 := List.take_append_drop (c₀ :: X₀).length (c :: W)
                            rw [hα] at h1
                            have h2 := congrArg List.length h1
                            simp only [List.length_append] at h2
                            exact h2
                          rw [fragGo_alpha b x i c₀ X₀ c W j hα]
                          show repairNF b x i (c₀ :: X₀)
                              (NFItem.mark i
                                :: (fragGo b x i (c₀ :: X₀)
                                      ((c :: W).drop (c₀ :: X₀).length) j
                                    ++ renameNF b x i (c₀ :: X₀)
                                      (pieces pairs (dropN (xlen pairs j - 1) T''))))
                            = pieces pairs (freezePass (c₀ :: X₀) hX i
                                ((c, none) :: (runE W ++ ((d, some j) :: T''))))
                          rw [repairNF_mark,
                              ← round_descend b x i (c₀ :: X₀) hX
                                ((c :: W).drop (c₀ :: X₀).length) j
                                (pieces pairs (dropN (xlen pairs j - 1) T''))]
                          have halg : pieces pairs
                              (runE ((c :: W).drop (c₀ :: X₀).length)
                                ++ ((d, some j) :: T''))
                              = pushFrag ((c :: W).drop (c₀ :: X₀).length)
                                  (NFItem.mark j
                                    :: pieces pairs (dropN (xlen pairs j - 1) T'')) := by
                            rw [pieces_run, pieces_some]
                          rw [← halg,
                              pieces_freeze_match pairs i (c₀ :: X₀) hX hxl (c, none)
                                (runE W ++ ((d, some j) :: T''))
                                (runE ((c :: W).drop (c₀ :: X₀).length)
                                  ++ ((d, some j) :: T'')) hdU,
                              ih (runE ((c :: W).drop (c₀ :: X₀).length)
                                ++ ((d, some j) :: T''))
                                (by
                                  have hB : (runE ((c :: W).drop (c₀ :: X₀).length)
                                      ++ ((d, some j) :: T'')).length
                                      = ((c :: W).drop (c₀ :: X₀).length).length
                                        + (T''.length + 1) := by
                                    rw [List.length_append, runE_length,
                                      show ((d, some j) :: T'').length
                                        = T''.length + 1 from rfl]
                                  omega)
                                (Chunked_runE_intro pairs
                                  ((c :: W).drop (c₀ :: X₀).length)
                                  ((d, some j) :: T'')
                                  (by rw [Chunked_some]; exact ⟨hFP, hCD⟩))]
                      · -- gamma or skip
                          by_cases hγ : (c₀ :: X₀) = (c :: W) ++ [b]
                          · -- gamma
                              have hdn : dropU? (c₀ :: X₀)
                                  ((c, none) :: (runE W ++ ((d, some j) :: T'')))
                                  = none :=
                                dropU?_runE_none (c₀ :: X₀) (c :: W)
                                  ((d, some j) :: T'') (Or.inr (by exact True.intro)) hα
                              have hshort : W.length < (c₀ :: X₀).length := by
                                rw [hγ, List.length_append, List.length_cons,
                                  List.length_singleton]
                                omega
                              rw [fragGo_gamma b x i c₀ X₀ c W j hα hγ]
                              show repairNF b x i (c₀ :: X₀)
                                  (NFItem.dmg (c :: W) i j
                                    :: renameNF b x i (c₀ :: X₀)
                                      (pieces pairs (dropN (xlen pairs j - 1) T'')))
                                = pieces pairs (freezePass (c₀ :: X₀) hX i
                                    ((c, none) :: (runE W ++ ((d, some j) :: T''))))
                              rw [repairNF_dmg]
                              show pushFrag (c :: W) (NFItem.mark j
                                  :: roundNF b x i (c₀ :: X₀)
                                    (pieces pairs (dropN (xlen pairs j - 1) T'')))
                                = pieces pairs (freezePass (c₀ :: X₀) hX i
                                    ((c, none) :: (runE W ++ ((d, some j) :: T''))))
                              have hR : pieces pairs
                                  (freezePass (c₀ :: X₀) hX i
                                    ((c, none) :: (runE W ++ ((d, some j) :: T''))))
                                  = shiftItem c (pushFrag W (NFItem.mark j
                                      :: pieces pairs
                                        (freezePass (c₀ :: X₀) hX i
                                          (dropN (xlen pairs j - 1) T'')))) := by
                                have hd1 : dropU? (c₀ :: X₀)
                                    ((d, some j) :: T'') = none := rfl
                                rw [freezePass_cons_none (c₀ :: X₀) hX i (c, none)
                                    (runE W ++ ((d, some j) :: T'')) hdn,
                                  freezePass_short (c₀ :: X₀) hX i W
                                    ((d, some j) :: T'') hshort
                                    (Or.inr (by exact True.intro)),
                                  freezePass_cons_none (c₀ :: X₀) hX i (d, some j)
                                    T'' hd1,
                                  pieces_none, pushFrag_single, pieces_run, pieces_some,
                                  freezePass_dropN_frozen (c₀ :: X₀) hX i
                                    (xlen pairs j - 1) T'' hFP]
                              have hlen := dropN_length_le (xlen pairs j - 1) T''
                              rw [ih (dropN (xlen pairs j - 1) T'') (by omega) hCD, hR]
                              exact pushFrag_shiftItem_mark c W j _
                          · -- skip
                              have hdn : dropU? (c₀ :: X₀)
                                  ((c, none) :: (runE W ++ ((d, some j) :: T'')))
                                  = none :=
                                dropU?_runE_none (c₀ :: X₀) (c :: W)
                                  ((d, some j) :: T'') (Or.inr (by exact True.intro)) hα
                              rw [fragGo_skip b x i c₀ X₀ c W j hα hγ,
                                  shiftItem_append c (fragGo b x i (c₀ :: X₀) W j)
                                    (renameNF b x i (c₀ :: X₀)
                                      (pieces pairs (dropN (xlen pairs j - 1) T'')))
                                    (fragGo_ne b x i (c₀ :: X₀) hX W.length W
                                      (Nat.le_refl _) j),
                                  repairNF_shift,
                                  ← round_descend b x i (c₀ :: X₀) hX W j
                                    (pieces pairs (dropN (xlen pairs j - 1) T''))]
                              have halg : pieces pairs (runE W ++ T2)
                                  = pushFrag W (NFItem.mark j
                                      :: pieces pairs (dropN (xlen pairs j - 1) T'')) := by
                                rw [pieces_run, hT2, pieces_some]
                              rw [← halg,
                                  pieces_freeze_skip pairs (c₀ :: X₀) hX i c
                                    (runE W ++ ((d, some j) :: T'')) hdn,
                                  ih (runE W ++ T2) (by omega)
                                    (Chunked_runE_intro pairs W T2
                                      (by rw [hT2, Chunked_some]; exact ⟨hFP, hCD⟩)),
                                  hT2]

/-- A prefix of `k` entries, all frozen with tag exactly `j`. -/
def purePrefix : Nat → Nat → List (α × Option Nat) → Prop
  | _, 0, _ => True
  | _, _ + 1, [] => False
  | j, k + 1, (_, some j') :: T' => j' = j ∧ purePrefix j k T'
  | _, _ + 1, (_, none) :: _ => False

/-- The strong chunk invariant: every frozen run is pure (a single
round's tag) and a concatenation of whole `|X_j|`-chunks. -/
def PureChunked (pairs : List (List α × List α)) : List (α × Option Nat) → Prop
  | [] => True
  | (_t, none) :: T' => PureChunked pairs T'
  | (_t, some j) :: T' =>
      purePrefix j (xlen pairs j - 1) T'
        ∧ PureChunked pairs (dropN (xlen pairs j - 1) T')
  termination_by T => T.length
  decreasing_by
    · simp only [List.length_cons]; omega
    · have h := dropN_length_le (xlen pairs j - 1) T'
      simp only [List.length_cons] at h ⊢
      omega

omit [DecidableEq α] in
/-- Unfolding `PureChunked` at an unfrozen entry. -/
theorem PureChunked_none (pairs : List (List α × List α)) (t : α)
    (T : List (α × Option Nat)) :
    PureChunked pairs ((t, none) :: T) = PureChunked pairs T := by
  simp only [PureChunked]

omit [DecidableEq α] in
/-- Unfolding `PureChunked` at a frozen entry. -/
theorem PureChunked_some (pairs : List (List α × List α)) (t : α) (j : Nat)
    (T : List (α × Option Nat)) :
    PureChunked pairs ((t, some j) :: T)
      = (purePrefix j (xlen pairs j - 1) T
          ∧ PureChunked pairs (dropN (xlen pairs j - 1) T)) := by
  simp only [PureChunked]

omit [DecidableEq α] in
/-- `PureChunked` of the empty annotated list. -/
theorem PureChunked_nil (pairs : List (List α × List α)) :
    PureChunked pairs ([] : List (α × Option Nat)) := by
  simp only [PureChunked]

omit [DecidableEq α] in
/-- A pure prefix is frozen. -/
theorem purePrefix_frozen : ∀ (j k : Nat) (T : List (α × Option Nat)),
    purePrefix j k T → frozenPrefix k T := by
  intro j k
  induction k with
  | zero => intro T _; exact trivial
  | succ k' ih =>
      intro T h
      cases T with
      | nil => exact False.elim h
      | cons t T' =>
          obtain ⟨c, o⟩ := t
          cases o with
          | none => exact False.elim h
          | some j' =>
              obtain ⟨_, hrest⟩ := h
              exact ih T' hrest

omit [DecidableEq α] in
/-- A pure prefix stays a pure prefix when a tail is appended. -/
theorem purePrefix_app : ∀ (j k : Nat) (F L : List (α × Option Nat)),
    purePrefix j k F → purePrefix j k (F ++ L) := by
  intro j k
  induction k with
  | zero => intro F L _; exact trivial
  | succ k' ih =>
      intro F L h
      cases F with
      | nil => exact False.elim h
      | cons t F' =>
          obtain ⟨c, o⟩ := t
          cases o with
          | none => exact False.elim h
          | some j' =>
              obtain ⟨hj, hrest⟩ := h
              exact ⟨hj, ih F' L hrest⟩

omit [DecidableEq α] in
/-- Splitting off a pure prefix. -/
theorem purePrefix_split : ∀ (j k : Nat) (T : List (α × Option Nat)),
    purePrefix j k T → ∃ F U, T = F ++ U ∧ F.length = k
      ∧ purePrefix j k F ∧ AllFrozen F := by
  intro j k
  induction k with
  | zero => intro T _; exact ⟨[], T, rfl, rfl, trivial, trivial⟩
  | succ k' ih =>
      intro T h
      cases T with
      | nil => exact False.elim h
      | cons t T' =>
          obtain ⟨c, o⟩ := t
          cases o with
          | none => exact False.elim h
          | some j' =>
              obtain ⟨hj, hrest⟩ := h
              obtain ⟨F, U, hT', hF, hP, hA⟩ := ih T' hrest
              refine ⟨(c, some j') :: F, U, by rw [hT']; rfl, ?_, ⟨hj, hP⟩, ?_⟩
              · simp [hF]
              · exact hA

/-- A freezing pass preserves pure prefixes. -/
theorem freezePass_purePrefix (X : List α) (hX : X ≠ []) (i j k : Nat) :
    ∀ T : List (α × Option Nat), purePrefix j k T →
    purePrefix j k (freezePass X hX i T) := by
  intro T h
  obtain ⟨F, U, hT, hF, hP, hA⟩ := purePrefix_split j k T h
  rw [hT, freezePass_frozen X hX i F U hA]
  exact purePrefix_app j k F _ hP

/-- Peeling a matched unfrozen block preserves the strong invariant. -/
theorem PureChunked_dropU (pairs : List (List α × List α)) :
    ∀ (n : Nat) (X : List α) (L U : List (α × Option Nat)), L.length ≤ n →
    dropU? X L = some U → PureChunked pairs L → PureChunked pairs U := by
  intro n
  induction n with
  | zero =>
      intro X L U hL
      cases L with
      | nil =>
          intro hd hC
          cases X with
          | nil =>
              have hd2 : some ([] : List (α × Option Nat)) = some U := hd
              injection hd2 with hd'
              subst hd'
              exact hC
          | cons c₀ X₀ =>
              have hd2 : none = some U := hd
              exact absurd hd2 (by simp)
      | cons t L' => rw [List.length_cons] at hL; omega
  | succ n' ih =>
      intro X L U hL hd hC
      cases L with
      | nil =>
          cases X with
          | nil =>
              have hd2 : some ([] : List (α × Option Nat)) = some U := hd
              injection hd2 with hd'
              subst hd'
              exact hC
          | cons c₀ X₀ =>
              have hd2 : none = some U := hd
              exact absurd hd2 (by simp)
      | cons t L' =>
          rw [List.length_cons] at hL
          obtain ⟨c, o⟩ := t
          cases o with
          | some j =>
              cases X with
              | nil =>
                  have hd2 : some ((c, some j) :: L') = some U := hd
                  injection hd2 with hd'
                  subst hd'
                  exact hC
              | cons c₀ X₀ =>
                  rw [dropU?_cons_some] at hd
                  exact absurd hd (by simp)
          | none =>
              cases X with
              | nil =>
                  have hd2 : some ((c, none) :: L') = some U := hd
                  injection hd2 with hd'
                  subst hd'
                  rw [PureChunked_none] at hC
                  rw [PureChunked_none]
                  exact hC
              | cons c₀ X₀ =>
                  rw [PureChunked_none] at hC
                  rw [dropU?_cons_none] at hd
                  by_cases hcc : c₀ = c
                  · rw [ite_eq_left hcc] at hd
                    exact ih X₀ L' U (by omega) hd hC
                  · rw [ite_eq_right hcc] at hd
                    exact absurd hd (by simp)

omit [DecidableEq α] in
/-- A `freezeBlock` is a pure prefix of round-`i` entries. -/
theorem purePrefix_freezeBlock (i : Nat) : ∀ (m : Nat) (T : List (α × Option Nat)),
    m ≤ T.length → purePrefix i m (freezeBlock i m T) := by
  intro m
  induction m with
  | zero => intro T _; exact trivial
  | succ m' ih =>
      intro T h
      cases T with
      | nil => simp at h
      | cons t T' =>
          have hlen : m' ≤ T'.length := by rw [List.length_cons] at h; omega
          exact ⟨rfl, ih T' hlen⟩

omit [DecidableEq α] in
/-- The strong invariant implies the weak one. -/
theorem PureChunked_imp_Chunked (pairs : List (List α × List α)) :
    ∀ (n : Nat) (T : List (α × Option Nat)), T.length ≤ n →
    PureChunked pairs T → Chunked pairs T := by
  intro n
  induction n with
  | zero =>
      intro T hT
      cases T with
      | nil => intro _; exact Chunked_nil pairs
      | cons t T' => rw [List.length_cons] at hT; omega
  | succ n' ih =>
      intro T hT hC
      cases T with
      | nil => exact Chunked_nil pairs
      | cons t T' =>
          rw [List.length_cons] at hT
          obtain ⟨c, o⟩ := t
          cases o with
          | none =>
              rw [PureChunked_none] at hC
              rw [Chunked_none]
              exact ih T' (by omega) hC
          | some j =>
              rw [PureChunked_some] at hC
              obtain ⟨hPP, hCD⟩ := hC
              rw [Chunked_some]
              have hlen := dropN_length_le (xlen pairs j - 1) T'
              exact ⟨purePrefix_frozen j (xlen pairs j - 1) T' hPP,
                ih _ (by omega) hCD⟩

omit [DecidableEq α] in
/-- Introducing a run preserves the strong invariant. -/
theorem PureChunked_runE_intro (pairs : List (List α × List α)) :
    ∀ (V : List α) (T : List (α × Option Nat)),
    PureChunked pairs T → PureChunked pairs (runE V ++ T) := by
  intro V
  induction V with
  | nil => intro T h; exact h
  | cons v V' ih =>
      intro T h
      show PureChunked pairs ((v, none) :: (runE V' ++ T))
      rw [PureChunked_none]
      exact ih T h

/-- The freezing pass preserves the strong chunk invariant. -/
theorem PureChunked_freezePass (pairs : List (List α × List α)) (X : List α)
    (hX : X ≠ []) (i : Nat) (hxl : xlen pairs i = X.length) :
    ∀ (n : Nat) (T : List (α × Option Nat)), T.length ≤ n →
    PureChunked pairs T → PureChunked pairs (freezePass X hX i T) := by
  intro n
  induction n with
  | zero =>
      intro T hT
      cases T with
      | nil => intro _; rw [freezePass_nil]; exact PureChunked_nil pairs
      | cons t T' => rw [List.length_cons] at hT; omega
  | succ n' ih =>
      intro T hT hC
      cases T with
      | nil => rw [freezePass_nil]; exact PureChunked_nil pairs
      | cons t T' =>
          rw [List.length_cons] at hT
          obtain ⟨c, o⟩ := t
          cases o with
          | some j =>
              have hdn : dropU? X ((c, some j) :: T') = none := by
                cases X with
                | nil => exact absurd rfl hX
                | cons c₀ X₀ => rfl
              rw [PureChunked_some] at hC
              obtain ⟨hPP, hCD⟩ := hC
              rw [freezePass_cons_none _ _ _ _ _ hdn, PureChunked_some]
              have hlen := dropN_length_le (xlen pairs j - 1) T'
              refine ⟨freezePass_purePrefix X hX i j (xlen pairs j - 1) T' hPP, ?_⟩
              rw [freezePass_dropN_frozen X hX i (xlen pairs j - 1) T'
                (purePrefix_frozen j (xlen pairs j - 1) T' hPP)]
              exact ih _ (by omega) hCD
          | none =>
              rw [PureChunked_none] at hC
              cases hd : dropU? X ((c, none) :: T') with
              | none =>
                  rw [freezePass_cons_none _ _ _ _ _ hd, PureChunked_none]
                  exact ih T' (by omega) hC
              | some U =>
                  rw [freezePass_cons_some _ _ _ _ _ _ hd]
                  have hX1 : 1 ≤ X.length := length_pos_of_ne_nil X hX
                  obtain ⟨m, hm⟩ : ∃ m, X.length = m + 1 :=
                    Nat.exists_eq_succ_of_ne_zero (by omega)
                  have him : xlen pairs i - 1 = m := by omega
                  have hlenU := dropU?_length X ((c, none) :: T') U hd
                  have hL : ((c, none) :: T').length = T'.length + 1 := rfl
                  have hlenB : m ≤ T'.length := by omega
                  rw [hm]
                  show PureChunked pairs
                    ((c, some i) :: (freezeBlock i m T' ++ freezePass X hX i U))
                  rw [PureChunked_some, him]
                  refine ⟨purePrefix_app i m (freezeBlock i m T')
                    (freezePass X hX i U) (purePrefix_freezeBlock i m T' hlenB), ?_⟩
                  rw [dropN_length (freezePass X hX i U) m (freezeBlock i m T')
                    (freezeBlock_length i m T' hlenB)]
                  exact ih U (by omega) (PureChunked_dropU pairs
                    ((c, none) :: T').length X ((c, none) :: T') U (Nat.le_refl _) hd
                    (by rw [PureChunked_none]; exact hC))

/-- The head of a dropped suffix is in the list. -/
theorem drop_head_mem : ∀ (L : List β) (k : Nat) (p : β) (ps' : List β),
    L.drop k = p :: ps' → p ∈ L := by
  intro L k
  induction k generalizing L with
  | zero =>
      intro p ps' h
      rw [List.drop_zero] at h
      subst h
      exact List.mem_cons_self ..
  | succ k' ih =>
      intro p ps' h
      cases L with
      | nil => simp at h
      | cons a L' =>
          have h2 : L'.drop k' = p :: ps' := h
          exact List.mem_cons_of_mem a (ih L' p ps' h2)

/-- Dropping one more past a cons-shaped drop. -/
theorem drop_succ_of_cons : ∀ (L : List β) (k : Nat) (p : β) (ps' : List β),
    L.drop k = p :: ps' → L.drop (k + 1) = ps' := by
  intro L k p ps' h
  have h2 : (L.drop k).drop 1 = L.drop (k + 1) := List.drop_drop
  rw [h] at h2
  exact h2.symm

/-- The head of a dropped suffix is the indexed entry. -/
theorem drop_head_getD : ∀ (L : List β) (k : Nat) (p : β) (ps' : List β) (d : β),
    L.drop k = p :: ps' → L.getD k d = p := by
  intro L k
  induction k generalizing L with
  | zero =>
      intro p ps' d h
      rw [List.drop_zero] at h
      subst h
      rfl
  | succ k' ih =>
      intro p ps' d h
      cases L with
      | nil => simp at h
      | cons a L' =>
          have h2 : L'.drop k' = p :: ps' := h
          exact ih L' p ps' d h2

/-! ### The construction over `enc2` directly

  `enc2Pass_eq` and `dec2Pass_enc2` (both proven above) bridge the
  pass-composition definitions to the block map `enc2`.  We record the
  construction in `enc2` form; the remaining work is purely about `subst`
  over texts that are concatenations of `enc2`-images and markers. -/

/-- The rename/repair rounds, `i = 1..n`, with the code layer bridged to
`enc2` (see `renameRepair2_eq`). -/
def renameRR (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (Xi, _) :: ps, T =>
      renameRR b x (i + 1) ps
        (subst (enc2 x Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc2 x Xi) T))

/-- The instantiation passes, `i = n..1`, in `enc2` form (see
`instantiate2_eq`). -/
def instRR (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (_, Yi) :: ps, T => instRR b x (i - 1) ps (subst (enc2 x Yi) (marker x b (i + 1)) T)

/-- The rename/repair rounds on the item layer, mirroring `renameRR`
one round at a time. -/
def renLoop (b x : α) : Nat → List (List α × List α) → List (NFItem α) → List (NFItem α)
  | _, [], ns => ns
  | i, (Xi, _) :: ps, ns =>
      renLoop b x (i + 1) ps (repairNF b x i Xi (renameNF b x i Xi ns))

/-- Unfolding `renLoop` on a round. -/
theorem renLoop_cons (b x : α) (i : Nat) (Xi Yi : List α) (ps : List (List α × List α))
    (ns : List (NFItem α)) :
    renLoop b x i ((Xi, Yi) :: ps) ns =
      renLoop b x (i + 1) ps (repairNF b x i Xi (renameNF b x i Xi ns)) := rfl

/-- The item-level rename rounds compute the pieces of the freezing
rounds over the annotated list. -/
theorem renLoop_markRounds (b x : α) (pairs : List (List α × List α))
    (hne : ∀ p ∈ pairs, p.1 ≠ []) :
    ∀ (ps : List (List α × List α)) (i : Nat), ps = pairs.drop (i - 1) → 1 ≤ i →
    ∀ (n : Nat) (A : List (α × Option Nat)), A.length ≤ n →
    PureChunked pairs A →
    renLoop b x i ps (pieces pairs A) = pieces pairs (markRounds ps i A) := by
  intro ps
  induction ps with
  | nil => intro i _ _ n A _ _; rfl
  | cons p ps' ih =>
      intro i hps hi n A hA hC
      obtain ⟨Xi, Yi⟩ := p
      have hmem : (Xi, Yi) ∈ pairs :=
        drop_head_mem pairs (i - 1) (Xi, Yi) ps' hps.symm
      have hXi : Xi ≠ [] := hne (Xi, Yi) hmem
      have hxl : xlen pairs i = Xi.length := by
        simp only [xlen]
        rw [drop_head_getD pairs (i - 1) (Xi, Yi) ps' ([], []) hps.symm]
      have hps2 : ps' = pairs.drop i := by
        have h3 := drop_succ_of_cons pairs (i - 1) (Xi, Yi) ps' hps.symm
        have h4 : i - 1 + 1 = i := by omega
        rw [h4] at h3
        exact h3.symm
      rw [renLoop_cons]
      show renLoop b x (i + 1) ps' (roundNF b x i Xi (pieces pairs A))
        = pieces pairs (markRounds ((Xi, Yi) :: ps') i A)
      have hMR : markRounds ((Xi, Yi) :: ps') i A
          = markRounds ps' (i + 1) (freezePass Xi hXi i A) := by
        simp only [markRounds]
        rw [dite_eq_right hXi]
      rw [hMR, round_pieces x b pairs i Xi hXi hxl A.length A (Nat.le_refl _)
        (PureChunked_imp_Chunked pairs A.length A (Nat.le_refl _) hC),
        ih (i + 1) hps2 (by omega) (freezePass Xi hXi i A).length
          (freezePass Xi hXi i A) (Nat.le_refl _)
          (PureChunked_freezePass pairs Xi hXi i hxl A.length A (Nat.le_refl _) hC)]

/-- Unfolding `renameRR` on a round. -/
theorem renameRR_cons (b x : α) (i : Nat) (Xi Yi : List α) (ps : List (List α × List α))
    (T : List α) :
    renameRR b x i ((Xi, Yi) :: ps) T =
      renameRR b x (i + 1) ps
        (subst (enc2 x Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc2 x Xi) T)) := rfl

/-- The item-level rounds compute the `renameRR` text. -/
theorem renLoop_scan (x b : α) (hxb : x ≠ b) :
    ∀ (ps : List (List α × List α)), (∀ p ∈ ps, p.1 ≠ []) → ∀ (i : Nat), 1 ≤ i →
    ∀ (ns : List (NFItem α)), CanonB (i - 1) ns →
    itext b x (renLoop b x i ps ns) = renameRR b x i ps (itext b x ns) := by
  intro ps
  induction ps with
  | nil => intro _ _ _ _ _; rfl
  | cons p ps ih =>
      intro hne i hi ns hC
      obtain ⟨Xi, Yi⟩ := p
      have hXi : Xi ≠ [] := hne (Xi, Yi) (by simp)
      have hR1 := renameNF_scan x b hxb i Xi hXi ns.length ns (Nat.le_refl _) hC
      have hRd := renameNF_rounded b x i Xi hXi hi ns.length ns (Nat.le_refl _) hC
      have hR2 := repairNF_scan x b hxb i Xi (renameNF b x i Xi ns).length
        (renameNF b x i Xi ns) (Nat.le_refl _) hRd
      rw [← hR1] at hR2
      rw [renLoop_cons, renameRR_cons, hR2]
      exact ih (fun p hp => hne p (List.mem_cons.mpr (Or.inr hp))) (i + 1) (by omega)
        (repairNF b x i Xi (renameNF b x i Xi ns))
        (repairNF_canon b x i Xi (renameNF b x i Xi ns).length
          (renameNF b x i Xi ns) (Nat.le_refl _) hRd)

/-- The item-level rounds keep the list canonical, with markers at
most the last round's index. -/
theorem renLoop_canon (b x : α) :
    ∀ (ps : List (List α × List α)), (∀ p ∈ ps, p.1 ≠ []) → ∀ (i : Nat), 1 ≤ i →
    ∀ (ns : List (NFItem α)), CanonB (i - 1) ns →
    CanonB (i - 1 + ps.length) (renLoop b x i ps ns) := by
  intro ps
  induction ps with
  | nil => intro _ _ _ ns hC; exact hC
  | cons p ps ih =>
      intro hne i hi ns hC
      obtain ⟨Xi, Yi⟩ := p
      have hXi : Xi ≠ [] := hne (Xi, Yi) (by simp)
      have hRd := renameNF_rounded b x i Xi hXi hi ns.length ns (Nat.le_refl _) hC
      have hRound : CanonB i (repairNF b x i Xi (renameNF b x i Xi ns)) :=
        repairNF_canon b x i Xi (renameNF b x i Xi ns).length
          (renameNF b x i Xi ns) (Nat.le_refl _) hRd
      have hidx : i - 1 + ((Xi, Yi) :: ps).length = (i + 1) - 1 + ps.length := by
        simp only [List.length_cons]
        omega
      rw [renLoop_cons, hidx]
      exact ih (fun p hp => hne p (List.mem_cons.mpr (Or.inr hp))) (i + 1) (by omega)
        (repairNF b x i Xi (renameNF b x i Xi ns)) hRound

/-- The instantiation rounds on the item layer, mirroring `instRR`. -/
def insLoop (b x : α) : Nat → List (List α × List α) → List (NFItem α) → List (NFItem α)
  | _, [], ns => ns
  | i, (_, Yi) :: ps, ns => insLoop b x (i - 1) ps (instNF b x i Yi ns)

omit [DecidableEq α] in
/-- Unfolding `insLoop` on a round. -/
theorem insLoop_cons (b x : α) (i : Nat) (Xi Yi : List α) (ps : List (List α × List α))
    (ns : List (NFItem α)) :
    insLoop b x i ((Xi, Yi) :: ps) ns = insLoop b x (i - 1) ps (instNF b x i Yi ns) := rfl

omit [DecidableEq α] in
/-- A leading fragment passes through the instantiation rounds. -/
theorem insLoop_frag (b x : α) :
    ∀ (ps : List (List α × List α)) (i : Nat) (P : List α) (ns : List (NFItem α)),
    itext b x (insLoop b x i ps (NFItem.frag P :: ns))
      = enc2 x P ++ itext b x (insLoop b x i ps ns) := by
  intro ps
  induction ps with
  | nil => intro i P ns; rfl
  | cons p ps' ih =>
      intro i P ns
      obtain ⟨Xi, Yi⟩ := p
      simp only [insLoop_cons]
      rw [instNF_frag_cons]
      exact ih (i - 1) P (instNF b x i Yi ns)

omit [DecidableEq α] in
/-- A pushed fragment passes through the instantiation rounds. -/
theorem insLoop_push (b x : α) :
    ∀ (ps : List (List α × List α)) (i : Nat) (P : List α) (ns : List (NFItem α)),
    itext b x (insLoop b x i ps (pushFrag P ns))
      = enc2 x P ++ itext b x (insLoop b x i ps ns) := by
  intro ps
  induction ps with
  | nil =>
      intro i P ns
      exact itext_push b x P ns
  | cons p ps' ih =>
      intro i P ns
      obtain ⟨Xi, Yi⟩ := p
      simp only [insLoop_cons]
      by_cases hP : P = []
      · rw [hP, pushFrag_nil, enc2_nil, List.nil_append]
      · cases ns with
        | nil =>
            have hp : pushFrag P ([] : List (NFItem α)) = NFItem.frag P :: [] := by
              simp only [pushFrag]
              rw [ite_eq_right hP]
            rw [hp, instNF_frag_cons, insLoop_frag]
        | cons n ns' =>
            cases n with
            | frag W =>
                have hp : pushFrag P (NFItem.frag W :: ns')
                    = NFItem.frag (P ++ W) :: ns' := rfl
                rw [hp, instNF_frag_cons, instNF_frag_cons, insLoop_frag,
                  insLoop_frag, enc2_append, List.append_assoc]
            | mark j =>
                have hp : pushFrag P (NFItem.mark j :: ns')
                    = NFItem.frag P :: NFItem.mark j :: ns' := by
                  simp only [pushFrag]
                  rw [ite_eq_right hP]
                rw [hp, instNF_frag_cons, insLoop_frag]
            | dmg W j k =>
                have hp : pushFrag P (NFItem.dmg W j k :: ns')
                    = NFItem.frag P :: NFItem.dmg W j k :: ns' := by
                  simp only [pushFrag]
                  rw [ite_eq_right hP]
                rw [hp, instNF_frag_cons, insLoop_frag]

omit [DecidableEq α] in
/-- Unfrozen runs pass through `assemble`. -/
theorem assemble_runE (pairs : List (List α × List α)) :
    ∀ (V : List α) (T : List (α × Option Nat)),
    assemble pairs (runE V ++ T) = V ++ assemble pairs T := by
  intro V
  induction V with
  | nil => intro T; rfl
  | cons v V' ih =>
      intro T
      have hr : runE (v :: V') = (v, none) :: runE V' := rfl
      rw [hr, List.cons_append]
      simp only [assemble]
      rw [ih T]
      rfl

omit [DecidableEq α] in
/-- Unfolding `insLoop` on a round, projecting the image. -/
theorem insLoop_cons' (b x : α) (i : Nat) (p : List α × List α) (ps : List (List α × List α))
    (ns : List (NFItem α)) :
    insLoop b x i (p :: ps) ns = insLoop b x (i - 1) ps (instNF b x i p.2 ns) := by
  obtain ⟨Xi, Yi⟩ := p
  rfl

/-- The head of the reversed prefix is the round's pair. -/
theorem take_reverse_cons : ∀ (pairs : List (List α × List α)) (i : Nat),
    i + 1 ≤ pairs.length →
    (pairs.take (i + 1)).reverse = pairs.getD i ([], []) :: (pairs.take i).reverse := by
  intro pairs i
  induction i generalizing pairs with
  | zero =>
      intro h
      cases pairs with
      | nil => simp only [List.length_nil] at h; omega
      | cons p ps => rfl
  | succ i' ih =>
      intro h
      cases pairs with
      | nil => simp only [List.length_nil] at h; omega
      | cons p ps =>
          have hps : i' + 1 ≤ ps.length := by
            simp only [List.length_cons] at h
            omega
          have hIH := ih ps hps
          have ht1 : (p :: ps).take (i' + 1 + 1) = p :: ps.take (i' + 1) := rfl
          have ht2 : (p :: ps).take (i' + 1) = p :: ps.take i' := rfl
          have hg : (p :: ps).getD (i' + 1) ([], []) = ps.getD i' ([], []) := rfl
          rw [ht1, hg, ht2, List.reverse_cons, List.reverse_cons, hIH, List.cons_append]

/-- A marker contributes the image of its round through the rounds. -/
theorem insLoop_mark (b x : α) (pairs : List (List α × List α)) :
    ∀ (i : Nat) (ps : List (List α × List α)),
    ps = (pairs.take i).reverse → 1 ≤ i → i ≤ pairs.length →
    ∀ (j : Nat) (ns0 : List (NFItem α)), 1 ≤ j → j ≤ i →
    itext b x (insLoop b x i ps (NFItem.mark j :: ns0))
      = enc2 x (pairs.getD (j - 1) ([], [])).2 ++ itext b x (insLoop b x i ps ns0) := by
  intro i
  induction i with
  | zero => intro ps hps hi1; omega
  | succ i' ih =>
      intro ps hps hi1 hi2 j ns0 hj1 hj2
      have hHead := take_reverse_cons pairs i' (by omega)
      by_cases hj : j = i' + 1
      · subst hj
        rw [Nat.add_sub_cancel, hps, hHead]
        simp only [insLoop_cons']
        rw [instNF_mark_fire, insLoop_push]
      · have hj' : j ≤ i' := by omega
        rw [hps, hHead]
        simp only [insLoop_cons']
        rw [instNF_mark_pass b x (i' + 1) (pairs.getD i' ([], [])).2 j ns0 hj]
        exact ih ((pairs.take i').reverse) rfl (by omega) (by omega) j
          (instNF b x (i' + 1) (pairs.getD i' ([], [])).2 ns0) hj1 hj'

/-- A defaulted entry inside range belongs to the list. -/
theorem getD_lt_mem {β : Type} : ∀ (L : List β) (k : Nat) (d : β), k < L.length →
    L.getD k d ∈ L := by
  intro L k d h
  have hlen : (L.drop k).length = L.length - k := List.length_drop
  have hpos : 0 < (L.drop k).length := by omega
  cases hdrop : L.drop k with
  | nil =>
      rw [hdrop] at hpos
      simp at hpos
  | cons p ps' =>
      rw [drop_head_getD L k p ps' d hdrop]
      exact drop_head_mem L k p ps' hdrop

omit [DecidableEq α] in
/-- `dropN` is the standard drop. -/
theorem dropN_eq_drop : ∀ (k : Nat) (T : List (α × Option Nat)),
    dropN k T = List.drop k T := by
  intro k
  induction k with
  | zero => intro T; rfl
  | succ k' ih =>
      intro T
      cases T with
      | nil => rfl
      | cons t T' =>
          show dropN k' T' = List.drop (k' + 1) (t :: T')
          rw [ih T']
          rfl

omit [DecidableEq α] in
/-- Dropping an additive amount. -/
theorem dropN_add : ∀ (a b : Nat) (T : List (α × Option Nat)),
    dropN (a + b) T = dropN b (dropN a T) := by
  intro a b T
  rw [dropN_eq_drop, dropN_eq_drop, dropN_eq_drop, List.drop_drop, ← dropN_eq_drop]

omit [DecidableEq α] in
/-- One more entry of the same round. -/
theorem runLen_self_cons (j : Nat) : ∀ (c : α) (X : List (α × Option Nat)),
    runLen j ((c, some j) :: X) = runLen j X + 1 := by
  intro c X
  show (if j = j then runLen j X + 1 else 0) = runLen j X + 1
  split
  · rfl
  · rename_i h
    exact absurd rfl h

omit [DecidableEq α] in
/-- The run length over a pure prefix. -/
theorem runLen_app : ∀ (j k : Nat) (T U : List (α × Option Nat)),
    purePrefix j k T → T.length = k → runLen j (T ++ U) = k + runLen j U := by
  intro j k
  induction k with
  | zero =>
      intro T U _ hT
      cases T with
      | nil => rw [Nat.zero_add]; rfl
      | cons t T' =>
          simp only [List.length_cons] at hT
          omega
  | succ k' ih =>
      intro T U h hT
      cases T with
      | nil => exact False.elim h
      | cons t T' =>
          obtain ⟨c, o⟩ := t
          cases o with
          | none => exact False.elim h
          | some j' =>
              obtain ⟨hj, hrest⟩ := h
              have hT' : T'.length = k' := by
                simp only [List.length_cons] at hT
                omega
              rw [hj, List.cons_append, runLen_self_cons j c (T' ++ U),
                ih T' U hrest hT']
              omega

omit [DecidableEq α] in
/-- The head run of a round, from the definition of `assemble`. -/
theorem assemble_runHead (pairs : List (List α × List α)) (j : Nat) :
    ∀ W : List (α × Option Nat),
    assemble pairs W
      = (List.replicate (runLen j W / xlen pairs j) (pairs.getD (j - 1) ([], [])).2).flatten
        ++ assemble pairs (dropN (runLen j W) W) := by
  intro W
  cases W with
  | nil =>
      have hr : runLen j ([] : List (α × Option Nat)) = 0 := rfl
      have hdn : dropN 0 ([] : List (α × Option Nat)) = [] := rfl
      rw [hr, Nat.zero_div, List.replicate_zero, hdn]
      rfl
  | cons t T' =>
      obtain ⟨c, o⟩ := t
      cases o with
      | none =>
          have hr : runLen j ((c, none) :: T') = 0 := rfl
          have hdn : dropN 0 ((c, none) :: T') = (c, none) :: T' := rfl
          rw [hr, Nat.zero_div, List.replicate_zero, hdn]
          rfl
      | some j' =>
          by_cases hjj : j' = j
          · subst hjj
            rw [dropN_eq_drop]
            simp only [assemble]
            rfl
          · have hr : runLen j ((c, some j') :: T') = 0 := by
              show (if j' = j then runLen j T' + 1 else 0) = 0
              split
              · rename_i h
                exact absurd h hjj
              · rfl
            have hdn : dropN 0 ((c, some j') :: T') = (c, some j') :: T' := rfl
            rw [hr, Nat.zero_div, List.replicate_zero, hdn]
            rfl

omit [DecidableEq α] in
/-- Freezing one chunk of a round. -/
theorem assemble_chunk (pairs : List (List α × List α)) (hne : ∀ p ∈ pairs, p.1 ≠ []) :
    ∀ (t : α) (j : Nat) (T : List (α × Option Nat)), 1 ≤ j → j ≤ pairs.length →
    PureChunked pairs ((t, some j) :: T) →
    assemble pairs ((t, some j) :: T)
      = (pairs.getD (j - 1) ([], [])).2 ++ assemble pairs (dropN (xlen pairs j - 1) T) := by
  intro t j T hj1 hj2 hC
  have hmem : pairs.getD (j - 1) ([], []) ∈ pairs :=
    getD_lt_mem pairs (j - 1) ([], []) (by omega)
  have hXne : (pairs.getD (j - 1) ([], [])).1 ≠ [] := hne _ hmem
  have hxj : 1 ≤ xlen pairs j := by
    simp only [xlen]
    cases hE : (pairs.getD (j - 1) ([], [])).1 with
    | nil => exact absurd hE hXne
    | cons v V =>
        simp only [List.length_cons]
        omega
  have hxdef : xlen pairs j = (pairs.getD (j - 1) ([], [])).1.length := rfl
  rw [PureChunked_some] at hC
  obtain ⟨hPP, hCW⟩ := hC
  obtain ⟨F, W, hT, hF, hPF, hAF⟩ := purePrefix_split j (xlen pairs j - 1) T hPP
  have hWdef : dropN (xlen pairs j - 1) T = W := by
    rw [hT, dropN_length W (xlen pairs j - 1) F hF]
  have hr : runLen j ((t, some j) :: T) = xlen pairs j + runLen j W := by
    rw [hT, runLen_self_cons j t (F ++ W), runLen_app j (xlen pairs j - 1) F W hPF hF]
    omega
  have hd : List.drop (runLen j ((t, some j) :: T)) ((t, some j) :: T)
      = dropN (runLen j W) W := by
    rw [hr, ← dropN_eq_drop]
    obtain ⟨k, hk⟩ : ∃ k, xlen pairs j + runLen j W = k + 1 :=
      ⟨xlen pairs j + runLen j W - 1, by omega⟩
    rw [hk]
    show dropN k T = dropN (runLen j W) W
    have hk2 : k = xlen pairs j - 1 + runLen j W := by omega
    rw [hk2, dropN_add, hWdef]
  rw [hWdef]
  simp only [assemble]
  rw [← hxdef, hd, hr, Nat.add_comm (xlen pairs j) (runLen j W),
    Nat.add_div_right (runLen j W) (by omega : 0 < xlen pairs j), List.replicate_succ,
    List.flatten_cons, assemble_runHead pairs j W, List.append_assoc]

/-- All frozen entries are tagged with round indices in range. -/
def TagsOK : Nat → List (α × Option Nat) → Prop
  | _, [] => True
  | n, (_, none) :: T => TagsOK n T
  | n, (_, some j) :: T => 1 ≤ j ∧ j ≤ n ∧ TagsOK n T

omit [DecidableEq α] in
/-- Unfolding `TagsOK` on the empty list. -/
theorem TagsOK_nil (n : Nat) : TagsOK n ([] : List (α × Option Nat)) = True := by
  simp only [TagsOK]

omit [DecidableEq α] in
/-- Unfolding `TagsOK` on an unfrozen entry. -/
theorem TagsOK_none (n : Nat) (c : α) (T : List (α × Option Nat)) :
    TagsOK n ((c, none) :: T) = TagsOK n T := by
  simp only [TagsOK]

omit [DecidableEq α] in
/-- Unfolding `TagsOK` on a frozen entry. -/
theorem TagsOK_some (n : Nat) (c : α) (j : Nat) (T : List (α × Option Nat)) :
    TagsOK n ((c, some j) :: T) = (1 ≤ j ∧ j ≤ n ∧ TagsOK n T) := by
  simp only [TagsOK]

omit [DecidableEq α] in
/-- Unfrozen lists satisfy any tag bound. -/
theorem TagsOK_runE : ∀ (n : Nat) (S : List α), TagsOK n (runE S) := by
  intro n S
  induction S with
  | nil => exact trivial
  | cons c S' ih =>
      show TagsOK n ((c, none) :: runE S')
      exact ih

omit [DecidableEq α] in
/-- Dropping entries preserves tag bounds. -/
theorem TagsOK_dropN : ∀ (n k : Nat) (T : List (α × Option Nat)),
    TagsOK n T → TagsOK n (dropN k T) := by
  intro n k T
  induction k generalizing T with
  | zero => intro h; exact h
  | succ k' ih =>
      intro h
      cases T with
      | nil => exact trivial
      | cons t T' =>
          obtain ⟨c, o⟩ := t
          cases o with
          | none => rw [TagsOK_none] at h; exact ih T' h
          | some j =>
              rw [TagsOK_some] at h
              obtain ⟨h1, h2, h3⟩ := h
              exact ih T' h3

omit [DecidableEq α] in
/-- Tag bounds pass over concatenation. -/
theorem TagsOK_app : ∀ (n : Nat) (A B : List (α × Option Nat)),
    TagsOK n A → TagsOK n B → TagsOK n (A ++ B) := by
  intro n A
  induction A with
  | nil => intro B _ hB; exact hB
  | cons a A' ih =>
      intro B hA hB
      obtain ⟨c, o⟩ := a
      cases o with
      | none => rw [TagsOK_none] at hA; exact ih B hA hB
      | some j =>
          rw [TagsOK_some] at hA
          obtain ⟨h1, h2, h3⟩ := hA
          exact ⟨h1, h2, ih B h3 hB⟩

omit [DecidableEq α] in
/-- A frozen block carries one tag, in range. -/
theorem TagsOK_freezeBlock : ∀ (i n : Nat), 1 ≤ i → i ≤ n →
    ∀ (m : Nat) (T : List (α × Option Nat)), TagsOK n (freezeBlock i m T) := by
  intro i n hi hin m T
  induction m generalizing T with
  | zero => exact trivial
  | succ m' ih =>
      cases T with
      | nil => exact trivial
      | cons t T' =>
          show 1 ≤ i ∧ i ≤ n ∧ TagsOK n (freezeBlock i m' T')
          exact ⟨hi, hin, ih T'⟩

/-- Tag bounds survive the unfrozen matcher. -/
theorem TagsOK_dropU : ∀ (n k : Nat) (X : List α) (L U : List (α × Option Nat)),
    L.length ≤ k → dropU? X L = some U → TagsOK n L → TagsOK n U := by
  intro n k
  induction k with
  | zero =>
      intro X L U hL
      cases L with
      | nil =>
          intro hd hC
          cases X with
          | nil =>
              have hd2 : some ([] : List (α × Option Nat)) = some U := hd
              injection hd2 with hd'
              subst hd'
              exact hC
          | cons c₀ X₀ =>
              have hd2 : none = some U := hd
              exact absurd hd2 (by simp)
      | cons t L' => rw [List.length_cons] at hL; omega
  | succ k' ih =>
      intro X L U hL hd hC
      cases L with
      | nil =>
          cases X with
          | nil =>
              have hd2 : some ([] : List (α × Option Nat)) = some U := hd
              injection hd2 with hd'
              subst hd'
              exact hC
          | cons c₀ X₀ =>
              have hd2 : none = some U := hd
              exact absurd hd2 (by simp)
      | cons t L' =>
          rw [List.length_cons] at hL
          obtain ⟨c, o⟩ := t
          cases o with
          | some j =>
              cases X with
              | nil =>
                  have hd2 : some ((c, some j) :: L') = some U := hd
                  injection hd2 with hd'
                  subst hd'
                  exact hC
              | cons c₀ X₀ =>
                  rw [dropU?_cons_some] at hd
                  exact absurd hd (by simp)
          | none =>
              cases X with
              | nil =>
                  have hd2 : some ((c, none) :: L') = some U := hd
                  injection hd2 with hd'
                  subst hd'
                  exact hC
              | cons c₀ X₀ =>
                  rw [TagsOK_none] at hC
                  rw [dropU?_cons_none] at hd
                  by_cases hcc : c₀ = c
                  · rw [ite_eq_left hcc] at hd
                    exact ih X₀ L' U (by omega) hd hC
                  · rw [ite_eq_right hcc] at hd
                    exact absurd hd (by simp)

/-- The freezing pass keeps tag bounds. -/
theorem TagsOK_freezePass : ∀ (i n : Nat), 1 ≤ i → i ≤ n → ∀ (X : List α) (hX : X ≠ []),
    ∀ (m : Nat) (T : List (α × Option Nat)), T.length ≤ m → TagsOK n T →
    TagsOK n (freezePass X hX i T) := by
  intro i n hi hin X hX m
  induction m with
  | zero =>
      intro T hT hC
      cases T with
      | nil => rw [freezePass_nil]; exact trivial
      | cons t T' => rw [List.length_cons] at hT; omega
  | succ m' ih =>
      intro T hT hC
      cases T with
      | nil => rw [freezePass_nil]; exact trivial
      | cons t T' =>
          rw [List.length_cons] at hT
          obtain ⟨c, o⟩ := t
          cases o with
          | some j =>
              have hdn : dropU? X ((c, some j) :: T') = none := by
                cases X with
                | nil => exact absurd rfl hX
                | cons c₀ X₀ => rfl
              rw [freezePass_cons_none _ _ _ _ _ hdn, TagsOK_some]
              rw [TagsOK_some] at hC
              obtain ⟨h1, h2, h3⟩ := hC
              exact ⟨h1, h2, ih T' (by omega) h3⟩
          | none =>
              cases hd : dropU? X ((c, none) :: T') with
              | none =>
                  rw [freezePass_cons_none _ _ _ _ _ hd]
                  exact ih T' (by omega) hC
              | some U =>
                  rw [freezePass_cons_some _ _ _ _ _ _ hd]
                  have hX1 : 1 ≤ X.length := length_pos_of_ne_nil X hX
                  have hlenU := dropU?_length X ((c, none) :: T') U hd
                  have hL : ((c, none) :: T').length = T'.length + 1 := rfl
                  refine TagsOK_app n (freezeBlock i X.length ((c, none) :: T'))
                    (freezePass X hX i U) ?_ ?_
                  · exact TagsOK_freezeBlock i n hi hin X.length ((c, none) :: T')
                  · exact ih U (by omega)
                      (TagsOK_dropU n ((c, none) :: T').length X
                        ((c, none) :: T') U (Nat.le_refl _) hd hC)

/-- The freezing rounds keep tag bounds. -/
theorem markRounds_TagsOK (pairs : List (List α × List α)) (hne : ∀ p ∈ pairs, p.1 ≠ []) :
    ∀ (ps : List (List α × List α)) (i : Nat), ps = pairs.drop (i - 1) → 1 ≤ i →
    i + ps.length = pairs.length + 1 →
    ∀ (T : List (α × Option Nat)), TagsOK pairs.length T →
    TagsOK pairs.length (markRounds ps i T) := by
  intro ps
  induction ps with
  | nil => intro i hps hi hlen T hC; exact hC
  | cons p ps' ih =>
      intro i hps hi hlen T hC
      obtain ⟨Xi, Yi⟩ := p
      have hmem : (Xi, Yi) ∈ pairs := drop_head_mem pairs (i - 1) (Xi, Yi) ps' hps.symm
      have hXi : Xi ≠ [] := hne _ hmem
      have hps2 : ps' = pairs.drop i := by
        have h3 := drop_succ_of_cons pairs (i - 1) (Xi, Yi) ps' hps.symm
        have h4 : i - 1 + 1 = i := by omega
        rw [h4] at h3
        exact h3.symm
      have hMR : markRounds ((Xi, Yi) :: ps') i T
          = markRounds ps' (i + 1) (freezePass Xi hXi i T) := by
        simp only [markRounds]
        split
        · next h => exact absurd h hXi
        · rfl
      simp only [List.length_cons] at hlen
      rw [hMR]
      exact ih (i + 1) hps2 (by omega) (by omega) (freezePass Xi hXi i T)
        (TagsOK_freezePass i pairs.length (by omega) (by omega) Xi hXi
          T.length T (Nat.le_refl _) hC)

/-- The freezing rounds keep the strong chunk invariant. -/
theorem markRounds_PureChunked (pairs : List (List α × List α)) (hne : ∀ p ∈ pairs, p.1 ≠ []) :
    ∀ (ps : List (List α × List α)) (i : Nat), ps = pairs.drop (i - 1) → 1 ≤ i →
    ∀ (T : List (α × Option Nat)), PureChunked pairs T →
    PureChunked pairs (markRounds ps i T) := by
  intro ps
  induction ps with
  | nil => intro i hps hi T hC; exact hC
  | cons p ps' ih =>
      intro i hps hi T hC
      obtain ⟨Xi, Yi⟩ := p
      have hmem : (Xi, Yi) ∈ pairs := drop_head_mem pairs (i - 1) (Xi, Yi) ps' hps.symm
      have hXi : Xi ≠ [] := hne _ hmem
      have hxl : xlen pairs i = Xi.length := by
        simp only [xlen]
        rw [drop_head_getD pairs (i - 1) (Xi, Yi) ps' ([], []) hps.symm]
      have hps2 : ps' = pairs.drop i := by
        have h3 := drop_succ_of_cons pairs (i - 1) (Xi, Yi) ps' hps.symm
        have h4 : i - 1 + 1 = i := by omega
        rw [h4] at h3
        exact h3.symm
      have hMR : markRounds ((Xi, Yi) :: ps') i T
          = markRounds ps' (i + 1) (freezePass Xi hXi i T) := by
        simp only [markRounds]
        split
        · next h => exact absurd h hXi
        · rfl
      rw [hMR]
      exact ih (i + 1) hps2 (by omega) (freezePass Xi hXi i T)
        (PureChunked_freezePass pairs Xi hXi i hxl T.length T (Nat.le_refl _) hC)

omit [DecidableEq α] in
/-- The instantiation rounds annihilate the empty item list. -/
theorem insLoop_nil (b x : α) : ∀ (ps : List (List α × List α)) (i : Nat),
    insLoop b x i ps [] = [] := by
  intro ps
  induction ps with
  | nil => intro i; rfl
  | cons p ps' ih =>
      intro i
      simp only [insLoop_cons']
      exact ih (i - 1)

/-- The instantiation rounds over frozen pieces compute the frozen text. -/
theorem insLoop_pieces_assemble (b x : α) (pairs : List (List α × List α))
    (hne : ∀ p ∈ pairs, p.1 ≠ []) :
    ∀ (n : Nat) (A : List (α × Option Nat)), A.length ≤ n → PureChunked pairs A →
    TagsOK pairs.length A →
    itext b x (insLoop b x pairs.length pairs.reverse (pieces pairs A))
      = enc2 x (assemble pairs A) := by
  intro n
  induction n with
  | zero =>
      intro A hA
      cases A with
      | nil =>
          intro _ _
          rw [pieces_nil, insLoop_nil b x pairs.reverse pairs.length]
          simp only [assemble]
          rfl
      | cons a A' =>
          rw [List.length_cons] at hA
          omega
  | succ n' ih =>
      intro A hA hPC hTO
      cases A with
      | nil =>
          rw [pieces_nil, insLoop_nil b x pairs.reverse pairs.length]
          simp only [assemble]
          rfl
      | cons a A' =>
          rw [List.length_cons] at hA
          obtain ⟨c, o⟩ := a
          cases o with
          | none =>
              rw [PureChunked_none] at hPC
              have hTO' : TagsOK pairs.length A' := hTO
              have hps : pairs.reverse = (pairs.take pairs.length).reverse := by
                rw [List.take_length]
              rw [pieces_none, insLoop_push b x pairs.reverse pairs.length [c]
                (pieces pairs A'), ih A' (by omega) hPC hTO']
              simp only [assemble]
              rfl
          | some j =>
              have hPC0 := hPC
              rw [PureChunked_some] at hPC
              obtain ⟨hPP, hCW⟩ := hPC
              rw [TagsOK_some] at hTO
              obtain ⟨hj1, hj2, hTO'⟩ := hTO
              have hTO2 : TagsOK pairs.length (dropN (xlen pairs j - 1) A') :=
                TagsOK_dropN pairs.length (xlen pairs j - 1) A' hTO'
              have hlen : (dropN (xlen pairs j - 1) A').length ≤ n' := by
                rw [dropN_eq_drop]
                have h1 : (List.drop (xlen pairs j - 1) A').length
                    = A'.length - (xlen pairs j - 1) := List.length_drop
                omega
              have hps : pairs.reverse = (pairs.take pairs.length).reverse := by
                rw [List.take_length]
              rw [pieces_some, insLoop_mark b x pairs pairs.length pairs.reverse hps
                (by omega) (Nat.le_refl _) j
                (pieces pairs (dropN (xlen pairs j - 1) A')) hj1 hj2,
                ih (dropN (xlen pairs j - 1) A') hlen hCW hTO2,
                assemble_chunk pairs hne c j A' hj1 hj2 hPC0, ← enc2_append]

omit [DecidableEq α] in
/-- A defaulted entry at or beyond the end is the default. -/
theorem getD_ge : ∀ (L : List β) (k : Nat) (d : β), L.length ≤ k → L.getD k d = d := by
  intro L k d
  induction L generalizing k with
  | nil => intro _; rfl
  | cons a L' ih =>
      intro h
      cases k with
      | zero => simp only [List.length_cons] at h; omega
      | succ k' =>
          show L'.getD k' d = d
          exact ih k' (by simp only [List.length_cons] at h; omega)

/-- The renaming rounds leave the empty text empty. -/
theorem renameRR_nil (b x : α) : ∀ (ps : List (List α × List α)) (i : Nat),
    renameRR b x i ps [] = [] := by
  intro ps
  induction ps with
  | nil => intro i; rfl
  | cons p ps' ih =>
      intro i
      obtain ⟨Xi, Yi⟩ := p
      show renameRR b x (i + 1) ps'
        (subst (enc2 x Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc2 x Xi) [])) = []
      rw [subst_nil, subst_nil, ih (i + 1)]

/-- The instantiation rounds leave the empty text empty. -/
theorem instRR_nil (b x : α) : ∀ (ps : List (List α × List α)) (i : Nat),
    instRR b x i ps [] = [] := by
  intro ps
  induction ps with
  | nil => intro i; rfl
  | cons p ps' ih =>
      intro i
      obtain ⟨Xi, Yi⟩ := p
      show instRR b x (i - 1) ps' (subst (enc2 x Yi) (marker x b (i + 1)) []) = []
      rw [subst_nil, ih (i - 1)]

/-- The decode passes leave the empty text empty. -/
theorem dec2Passes_nil (x : α) : ∀ (σ : List α), dec2Passes x σ [] = [] := by
  intro σ
  induction σ with
  | nil => rfl
  | cons c σ' ih =>
      show (if c = x then dec2Passes x σ' []
        else dec2Passes x σ' (subst [c] [x, c] [])) = []
      rw [subst_nil]
      split
      · exact ih
      · exact ih

/-- `dec2Pass` leaves the empty text empty. -/
theorem dec2Pass_nil (x : α) (σ : List α) : dec2Pass x σ [] = [] := by
  show subst [x] [x, x] (dec2Passes x σ []) = []
  rw [dec2Passes_nil, subst_nil]

/-- The freezing rounds leave the empty text empty. -/
theorem markRounds_nil : ∀ (ps : List (List α × List α)) (i : Nat),
    markRounds ps i [] = [] := by
  intro ps
  induction ps with
  | nil => intro i; rfl
  | cons p ps' ih =>
      intro i
      obtain ⟨Xi, Yi⟩ := p
      show markRounds ps' (i + 1) (if h : Xi = [] then [] else freezePass Xi h i []) = []
      split
      · exact ih (i + 1)
      · rw [freezePass_nil, ih (i + 1)]

omit [DecidableEq α] in
/-- Dropping entries loses no memberships. -/
theorem mem_dropN : ∀ (k : Nat) (T : List (α × Option Nat)) (e : α × Option Nat),
    e ∈ dropN k T → e ∈ T := by
  intro k
  induction k with
  | zero => intro T e h; exact h
  | succ k' ih =>
      intro T e h
      cases T with
      | nil => exact absurd h (by simp [dropN])
      | cons t T' => exact List.mem_cons_of_mem _ (ih T' e h)

omit [DecidableEq α] in
/-- A frozen block has no unfrozen entries. -/
theorem freezeBlock_notNone : ∀ (i m : Nat) (T : List (α × Option Nat)),
    ∀ e ∈ freezeBlock i m T, e.2 ≠ none := by
  intro i m
  induction m with
  | zero =>
      intro T e he
      rw [show freezeBlock i 0 T = ([] : List (α × Option Nat)) from rfl] at he
      exact absurd he (by simp)
  | succ m' ih =>
      intro T e he
      cases T with
      | nil =>
          rw [show freezeBlock i (m' + 1) ([] : List (α × Option Nat))
              = ([] : List (α × Option Nat)) from rfl] at he
          exact absurd he (by simp)
      | cons t T' =>
          obtain ⟨d, o⟩ := t
          cases List.mem_cons.mp he with
          | inl h =>
              rw [h]
              exact Option.some_ne_none i
          | inr h => exact ih T' e h

/-- The unfrozen matcher keeps memberships. -/
theorem mem_dropU : ∀ (k : Nat) (X : List α) (L U : List (α × Option Nat)),
    L.length ≤ k → dropU? X L = some U → ∀ e ∈ U, e ∈ L := by
  intro k
  induction k with
  | zero =>
      intro X L U hL
      cases L with
      | nil =>
          intro hd e he
          cases X with
          | nil =>
              have hd2 : some ([] : List (α × Option Nat)) = some U := hd
              injection hd2 with hd'
              subst hd'
              exact he
          | cons c₀ X₀ =>
              have hd2 : none = some U := hd
              exact absurd hd2 (by simp)
      | cons t L' => rw [List.length_cons] at hL; omega
  | succ k' ih =>
      intro X L U hL hd e he
      cases L with
      | nil =>
          cases X with
          | nil =>
              have hd2 : some ([] : List (α × Option Nat)) = some U := hd
              injection hd2 with hd'
              subst hd'
              exact he
          | cons c₀ X₀ =>
              have hd2 : none = some U := hd
              exact absurd hd2 (by simp)
      | cons t L' =>
          rw [List.length_cons] at hL
          obtain ⟨c, o⟩ := t
          cases o with
          | some j =>
              cases X with
              | nil =>
                  have hd2 : some ((c, some j) :: L') = some U := hd
                  injection hd2 with hd'
                  subst hd'
                  exact he
              | cons c₀ X₀ =>
                  rw [dropU?_cons_some] at hd
                  exact absurd hd (by simp)
          | none =>
              cases X with
              | nil =>
                  have hd2 : some ((c, none) :: L') = some U := hd
                  injection hd2 with hd'
                  subst hd'
                  exact he
              | cons c₀ X₀ =>
                  rw [dropU?_cons_none] at hd
                  by_cases hcc : c₀ = c
                  · rw [ite_eq_left hcc] at hd
                    exact List.mem_cons_of_mem _ (ih X₀ L' U (by omega) hd e he)
                  · rw [ite_eq_right hcc] at hd
                    exact absurd hd (by simp)

/-- Unfrozen characters are never introduced by a freezing pass. -/
theorem freezePass_mem (σ : List α) : ∀ (X : List α) (hX : X ≠ []) (i : Nat),
    ∀ (n : Nat) (T : List (α × Option Nat)), T.length ≤ n →
    (∀ e ∈ T, e.2 = none → e.1 ∈ σ) →
    (∀ e ∈ freezePass X hX i T, e.2 = none → e.1 ∈ σ) := by
  intro X hX i n
  induction n with
  | zero =>
      intro T hT
      cases T with
      | nil =>
          intro _ e he
          rw [freezePass_nil] at he
          exact absurd he (by simp)
      | cons t T' => rw [List.length_cons] at hT; omega
  | succ n' ih =>
      intro T hT hcond
      cases T with
      | nil =>
          intro e he
          rw [freezePass_nil] at he
          exact absurd he (by simp)
      | cons t T' =>
          rw [List.length_cons] at hT
          obtain ⟨c, o⟩ := t
          cases o with
          | some j =>
              have hdn : dropU? X ((c, some j) :: T') = none := by
                cases X with
                | nil => exact absurd rfl hX
                | cons c₀ X₀ => rfl
              rw [freezePass_cons_none _ _ _ _ _ hdn]
              intro e he he2
              cases List.mem_cons.mp he with
              | inl h =>
                  rw [h] at he2
                  exact absurd he2 (Option.some_ne_none j)
              | inr h =>
                  refine ih T' (by omega) ?_ e h he2
                  intro e2 he2' he22
                  exact hcond e2 (List.mem_cons_of_mem _ he2') he22
          | none =>
              cases hd : dropU? X ((c, none) :: T') with
              | none =>
                  rw [freezePass_cons_none _ _ _ _ _ hd]
                  intro e he he2
                  cases List.mem_cons.mp he with
                  | inl h =>
                      subst h
                      exact hcond (c, none) List.mem_cons_self rfl
                  | inr h =>
                      refine ih T' (by omega) ?_ e h he2
                      intro e2 he2' he22
                      exact hcond e2 (List.mem_cons_of_mem _ he2') he22
              | some U =>
                  rw [freezePass_cons_some _ _ _ _ _ _ hd]
                  have hX1 : 1 ≤ X.length := length_pos_of_ne_nil X hX
                  have hlenU := dropU?_length X ((c, none) :: T') U hd
                  have hL : ((c, none) :: T').length = T'.length + 1 := rfl
                  intro e he he2
                  cases List.mem_append.mp he with
                  | inl h =>
                      exact absurd he2 (freezeBlock_notNone i X.length ((c, none) :: T') e h)
                  | inr h =>
                      refine ih U (by omega) ?_ e h he2
                      intro e2 he2' he22
                      exact hcond e2 (mem_dropU ((c, none) :: T').length X
                        ((c, none) :: T') U (Nat.le_refl _) hd e2 he2') he22

/-- Unfrozen characters are never introduced by the freezing rounds. -/
theorem markRounds_mem (σ : List α) : ∀ (ps : List (List α × List α)) (i : Nat)
    (T : List (α × Option Nat)), (∀ e ∈ T, e.2 = none → e.1 ∈ σ) →
    (∀ e ∈ markRounds ps i T, e.2 = none → e.1 ∈ σ) := by
  intro ps
  induction ps with
  | nil => intro i T h; exact h
  | cons p ps' ih =>
      intro i T h
      obtain ⟨Xi, Yi⟩ := p
      by_cases hXi : Xi = []
      · have hMR : markRounds ((Xi, Yi) :: ps') i T = markRounds ps' (i + 1) T := by
          simp only [markRounds]
          split
          · rfl
          · next h => exact absurd hXi h
        rw [hMR]
        exact ih (i + 1) T h
      · have hMR : markRounds ((Xi, Yi) :: ps') i T
            = markRounds ps' (i + 1) (freezePass Xi hXi i T) := by
          simp only [markRounds]
          split
          · next h => exact absurd h hXi
          · rfl
        rw [hMR]
        exact ih (i + 1) (freezePass Xi hXi i T)
          (freezePass_mem σ Xi hXi i T.length T (Nat.le_refl _) h)

/-- Membership of the assembled text. -/
theorem assemble_mem (pairs : List (List α × List α)) (σ : List α)
    (hσ : ∀ (j : Nat) (c : α), c ∈ (pairs.getD (j - 1) ([], [])).2 → c ∈ σ) :
    ∀ (n : Nat) (A : List (α × Option Nat)), A.length ≤ n →
    (∀ e ∈ A, e.2 = none → e.1 ∈ σ) →
    ∀ c ∈ assemble pairs A, c ∈ σ := by
  intro n
  induction n with
  | zero =>
      intro A hA
      cases A with
      | nil =>
          intro _ c hc
          exact absurd hc (by simp [assemble])
      | cons e A' => rw [List.length_cons] at hA; omega
  | succ n' ih =>
      intro A hA hcond
      cases A with
      | nil =>
          intro c hc
          exact absurd hc (by simp [assemble])
      | cons e A' =>
          rw [List.length_cons] at hA
          obtain ⟨c₀, o⟩ := e
          cases o with
          | none =>
              intro c hc
              have hunf : assemble pairs ((c₀, none) :: A') = c₀ :: assemble pairs A' := by
                simp only [assemble]
              rw [hunf] at hc
              cases List.mem_cons.mp hc with
              | inl hc' =>
                  rw [hc']
                  exact hcond (c₀, none) List.mem_cons_self rfl
              | inr hc' =>
                  refine ih A' (by omega) ?_ c hc'
                  intro e2 he2' he22
                  exact hcond e2 (List.mem_cons_of_mem _ he2') he22
          | some j =>
              intro c hc
              have hunf := assemble_runHead pairs j ((c₀, some j) :: A')
              rw [hunf] at hc
              cases List.mem_append.mp hc with
              | inl hc' =>
                  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc'
                  obtain ⟨_, hl'⟩ := List.mem_replicate.mp hl
                  rw [hl'] at hcl
                  exact hσ j c hcl
              | inr hc' =>
                  have hcond2 : ∀ e ∈ dropN (runLen j ((c₀, some j) :: A'))
                      ((c₀, some j) :: A'), e.2 = none → e.1 ∈ σ := by
                    intro e he he2
                    exact hcond e (mem_dropN _ _ _ he) he2
                  refine ih (dropN (runLen j ((c₀, some j) :: A'))
                    ((c₀, some j) :: A')) ?_ hcond2 c hc'
                  rw [runLen_self_cons j c₀ A']
                  show (dropN (runLen j A') A').length ≤ n'
                  have h1 := dropN_length_le (runLen j A') A'
                  omega

omit [DecidableEq α] in
/-- Frozen pieces are instantiable. -/
theorem pieces_InstOK (pairs : List (List α × List α)) :
    ∀ (n : Nat) (A : List (α × Option Nat)), A.length ≤ n → TagsOK pairs.length A →
    InstOK pairs.length (pieces pairs A) := by
  intro n
  induction n with
  | zero =>
      intro A hA
      cases A with
      | nil =>
          intro _
          rw [pieces_nil]
          exact trivial
      | cons e A' => rw [List.length_cons] at hA; omega
  | succ n' ih =>
      intro A hA hTO
      cases A with
      | nil =>
          rw [pieces_nil]
          exact trivial
      | cons e A' =>
          rw [List.length_cons] at hA
          obtain ⟨c, o⟩ := e
          cases o with
          | none =>
              rw [TagsOK_none] at hTO
              rw [pieces_none]
              exact pushFrag_instOK [c] pairs.length (pieces pairs A')
                (ih A' (by omega) hTO)
          | some j =>
              rw [TagsOK_some] at hTO
              obtain ⟨hj1, hj2, hTO'⟩ := hTO
              rw [pieces_some]
              show 1 ≤ j ∧ j ≤ pairs.length
                ∧ InstOK pairs.length (pieces pairs (dropN (xlen pairs j - 1) A'))
              have hfu : (dropN (xlen pairs j - 1) A').length ≤ n' := by
                have h1 := dropN_length_le (xlen pairs j - 1) A'
                omega
              exact ⟨hj1, hj2,
                ih (dropN (xlen pairs j - 1) A') hfu (TagsOK_dropN pairs.length
                  (xlen pairs j - 1) A' hTO')⟩

/-- Unfolding `instRR` on a round. -/
theorem instRR_cons (b x : α) (i : Nat) (Xi Yi : List α) (ps : List (List α × List α))
    (T : List α) :
    instRR b x i ((Xi, Yi) :: ps) T
      = instRR b x (i - 1) ps (subst (enc2 x Yi) (marker x b (i + 1)) T) := rfl

/-- The item-level instantiation rounds compute the `instRR` text. -/
theorem insLoop_scan (x b : α) (hxb : x ≠ b) :
    ∀ (ps : List (List α × List α)) (i : Nat), ps.length ≤ i →
    ∀ (ns : List (NFItem α)), InstOK i ns →
    itext b x (insLoop b x i ps ns) = instRR b x i ps (itext b x ns) := by
  intro ps
  induction ps with
  | nil => intro _ _ _ _; rfl
  | cons p ps ih =>
      intro i hlen ns hC
      obtain ⟨Xi, Yi⟩ := p
      have hlen' : ps.length + 1 ≤ i := by
        have h1 : ((Xi, Yi) :: ps).length = ps.length + 1 := by simp
        omega
      have hR := instNF_scan x b hxb i (by omega) Yi ns.length ns (Nat.le_refl _) hC
      rw [insLoop_cons, instRR_cons, hR]
      exact ih (i - 1) (by omega) (instNF b x i Yi ns)
        (instNF_canon b x i Yi ns.length ns (Nat.le_refl _) hC)

theorem renameRepair2_eq (b x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    ∀ (ps : List (List α × List α)) (i : Nat), (∀ p ∈ ps, p ∈ pairs) → ∀ T : List α,
    renameRepair2 b x σ i ps T = renameRR b x i ps T := by
  intro ps
  induction ps with
  | nil => intro _ _ T; rfl
  | cons p ps ih =>
      intro i hmem T
      have hXi : ∀ c ∈ p.1, c ∈ σ := fun c hc =>
        hp p (hmem p (List.mem_cons_self ..)) c (List.mem_append_left _ hc)
      have hps : ∀ q ∈ ps, q ∈ pairs := fun q hq => hmem q (List.mem_cons_of_mem _ hq)
      show renameRepair2 b x σ (i + 1) ps
          (subst (enc2Pass x σ p.1 ++ [b]) (marker x b (i + 2))
            (subst (marker x b (i + 1)) (enc2Pass x σ p.1) T))
        = renameRR b x (i + 1) ps
          (subst (enc2 x p.1 ++ [b]) (marker x b (i + 2))
            (subst (marker x b (i + 1)) (enc2 x p.1) T))
      rw [enc2Pass_eq x σ hnd p.1 hXi, ih (i + 1) hps _]

theorem instantiate2_eq (b x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    ∀ (ps : List (List α × List α)) (i : Nat), (∀ p ∈ ps, p ∈ pairs) → ∀ T : List α,
    instantiate2 b x σ i ps T = instRR b x i ps T := by
  intro ps
  induction ps with
  | nil => intro _ _ T; rfl
  | cons p ps ih =>
      intro i hmem T
      have hYi : ∀ c ∈ p.2, c ∈ σ := fun c hc =>
        hp p (hmem p (List.mem_cons_self ..)) c (List.mem_append_right _ hc)
      have hps : ∀ q ∈ ps, q ∈ pairs := fun q hq => hmem q (List.mem_cons_of_mem _ hq)
      show instantiate2 b x σ (i - 1) ps (subst (enc2Pass x σ p.2) (marker x b (i + 1)) T)
        = instRR b x (i - 1) ps (subst (enc2 x p.2) (marker x b (i + 1)) T)
      rw [enc2Pass_eq x σ hnd p.2 hYi, ih (i - 1) hps _]

theorem mem_reverse_of {β : Type} {l : List β} {q : β} (h : q ∈ l) : q ∈ l.reverse :=
  List.mem_reverse.mpr h

/-- The construction, with the code layer bridged: everything after this
point works with `enc2` and `subst` only. -/
theorem repC2_eq (b x : α) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (S : List α) (hS : ∀ c ∈ S, c ∈ σ)
    (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    repC2 b x σ pairs S =
      dec2Pass x σ (instRR b x pairs.length pairs.reverse
        (renameRR b x 1 pairs (enc2 x S))) := by
  have hall : ∀ p ∈ pairs.reverse, p ∈ pairs := fun p hp2 =>
    List.mem_reverse.mp hp2
  unfold repC2
  rw [renameRepair2_eq b x σ hnd pairs hp pairs 1 (fun _ h => h),
    instantiate2_eq b x σ hnd pairs hp pairs.reverse pairs.length hall,
    enc2Pass_eq x σ hnd S hS]

omit [DecidableEq α] in
/-- An unfrozen run is strongly chunked. -/
theorem PureChunked_runE (pairs : List (List α × List α)) :
    ∀ (V : List α), PureChunked pairs (runE V) := by
  intro V
  induction V with
  | nil => exact PureChunked_nil pairs
  | cons v V' ih =>
      show PureChunked pairs ((v, none) :: runE V')
      rw [PureChunked_none]
      exact ih

/-- Theorem (Multiple Substitution): the comma-code construction
computes the freezing semantics for ARBITRARY nonempty patterns -- no
restriction on the patterns.  The patterns, replacements, and `S` must be
over `σ` (the paper works over a fixed finite alphabet throughout).

The proof is the phase-locking argument: in a normal text (a concatenation
of `enc2`-fragments and markers) every misaligned occurrence of `enc2(X_i)`
is shadowed by an aligned occurrence starting one position earlier (the
all-`x` patterns), and every aligned-but-spurious occurrence runs into a
marker and is exactly repaired by the following pass (the patterns ending
in `b`).  Roadmap: (1) the code layer -- `enc2Pass_eq`, `dec2Pass_enc2` --
is PROVEN above; (2) the normal-form invariant through rename and repair
(fragments + markers, `b`-runs ≤ 1); (3) the occurrence classification
(α)/(β)/(γ) with (β) shadowed; (4) repair exactness; (5) instantiation by
whole markers. -/
theorem repC2_correct (b x : α) (hxb : x ≠ b) (σ : List α) (hnd : σ.Pairwise (· ≠ ·))
    (pairs : List (List α × List α)) (hne : ∀ p ∈ pairs, p.1 ≠ [])
    (S : List α) (hS : ∀ c ∈ S, c ∈ σ)
    (hp : ∀ p ∈ pairs, ∀ c ∈ p.1 ++ p.2, c ∈ σ) :
    repC2 b x σ pairs S = repRef pairs S := by
  by_cases hSnil : S = []
  · subst hSnil
    have hE : enc2 x ([] : List α) = [] := rfl
    rw [repC2_eq b x σ hnd pairs [] hS hp, hE, renameRR_nil b x pairs 1,
      instRR_nil b x pairs.reverse pairs.length, dec2Pass_nil x σ]
    show ([] : List α) = assemble pairs (markRounds pairs 1 ([] : List (α × Option Nat)))
    rw [markRounds_nil pairs 1]
    simp only [assemble]
  · have hps0 : pairs = List.drop (1 - 1) pairs := by
      show pairs = List.drop 0 pairs
      rw [List.drop_zero]
    have hpc : pieces pairs (runE S) = NFItem.frag S :: [] := by
      cases S with
      | nil => exact absurd rfl hSnil
      | cons v S' =>
          rw [show runE (v :: S') = runE (v :: S') ++ ([] : List (α × Option Nat))
              from (List.append_nil _).symm, pieces_run, pieces_nil, pushFrag_cons_nil]
    have hPC : PureChunked pairs (runE S) := PureChunked_runE pairs S
    have hTO : TagsOK pairs.length (runE S) := TagsOK_runE pairs.length S
    have hMR1 : renLoop b x 1 pairs (NFItem.frag S :: [])
        = pieces pairs (markRounds pairs 1 (runE S)) := by
      rw [← hpc]
      exact renLoop_markRounds b x pairs hne pairs 1 hps0 (by omega)
        (runE S).length (runE S) (Nat.le_refl _) hPC
    have hTOMR : TagsOK pairs.length (markRounds pairs 1 (runE S)) :=
      markRounds_TagsOK pairs hne pairs 1 hps0 (by omega) (by omega) (runE S) hTO
    have hPCMR : PureChunked pairs (markRounds pairs 1 (runE S)) :=
      markRounds_PureChunked pairs hne pairs 1 hps0 (by omega) (runE S) hPC
    have hIOK : InstOK pairs.length (renLoop b x 1 pairs (NFItem.frag S :: [])) := by
      rw [hMR1]
      exact pieces_InstOK pairs (markRounds pairs 1 (runE S)).length
        (markRounds pairs 1 (runE S)) (Nat.le_refl _) hTOMR
    have hCanon : CanonB (1 - 1) (NFItem.frag S :: []) := hSnil
    have hRS := renLoop_scan x b hxb pairs hne 1 (by omega) (NFItem.frag S :: []) hCanon
    have hite : itext b x (NFItem.frag S :: []) = enc2 x S := by simp [itext]
    have hR : renameRR b x 1 pairs (enc2 x S)
        = itext b x (renLoop b x 1 pairs (NFItem.frag S :: [])) := by
      rw [← hite, ← hRS]
    have hIS := insLoop_scan x b hxb pairs.reverse pairs.length
      (by rw [List.length_reverse]; exact Nat.le_refl pairs.length)
      (renLoop b x 1 pairs (NFItem.frag S :: [])) hIOK
    have hσ : ∀ (j : Nat) (c : α), c ∈ (pairs.getD (j - 1) ([], [])).2 → c ∈ σ := by
      intro j c hc
      by_cases hj : j - 1 < pairs.length
      · exact hp (pairs.getD (j - 1) ([], []))
          (getD_lt_mem pairs (j - 1) ([], []) hj) c
          (List.mem_append_right (pairs.getD (j - 1) ([], [])).1 hc)
      · rw [getD_ge pairs (j - 1) ([], []) (by omega)] at hc
        simp at hc
    have hcond0 : ∀ e ∈ runE S, e.2 = none → e.1 ∈ σ := by
      intro e he _
      have he' : e ∈ S.map (fun w => (w, none)) := he
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp he'
      have he3 : (w, none) = e := heq
      rw [← he3]
      exact hS w hw
    have hmem : ∀ c ∈ assemble pairs (markRounds pairs 1 (runE S)), c ∈ σ :=
      assemble_mem pairs σ hσ (markRounds pairs 1 (runE S)).length
        (markRounds pairs 1 (runE S)) (Nat.le_refl _)
        (markRounds_mem σ pairs 1 (runE S) hcond0)
    rw [repC2_eq b x σ hnd pairs S hS hp, hR, ← hIS, hMR1,
      insLoop_pieces_assemble b x pairs hne (markRounds pairs 1 (runE S)).length
        (markRounds pairs 1 (runE S)) (Nat.le_refl _) hPCMR hTOMR,
      dec2Pass_enc2 x σ hnd (assemble pairs (markRounds pairs 1 (runE S))) hmem]
    rfl

#eval repC2 'a' 'c' ['a', 'b', 'c'] [(['a'], ['b', 'a'])] ['a', 'b', 'a']  -- [b, a, b, b, a]
#eval repC2 'a' 'c' ['a', 'b', 'c'] [(['a', 'b'], ['c']), (['b', 'a'], ['a', 'a'])] ['a', 'b', 'a']  -- [c, a]

-- The shadowing instance of the remark: `X₁ = "ab"` and `X₂ = "bbb"` both
-- end with `x = 'b'`, which the enc-based variant `repC` cannot handle --
-- yet the comma code computes the freezing semantics.
#eval repC2 'a' 'b' ['a', 'b'] [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
#eval repRef [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
-- [b, b, b, a, a, b, b, b, a] both times (`repC` returns [b, b, b, a, a, a, b])

-- Regression sweep: repC2 against the freezing semantics, including
-- patterns that end in `x` (b = 'a', x = 'c'; `ac` and `cc` end with
-- `x = 'c'`); all strings, patterns, and replacements over σ = {a, b, c}.
-- (The full domain -- all strings ≤ 8 over σ -- was verified against the
-- independent Python model: 984,100 evaluations, 0 failures.)
#eval Id.run do
  let mut allOk := true
  let strs : List (List Char) :=
    ["", "a", "b", "c", "ab", "ba", "ca", "bc", "abc", "aab", "bcc", "abaab"].map String.toList
  let pats : List (List Char) :=
    ["a", "b", "c", "ab", "ba", "aa", "bb", "cab", "ac", "cc"].map String.toList
  for S in strs do
    for X1 in pats do
      for X2 in pats do
        let pairs := [(X1, ['a', 'b']), (X2, ['b'])]
        if repC2 'a' 'c' ['a', 'b', 'c'] pairs S != repRef pairs S then
          allOk := false
  return allOk
-- true
