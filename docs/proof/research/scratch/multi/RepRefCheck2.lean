-- Standalone copy of the Lean reference semantics (repRef) from
-- docs/proof/lean/Subst.lean, to check two #eval comments that look stale.
-- Run: lean RepRefCheck.lean

variable {α : Type} [DecidableEq α]

/-- If the unfrozen text `T` begins with the block `X`, return the rest. -/
def dropU? : List α → List (α × Option Nat) → Option (List (α × Option Nat))
  | [], T => some T
  | _, [] => none
  | c :: X', (d, none) :: T' => if c = d then dropU? X' T' else none
  | _ :: _, _ :: _ => none

/-- The first `k` entries, frozen (they form the matched block). -/
def freezeBlock (i : Nat) : Nat → List (α × Option Nat) → List (α × Option Nat)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, (d, _) :: T' => (d, some i) :: freezeBlock i k T'

partial def freezePass (X : List α) (hX : X ≠ []) (i : Nat) :
    List (α × Option Nat) → List (α × Option Nat)
  | [] => []
  | t :: T' =>
      match _h : dropU? X (t :: T') with
      | some U => freezeBlock i X.length (t :: T') ++ freezePass X hX i U
      | none => t :: freezePass X hX i T'


def markRounds : List (List α × List α) → Nat → List (α × Option Nat) → List (α × Option Nat)
  | [], _, T => T
  | (X, _) :: ps, i, T => markRounds ps (i + 1) (if h : X = [] then T else freezePass X h i T)

def runLen : Nat → List (α × Option Nat) → Nat
  | _, [] => 0
  | i, (_, some j) :: T => if j = i then runLen i T + 1 else 0
  | _, (_, none) :: _ => 0

partial def assemble : List (List α × List α) → List (α × Option Nat) → List α
  | [], _ => []
  | _, [] => []
  | pairs, (t, none) :: T' => t :: assemble pairs T'
  | pairs, (t, some i) :: T' =>
      (List.replicate
        (runLen i ((t, some i) :: T') / (pairs.getD (i - 1) ([], [])).1.length)
        (pairs.getD (i - 1) ([], [])).2).flatten
        ++ assemble pairs (List.drop (runLen i ((t, some i) :: T')) ((t, some i) :: T'))


def repRef (pairs : List (List α × List α)) (S : List α) : List α :=
  assemble pairs (markRounds pairs 1 (S.map (fun c => (c, none))))

#eval repRef [(['a', 'b'], ['c']), (['b', 'a'], ['a', 'a'])] ['a', 'b', 'a']
-- Subst.lean comment says [c, a, a]; the paper's freezing definition gives [c, a]

#eval repRef [(['a'], ['b', 'a'])] ['a', 'b', 'a']
-- Subst.lean comment says [b, a, b, b, a]

partial def subst (A B : List α) : List α → List α
  | [] => []
  | c :: C =>
      match B with
      | [] => c :: C
      | B' =>
        let rec matchHere : List α → List α → Option (List α)
          | [], T => some T
          | _, [] => none
          | b :: B'', cc :: C' => if b = cc then matchHere B'' C' else none
        match matchHere B (c :: C) with
        | some D => A ++ subst A B D
        | none => c :: subst A B C

def enc (b x : α) (S : List α) : List α := subst [x, b] [b] S
def dec (b x : α) (S : List α) : List α := subst [b] [x, b] S
def marker (x b : α) (k : Nat) : List α := x :: List.replicate k b

partial def renameRepair (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (Xi, _) :: ps, T =>
      renameRepair b x (i + 1) ps
        (subst (enc b x Xi ++ [b]) (marker x b (i + 2))
          (subst (marker x b (i + 1)) (enc b x Xi) T))

partial def instantiate (b x : α) : Nat → List (List α × List α) → List α → List α
  | _, [], T => T
  | i, (_, Yi) :: ps, T =>
      instantiate b x (i - 1) ps (subst (enc b x Yi) (marker x b (i + 1)) T)

def repC (b x : α) (pairs : List (List α × List α)) (S : List α) : List α :=
  dec b x (instantiate b x pairs.length pairs.reverse
    (renameRepair b x 1 pairs (enc b x S)))

-- the paper's shadowing instance: b = 'a', x = 'b' (sigma1 = 'a', sigma2 = 'b')
#eval repC 'a' 'b' [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
#eval repRef [("ab".toList, "bbba".toList), ("bbb".toList, "aa".toList)] "abaab".toList
#eval subst ['a', 'a'] ['a'] ['a', 'a']   -- check the stale comment [a]
