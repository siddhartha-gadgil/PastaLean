import Libraries.re.Parser

namespace Libraries.re

open PastaLean

/-! ### Matching -/

structure MCtx where
  s : Array Char
  flags : Int

def foldCase (flags : Int) (c : Char) : Char :=
  if hasFlag flags IGNORECASE then c.toLower else c

def itemMatches (flags : Int) (c : Char) : ClassItem → Bool
  | .single x => foldCase flags x == foldCase flags c
  | .range lo hi =>
      (lo ≤ c && c ≤ hi) ||
        (hasFlag flags IGNORECASE && ((lo ≤ c.toLower && c.toLower ≤ hi) || (lo ≤ c.toUpper && c.toUpper ≤ hi)))
  | .digit neg => c.isDigit != neg
  | .space neg => isSpaceChar c != neg
  | .word neg => isWordChar c != neg

abbrev Caps := Array (Option (Nat × Nat))

/-- Match `nodes` at `i`, then call `k` with the end position and captures (first success wins). -/
partial def matchSeq (ctx : MCtx) (nodes : List Node) (i : Nat) (caps : Caps)
    (k : Nat → Caps → Option (Nat × Caps)) : Option (Nat × Caps) :=
  match nodes with
  | [] => k i caps
  | n :: rest => matchNode ctx n i caps fun j caps' => matchSeq ctx rest j caps' k
where
  matchNode (ctx : MCtx) (n : Node) (i : Nat) (caps : Caps)
      (k : Nat → Caps → Option (Nat × Caps)) : Option (Nat × Caps) :=
    let s := ctx.s
    match n with
    | .char c => if h : i < s.size then (if foldCase ctx.flags s[i] == foldCase ctx.flags c then k (i + 1) caps else none) else none
    | .any => if h : i < s.size then (if s[i] != '\n' || hasFlag ctx.flags DOTALL then k (i + 1) caps else none) else none
    | .cls items neg =>
        if h : i < s.size then
          (if items.any (itemMatches ctx.flags s[i]) != neg then k (i + 1) caps else none) else none
    | .lineStart =>
        if i == 0 || (hasFlag ctx.flags MULTILINE && s[i - 1]? == some '\n') then k i caps else none
    | .lineEnd =>
        if i == s.size || (i + 1 == s.size && s[i]? == some '\n')
            || (hasFlag ctx.flags MULTILINE && s[i]? == some '\n') then k i caps else none
    | .strStart => if i == 0 then k i caps else none
    | .strEnd => if i == s.size then k i caps else none
    | .wordBoundary neg =>
        let before := i > 0 && (s[i - 1]?.map isWordChar).getD false
        let after := (s[i]?.map isWordChar).getD false
        if (before != after) != neg then k i caps else none
    | .backref idx =>
        match caps[idx]? with
        | some (some (a, b)) =>
            let len := b - a
            if i + len ≤ s.size && (List.range len).all (fun t =>
                foldCase ctx.flags s[a + t]! == foldCase ctx.flags s[i + t]!) then k (i + len) caps else none
        | _ => none
    | .group idx alts =>
        alts.findSome? fun alt =>
          matchSeq ctx alt i caps fun j caps' =>
            let caps'' := match idx with
              | some g => if g < caps'.size then caps'.set! g (some (i, j)) else caps'
              | none => caps'
            k j caps''
    | .rep inner lo hi greedy => rep ctx inner lo hi greedy 0 i caps k
    | .look false neg alts =>
        let r := matchNode ctx (.group none alts) i caps fun j c => some (j, c)
        match r, neg with
        | some (_, caps'), false => k i caps'
        | none, true => k i caps
        | _, _ => none
    | .look true neg alts =>
        -- some start `j ≤ i` from which the body matches exactly up to `i`
        let r := (List.range (i + 1)).findSome? fun d =>
          matchNode ctx (.group none alts) (i - d) caps fun j c => if j == i then some (j, c) else none
        match r, neg with
        | some (_, caps'), false => k i caps'
        | none, true => k i caps
        | _, _ => none
  rep (ctx : MCtx) (inner : Node) (lo : Nat) (hi : Option Nat) (greedy : Bool) (count i : Nat)
      (caps : Caps) (k : Nat → Caps → Option (Nat × Caps)) : Option (Nat × Caps) :=
    let canMore : Bool := match hi with | some h => decide (count < h) | none => true
    let more : Unit → Option (Nat × Caps) := fun _ =>
      if canMore then
        matchNode ctx inner i caps fun j caps' =>
          -- an empty iteration ends the repetition (keeping its captures, as Python's engine does)
          if j == i then k j caps' else rep ctx inner lo hi greedy (count + 1) j caps' k
      else none
    if count < lo then more ()
    else if greedy then (more ()).orElse fun _ => k i caps
    else (k i caps).orElse fun _ => more ()

def runAt (p : Pattern) (s : Array Char) (start : Nat) (full : Bool) : Option (Nat × Caps) :=
  let caps : Caps := Array.replicate (p.groupCount + 1) none
  matchSeq { s, flags := p.flags } [.group none p.prog] start caps fun j caps =>
    if full && j != s.size then none else some (j, caps)

def toMatch (p : Pattern) (str : String) (start : Nat) : Nat × Caps → Match
  | (j, caps) => { string := str, spans := caps.set! 0 (some (start, j)), groupNames := p.groupNames }

end Libraries.re
