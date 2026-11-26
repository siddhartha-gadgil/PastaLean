import Libraries.re.Syntax

namespace Libraries.re

open PastaLean

/-! ### Parsing -/

structure PState where
  src : Array Char
  pos : Nat
  verbose : Bool
  groups : Nat
  names : List (String × Nat)
  /-- Flags set inline (`(?i)`), added to the pattern's flags. -/
  inline : Int := 0

abbrev PM := StateM PState

def peek? : PM (Option Char) := do
  let s ← get
  return s.src[s.pos]?

def advance : PM Unit := modify fun s => { s with pos := s.pos + 1 }

/-- In `VERBOSE` mode, skip whitespace and `#` comments between pattern items. -/
partial def skipVerbose : PM Unit := do
  let s ← get
  if !s.verbose then return
  match s.src[s.pos]? with
  | some c =>
      if isSpaceChar c then advance; skipVerbose
      else if c == '#' then
        let rec toEol : PM Unit := do
          match ← peek? with
          | some '\n' => advance
          | some _ => advance; toEol
          | none => pure ()
        toEol; skipVerbose
  | none => pure ()

partial def parseInt? : PM (Option Nat) := do
  let mut n : Option Nat := none
  repeat
    match ← peek? with
    | some c =>
        if c.isDigit then
          n := some ((n.getD 0) * 10 + (c.toNat - '0'.toNat)); advance
        else break
    | none => break
  return n

/-- The item an escape stands for inside or outside a class (`none`: a node-level escape). -/
def escapeItem? (c : Char) : Option ClassItem :=
  match c with
  | 'd' => some (.digit false) | 'D' => some (.digit true)
  | 's' => some (.space false) | 'S' => some (.space true)
  | 'w' => some (.word false) | 'W' => some (.word true)
  | 'n' => some (.single '\n') | 't' => some (.single '\t') | 'r' => some (.single '\r')
  | 'f' => some (.single '\x0c') | 'v' => some (.single '\x0b') | '0' => some (.single '\x00')
  | _ => none

partial def parseClass : PM Node := do
  let mut neg := false
  if (← peek?) == some '^' then neg := true; advance
  let mut items : List ClassItem := []
  let mut first := true
  repeat
    match ← peek? with
    | none => return patternError "unterminated character set"
    | some ']' =>
        if first then items := items ++ [.single ']']; advance; first := false
        else advance; break
    | some c =>
        first := false
        advance
        let lo : ClassItem ← if c == '\\' then do
            match ← peek? with
            | some e => advance; pure ((escapeItem? e).getD (.single e))
            | none => pure (patternError "bad escape (end of pattern)")
          else pure (.single c)
        -- `a-z` range (a trailing `-` is literal)
        match lo, ← peek? with
        | .single a, some '-' =>
            let s ← get
            match s.src[s.pos + 1]? with
            | some ']' | none => items := items ++ [lo]
            | some b =>
                advance; advance
                let hi ← if b == '\\' then do
                    match ← peek? with
                    | some e => advance; pure (match escapeItem? e with | some (.single x) => x | _ => e)
                    | none => pure b
                  else pure b
                items := items ++ [.range a hi]
        | _, _ => items := items ++ [lo]
  return .cls items neg

mutual

partial def parseAlts : PM (List (List Node)) := do
  let mut alts : List (List Node) := []
  let mut cur : List Node := []
  repeat
    skipVerbose
    match ← peek? with
    | none => break
    | some ')' => break
    | some '|' => advance; alts := alts ++ [cur]; cur := []
    | some _ =>
        let atom ← parseAtom
        let atom ← parseQuantifier atom
        cur := cur ++ [atom]
  return alts ++ [cur]

partial def parseQuantifier (atom : Node) : PM Node := do
  skipVerbose
  let q? : Option (Nat × Option Nat) ← match ← peek? with
    | some '*' => advance; pure (some (0, none))
    | some '+' => advance; pure (some (1, none))
    | some '?' => advance; pure (some (0, some 1))
    | some '{' =>
        let saved ← get
        advance
        let lo ← parseInt?
        match ← peek? with
        | some '}' =>
            match lo with
            | some n => advance; pure (some (n, some n))
            | none => set saved; pure none
        | some ',' =>
            advance
            let hi ← parseInt?
            if (← peek?) == some '}' then advance; pure (some (lo.getD 0, hi))
            else set saved; pure none
        | _ => set saved; pure none
    | _ => pure none
  match q? with
  | none => return atom
  | some (lo, hi) =>
      let greedy ← if (← peek?) == some '?' then do advance; pure false else pure true
      return .rep atom lo hi greedy

partial def parseAtom : PM Node := do
  let some c ← peek? | return patternError "unexpected end of pattern"
  advance
  match c with
  | '.' => return .any
  | '^' => return .lineStart
  | '$' => return .lineEnd
  | '[' => parseClass
  | '(' =>
      let mut idx : Option Nat := none
      if (← peek?) == some '?' then
        advance
        match ← peek? with
        | some ':' => advance
        | some '=' | some '!' =>
            let neg := (← peek?) == some '!'
            advance
            let alts ← parseAlts
            if (← peek?) != some ')' then return patternError "missing ), unterminated subpattern"
            advance
            return .look false neg alts
        | some '<' =>
            advance
            match ← peek? with
            | some '=' | some '!' =>
                let neg := (← peek?) == some '!'
                advance
                let alts ← parseAlts
                if (← peek?) != some ')' then return patternError "missing ), unterminated subpattern"
                advance
                return .look true neg alts
            | _ => return patternError "unknown extension ?<"
        | some '#' =>
            -- `(?#comment)`
            repeat
              match ← peek? with
              | some ')' => advance; break
              | some _ => advance
              | none => return patternError "missing ), unterminated comment"
            return .group none [[]]
        | some c =>
            if "aiLmsux".contains c then
              -- inline flags `(?imsx)`, or scoped `(?i:…)` (applied to the whole pattern here)
              let mut flags : Int := 0
              repeat
                match ← peek? with
                | some 'i' => flags := orFlags flags 2; advance
                | some 'm' => flags := orFlags flags 8; advance
                | some 's' => flags := orFlags flags 16; advance
                | some 'x' => flags := orFlags flags 64; advance
                | some 'a' | some 'L' | some 'u' => advance
                | _ => break
              modify fun st => { st with inline := orFlags st.inline flags,
                                         verbose := st.verbose || (flags / 64) % 2 == 1 }
              if (← peek?) == some ')' then advance; return .group none [[]]
              if (← peek?) != some ':' then return patternError "unknown extension"
              advance
            else if c == 'P' then
              advance
              if (← peek?) == some '=' then
                -- `(?P=name)` backreference
                advance
                let mut name := ""
                repeat
                  match ← peek? with
                  | some ')' => advance; break
                  | some ch => name := name.push ch; advance
                  | none => return patternError "missing ), unterminated name"
                match (← get).names.lookup name with
                | some n => return .backref n
                | none => return patternError s!"unknown group name '{name}'"
              if (← peek?) != some '<' then return patternError "unknown extension"
              advance
              let mut name := ""
              repeat
                match ← peek? with
                | some '>' => advance; break
                | some ch => name := name.push ch; advance
                | none => return patternError "missing >, unterminated name"
              let s ← get
              let n := s.groups + 1
              set { s with groups := n, names := s.names ++ [(name, n)] }
              idx := some n
            else return patternError "unknown extension"
        | none => return patternError "unexpected end of pattern"
      else
        let s ← get
        set { s with groups := s.groups + 1 }
        idx := some (s.groups + 1)
      let alts ← parseAlts
      if (← peek?) != some ')' then return patternError "missing ), unterminated subpattern"
      advance
      return .group idx alts
  | '\\' =>
      let some e ← peek? | return patternError "bad escape (end of pattern)"
      advance
      match e with
      | 'A' => return .strStart
      | 'Z' => return .strEnd
      | 'b' => return .wordBoundary false
      | 'B' => return .wordBoundary true
      | _ =>
          if e.isDigit && e != '0' then
            let d := e.toNat - '0'.toNat
            -- a second digit continues the group number (`\12`)
            match ← peek? with
            | some e2 =>
                if e2.isDigit then advance; return .backref (d * 10 + (e2.toNat - '0'.toNat))
                else return .backref d
            | none => return .backref d
          match escapeItem? e with
          | some (.single x) => return .char x
          | some item => return .cls [item] false
          | none => return .char e
  | ')' => return patternError "unbalanced parenthesis"
  | ch => return .char ch

end

/-- `re.compile(pattern, flags)`. -/
def compile (pattern : String) (flags : Int := 0) : Pattern :=
  let (alts, s) := (do
      let alts ← parseAlts
      if (← peek?).isSome then return (patternError "unbalanced parenthesis" : List (List Node))
      return alts).run { src := pattern.toList.toArray, pos := 0, verbose := hasFlag flags VERBOSE,
                         groups := 0, names := [] }
  { pattern, flags := orFlags flags s.inline, prog := alts, groupCount := s.groups, groupNames := s.names }

end Libraries.re
