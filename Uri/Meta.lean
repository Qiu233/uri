module

public meta import Lean
public meta import Uri.Parser

/-!
Compile-time uri literal elaboration.
TODO:
1. Rewrite a dedicated meta parser.
2. Create IPv4 and IPv6 from parts rather than from string.
-/

public meta section

open Lean Elab Parser PrettyPrinter

namespace Uri.Parser

-- TODO: Rewrite a dedicated meta parser.

-- @[always_inline]
-- def unreserved : Char → Bool := fun c => c.isAlphanum || c matches '-' | '.' | '_' | '~'

-- @[always_inline]
-- def gen_delims : Char → Bool := fun c => c matches ':' | '/' | '?' | '#' | '[' | ']' | '@'

-- @[always_inline]
-- def sub_delims : Char → Bool := fun c => c matches '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '='

-- @[always_inline]
-- def reserved : Char → Bool := fun c => gen_delims c || sub_delims c

-- @[always_inline]
-- def is_hex : Char → Bool := fun c => c.isDigit || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')

-- def pcharKind := `pchar

-- def pcharFn : ParserFn := fun c s =>
--   let startPos := s.pos
--   if h : c.atEnd startPos then
--     s.mkEOIError
--   else
--     let curr := c.get' startPos h
--     if unreserved curr || sub_delims curr || curr matches ':' | '@' then
--       let s := s.setPos (c.next' startPos h)
--       mkNodeToken pcharKind startPos false c s
--     else if curr == '%' then
--       let pos := c.next' startPos h
--       if h : c.atEnd pos then
--         s.mkEOIError
--       else
--         let a := c.get' pos h
--         if !is_hex a then
--           s.mkUnexpectedErrorAt "hex" pos
--         else
--           let pos := c.next' pos h
--           if h : c.atEnd pos then
--             s.mkEOIError
--           else
--             let b := c.get' pos h
--             if !is_hex b then
--               s.mkUnexpectedErrorAt "hex" pos
--             else
--               let s := s.setPos (c.next pos)
--               mkNodeToken pcharKind startPos false c s
--     else
--       s.mkUnexpectedErrorAt "pchar" startPos

-- run_meta do
--   modifyEnv fun env =>
--     addSyntaxNodeKind env pcharKind

-- public def pchar : Parser where
--   fn := pcharFn
--   info := mkAtomicInfo "pchar"

-- open Parenthesizer in
-- @[parenthesizer pchar]
-- public meta def pchar.parenthesizer : Parenthesizer := do
--   visitToken

-- open Formatter Lean.Syntax.MonadTraverser in
-- @[formatter pchar]
-- public meta def pchar.formatter : Formatter := do
--   checkKind pcharKind
--   visitArgs do
--     let stx ← getCur
--     match stx with
--     | .atom _ s =>
--       modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
--       goLeft
--     | _ => throwError s!"not a pchar: {← getCur}"

def uriLitKind := `uriLit

def uriLitFn : ParserFn := fun c s =>
  let startPos := s.pos
  let initStackSz := s.stxStack.size
  let s := strLitFn c s
  if s.hasError then
    s
  else
    let stx := s.stxStack.back
    match stx.isStrLit? with
    | none => s.mkErrorAt "string literal" startPos (some initStackSz)
    | some value =>
      match Uri.parse value with
      | .ok _ =>
        s.mkNode uriLitKind initStackSz
      | .error err =>
        s.mkErrorAt (s!"invalid URI: {err}") startPos (some initStackSz)

run_meta do
  modifyEnv fun env =>
    addSyntaxNodeKind env uriLitKind

public def uriLitNoAntiquot : Parser where
  fn := uriLitFn
  info := mkAtomicInfo "uriLit"

public def uriLit : Parser := withAntiquot (mkAntiquot "uriLit" uriLitKind) uriLitNoAntiquot

open Parenthesizer in
@[parenthesizer uriLit, combinator_parenthesizer uriLit]
public meta def uriLit.parenthesizer : Parenthesizer := do
  visitToken

open Formatter Lean.Syntax.MonadTraverser in
@[formatter uriLit, combinator_formatter uriLit]
public meta def uriLit.formatter : Formatter := do
  checkKind uriLitKind
  visitArgs do
    visitArgs do
      let stx ← getCur
      match stx with
      | .atom _ s =>
        modify fun st => { st with stack := st.stack.push s, isUngrouped := false }
        goLeft
      | _ => throwError s!"not a uriLit: {← getCur}"

syntax (name := uriQuot) "uri!" uriLit : term

def quoteHost (host : Uri.Host) : Term.TermElabM Term := do
  match host with
  | .ipv4 v4 => ``(Uri.Host.ipv4 (Option.get! (Std.Net.IPv4Addr.ofString $(quote v4.toString))))
  | .ipv6 v6 => ``(Uri.Host.ipv6 (Option.get! (Std.Net.IPv6Addr.ofString $(quote v6.toString))))
  | .ipvFuture x => ``(Uri.Host.ipvFuture $(quote x):str)
  | .regName x => ``(Uri.Host.regName $(quote x):str)

def quoteAuth (auth : Uri.Authority) : Term.TermElabM Term := do
  let ui ← match auth.userInfo? with
    | none => `(Option.none)
    | some x => `(Option.some $(quote x))
  let host ← quoteHost auth.host
  let port ← match auth.port? with
    | none => `(Option.none)
    | some x => `(Option.some $(quote x.toNat))
  `({ userInfo? := $ui, host := $host, port? := $port : Uri.Authority })

def quoteUri (uri : Uri) : Term.TermElabM Term := do
  let scheme : TSyntax `str := quote uri.scheme
  let auth ← uri.authority?.mapM quoteAuth
  let auth ← auth.mapM fun x => `(Option.some $x)
  let auth ← auth.getDM `(Option.none)
  let path : TSyntax `str := quote uri.path
  let query ← match uri.query? with
    | none => `(Option.none)
    | some x => `(Option.some $(quote x))
  let fragment ← match uri.fragment? with
    | none => `(Option.none)
    | some x => `(Option.some $(quote x))
  `({ scheme := $scheme, authority? := $auth, path := $path, query? := $query, fragment? := $fragment : Uri })

@[term_elab Uri.Parser.uriQuot]
def elabUriQuot : Term.TermElab := fun stx type? => do
  let `(Uri.Parser.uriQuot| uri! $v:uriLit) := stx |
    println! "{stx}"
    throwUnsupportedSyntax
  let t := v.raw[0]
  if t.isMissing then
    throwErrorAt v "missing syntax"
  let t : TSyntax `str := TSyntax.mk t
  let content := t.getString
  let uri ← match Uri.parse content with
    | Except.ok r => pure r
    | Except.error err => throwErrorAt v "failed to parse: {err}"
  let s ← quoteUri uri
  let v ← Term.elabTerm s (some (Expr.const ``Uri []))
  return v
