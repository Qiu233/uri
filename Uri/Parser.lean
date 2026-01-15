module

public import Uri.Basic

/-!
[RFC 3986](https://datatracker.ietf.org/doc/html/rfc3986)

-/

public section

namespace Uri.Parser

/-- The primitive effects required to implement uri parser. Some of them are overlapping for performance. -/
class MonadParser (m : Type → Type) where
  satisfy : (Char → Bool) → m Char
  skipChar : Char → m Unit
  skipString : String → m Unit
  attempt : m α → m α
  optional : m α → m (Option α)
  many : m α → m (Array α)
  many1 : m α → m (Array α)
  fail : String → m α
  notFollowedBy : m α → m Unit

variable [Monad m] [∀ α, OrElse (m α)] [MonadParser m]

open MonadParser

@[always_inline, specialize]
private def digitRange (lo hi : Char) : m Char :=
  satisfy fun c => c >= lo && c <= hi

@[always_inline, specialize]
private def manyChars (x : m Char) : m String := do
  let cs ← many x
  return String.ofList cs.toList

@[always_inline, specialize]
private def many1Chars (x : m Char) : m String := do
  let cs ← many1 x
  return String.ofList cs.toList

@[always_inline, specialize]
private def hexDigit : m Char := satisfy fun c =>
  c.isDigit || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')

@[always_inline, specialize]
def unreserved : m Char := satisfy fun c => c.isAlphanum || c matches '-' | '.' | '_' | '~'

@[always_inline, specialize]
def gen_delims : m Char := satisfy fun c => c matches ':' | '/' | '?' | '#' | '[' | ']' | '@'

@[always_inline, specialize]
def sub_delims : m Char := satisfy fun c => c matches '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '='

@[always_inline, specialize]
def reserved : m Char := gen_delims <|> sub_delims

private def decode_hex : Char → Nat := fun c =>
  if c.isDigit then
    (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then
    (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then
    (c.toNat - 'a'.toNat + 10)
  else
    panic! "invalid character"

@[specialize]
def pct_encoded : m String := do
  skipChar '%'
  let a ← hexDigit
  let b ← hexDigit
  return s!"%{a}{b}"

@[always_inline]
private def c2s : Char → String := fun c => String.ofList [c]

@[always_inline, specialize]
private def many_concat (x : m String) : m String := do
  let xs ← many x
  return String.intercalate "" xs.toList

@[always_inline, specialize]
private def many1_concat (x : m String) : m String := do
  let xs ← many1 x
  return String.intercalate "" xs.toList

@[specialize]
def pchar' : m String := c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims <|> c2s <$> satisfy fun c => c matches ':' | '@'

@[specialize]
def scheme : m String := do
  let l ← satisfy Char.isAlpha
  let t ← manyChars (satisfy fun c => c.isAlphanum || c matches '+' | '-' | '.')
  return String.ofList (l :: t.toList)

@[always_inline, specialize]
def segment : m String := many_concat pchar'

@[always_inline, specialize]
def segment_nz : m String := many1_concat pchar'

@[always_inline, specialize]
def segment_nz_nc : m String := many1_concat <| c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims <|> c2s <$> satisfy fun c => c matches '@'

@[specialize]
def path_abempty : m String := do
  let xs ← many (skipChar '/' *> segment)
  let xs := xs.map fun x => s!"/{x}"
  return String.intercalate "" xs.toList

@[specialize]
def path_absolute : m String := do
  skipChar '/'
  match ← optional segment_nz with
  | none => return "/"
  | some l =>
    let l := s!"/{l}"
    let xs ← many (skipChar '/' *> segment)
    let xs := xs.map fun x => s!"/{x}"
    let xs := l :: xs.toList
    return String.intercalate "" xs

@[specialize]
def path_noscheme : m String := do
  let l ← segment_nz_nc
  let xs ← many (skipChar '/' *> segment)
  let xs := xs.map fun x => s!"/{x}"
  let xs := l :: xs.toList
  return String.intercalate "" xs

@[specialize]
def path_rootless : m String := do
  let l ← segment_nz
  let xs ← many (skipChar '/' *> segment)
  let xs := xs.map fun x => s!"/{x}"
  let xs := l :: xs.toList
  return String.intercalate "" xs

@[inline, specialize]
def userinfo : m String := do
  many_concat <| c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims <|> c2s <$> satisfy fun c => c matches ':'

@[inline, specialize]
private def takeUpTo (n : Nat) (p : m α) : m (Array α) :=
  rest n #[]
where
  rest : Nat → Array α → m (Array α)
    | 0, xs => return xs
    | n+1, xs => do
      match ← optional (attempt p) with
      | some x => rest n <| xs.push x
      | none => return xs

@[inline, specialize]
def take (n : Nat) (p : m α) : m (Array α) := attempt <| rest n #[]
where
  rest : Nat → Array α → m (Array α)
    | 0, xs => return xs
    | n+1, xs => do rest n <| xs.push (← p)

@[specialize]
def h16 : m UInt16 := do
  let first ← hexDigit
  let rest ← takeUpTo 3 hexDigit
  let xs := first :: rest.toList
  let xs := xs.map decode_hex
  let x :: xs := xs | unreachable!
  let val := xs.foldl (init := x) fun acc x => acc * 16 + x
  assert! val < 2 ^ 16
  return UInt16.ofNat val

@[specialize]
def dec_octet : m UInt8 := do
  let s ← many1Chars <| satisfy fun c => c.isDigit
  if s.length > 1 && s.startsWith "0" then
    fail "leading zeros are not valid in IPv4 octets"
  if s.length > 3 then
    fail "IPv4 octet is too long"
  let ts := s.toList.map fun x => x.toNat - '0'.toNat
  let t :: ts := ts | unreachable!
  let val := ts.foldl (init := t) fun acc t => acc * 10 + t
  if val > 255 then
    fail "IPv4 octet is out of range"
  return UInt8.ofNat val

@[specialize]
def ipv4address : m Std.Net.IPv4Addr := do
  let a ← dec_octet
  skipChar '.'
  let b ← dec_octet
  skipChar '.'
  let c ← dec_octet
  skipChar '.'
  let d ← dec_octet
  return Std.Net.IPv4Addr.ofParts a b c d

@[specialize]
def ls32 : m (UInt16 × UInt16) :=
  (attempt do
    let a ← h16
    skipChar ':'
    let b ← h16
    return (a, b))
    <|> (ipv4address >>= fun x => return (x.octets[0].toUInt16 * (256 : UInt16) + x.octets[1].toUInt16, x.octets[2].toUInt16 * (256 : UInt16) + x.octets[3].toUInt16))

@[always_inline, specialize]
private def char : Char → m Char := fun c => satisfy (· == c)

@[specialize]
private def sep1 (x : m α) (s : m Unit) : m (Array α) := do
  let l ← x
  let mut t := #[l]
  repeat
    if let some v ← optional (attempt (s *> x)) then
      t := t.push v
    else break
  return t

@[specialize]
private def sep1UpTo (n : Nat) (x : m α) (s : m Unit) : m (Array α) := do
  let l ← x
  let mut t := #[l]
  repeat
    if t.size ≥ n then break
    if let some v ← optional (attempt (s *> x)) then
      t := t.push v
    else break
  return t

@[specialize]
private def sepUpTo (n : Nat) (x : m α) (s : m Unit) : m (Array α) := attempt (sep1UpTo n x s) <|> (pure #[])

@[specialize]
def ipv6address : m Std.Net.IPv6Addr := do
  let ret (t : Array UInt16) := do
    if h : t.size = 8 then
      return { segments := ⟨t, h⟩ : Std.Net.IPv6Addr }
    else
      unreachable!
  let t ← sepUpTo 8 (h16 <* notFollowedBy (char '.')) (skipChar ':')
  if t.size == 8 then
    ret t
  else if t.size == 7 then
    skipString "::"
    ret <| t.push 0
  else if t.size == 6 then
    (do
      skipString "::"
      let a ← h16
      ret <| t.push 0 |>.push a)
    <|> (do
      skipChar ':'
      let (a, b) ← ls32 -- ipv4
      ret <| t.push a |>.push b)
  else
    skipString "::"
    let r ← sepUpTo (7 - t.size) (h16  <* notFollowedBy (char '.')) (skipChar ':')
    if r.size == 7 - t.size then
      ret <| t.push 0 |>.append r
    else if r.size == 6 - t.size then
      ret <| t.append #[0, 0] |>.append r
    else
      (attempt do
        skipChar ':'
        let (a, b) ← ls32 -- ipv4
        let pad := 8 - t.size - r.size - 2
        ret <| t.append (Array.replicate pad 0) |>.append r |>.append #[a, b])
      <|> (do
        let pad := 8 - t.size - r.size
        ret <| t.append (Array.replicate pad 0) |>.append r)

@[specialize]
def ipv_future : m String := do
  skipChar 'v'
  let version ← many1Chars hexDigit
  skipChar '.'
  let body ← many1Chars (unreserved <|> sub_delims <|> char ':')
  return "v" ++ version ++ "." ++ body

@[specialize]
def ip_literal : m Host := do
  let _ ← char '['
  let inner ← attempt (Host.ipv6 <$> ipv6address) <|> Host.ipvFuture <$> ipv_future
  let _ ← char ']'
  return inner

@[specialize]
def reg_name : m String := many_concat (c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims)

@[specialize]
public def host : m Host :=
  attempt ip_literal
  <|> (attempt (Host.ipv4 <$> ipv4address))
  <|> (Host.regName <$> reg_name)

@[specialize]
def port? : m (Option UInt16) := do
  let v ← manyChars (satisfy Char.isDigit)
  if v.length == 0 then
    return none
  let xs := v.toList
  let xs := xs.map fun x => x.toNat - '0'.toNat
  let x :: xs := xs | unreachable!
  let val := xs.foldl (init := x) fun acc t => acc * 10 + t
  if val ≥ 2 ^ 16 then
    fail "port too large"
  return some (UInt16.ofNat val)

@[specialize]
public def authority : m Authority := do
  let ui? ← optional <| attempt (userinfo <* skipChar '@')
  let host ← host
  let port? ← optional <| attempt (skipChar ':' *> port?)
  let port? := port?.join
  return { userInfo? := ui?, host, port? }

@[specialize]
public def hier_part : m (Option Authority × String) := do
  let ss := do
    skipString "//"
    let auth ← authority
    let path ← path_abempty
    return (some auth, path)
  ss <|> (path_absolute <&> (none, ·)) <|> (path_rootless <&> (none, ·)) <|> (pure (none, ""))

@[always_inline, specialize]
def query : m String := many_concat (pchar' <|> c2s <$> char '/' <|> c2s <$> char '?')

@[always_inline, specialize]
def fragment : m String := many_concat (pchar' <|> c2s <$> char '/' <|> c2s <$> char '?')

@[specialize]
public def uri : m Uri := do
  let scheme ← scheme
  skipChar ':'
  let (auth?, path) ← hier_part
  let query? ← optional do
    skipChar '?'
    query
  let fragment? ← optional do
    skipChar '#'
    fragment
  return { scheme? := some scheme, path, authority? := auth?, query?, fragment? }

@[specialize]
def absolute_uri : m Uri := do
  let scheme ← scheme
  skipChar ':'
  let (auth?, path) ← hier_part
  let query? ← optional do
    skipChar '?'
    query
  return { scheme? := some scheme, path, authority? := auth?, query?, fragment? := none }

@[specialize]
def relative_part : m (Option Authority × String) := do
  let ss := do
    skipString "//"
    let auth ← authority
    let path ← path_abempty
    return (some auth, path)
  ss <|> (path_absolute <&> (none, ·)) <|> (path_noscheme <&> (none, ·)) <|> (pure (none, ""))

@[specialize]
def relative_ref : m Uri := do
  let (auth?, path) ← relative_part
  let query? ← optional do
    skipChar '?'
    query
  let fragment? ← optional do
    skipChar '#'
    fragment
  return { scheme? := none, path, authority? := auth?, query?, fragment? }

@[always_inline, specialize]
def uri_reference : m Uri := attempt uri <|> relative_ref

end Uri.Parser
