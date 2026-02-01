module

public import Uri.Basic
public import Binary

/-!
[RFC 3986](https://datatracker.ietf.org/doc/html/rfc3986)

-/

public section

namespace Uri.Parser

open Binary UTF8

@[always_inline]
private def digitRange (lo hi : Char) : Get Char :=
  satisfy fun c => c >= lo && c <= hi

@[always_inline]
private def hexDigit : Get Char := satisfy fun c =>
  c.isDigit || ('A' ≤ c && c ≤ 'F') || ('a' ≤ c && c ≤ 'f')

@[always_inline]
def unreserved : Get Char := satisfy fun c => c.isAlphanum || c matches '-' | '.' | '_' | '~'

@[always_inline]
def gen_delims : Get Char := satisfy fun c => c matches ':' | '/' | '?' | '#' | '[' | ']' | '@'

@[always_inline]
def sub_delims : Get Char := satisfy fun c => c matches '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '='

@[always_inline]
def reserved : Get Char := gen_delims <|> sub_delims

@[inline]
private def decode_hex : Char → Nat := fun c =>
  if c.isDigit then
    (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then
    (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then
    (c.toNat - 'a'.toNat + 10)
  else
    panic! "invalid character"

@[always_inline]
def pct_encoded : Get String := do
  skipChar '%'
  let a ← hexDigit
  let b ← hexDigit
  return s!"%{a}{b}"

@[always_inline]
private def c2s : Char → String := fun c => String.ofList [c]

@[always_inline, specialize]
private def many_concat (x : Get String) : Get String := do
  let xs ← many x
  return String.intercalate "" xs.toList

@[always_inline, specialize]
private def many1_concat (x : Get String) : Get String := do
  let xs ← many1 x
  return String.intercalate "" xs.toList

@[always_inline]
def pchar' : Get String := c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims <|> c2s <$> satisfy fun c => c matches ':' | '@'

@[always_inline]
def scheme : Get String := do
  let l ← satisfy Char.isAlpha
  let t ← manyChars (satisfy fun c => c.isAlphanum || c matches '+' | '-' | '.')
  return String.ofList (l :: t.toList)

@[always_inline]
def segment : Get String := many_concat pchar'

@[always_inline]
def segment_nz : Get String := many1_concat pchar'

@[always_inline]
def segment_nz_nc : Get String :=
  many1_concat <| c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims <|> c2s <$> satisfy fun c => c matches '@'

@[always_inline]
def path_abempty : Get String := do
  let xs ← many (skipChar '/' *> segment)
  let xs := xs.map fun x => s!"/{x}"
  return String.intercalate "" xs.toList

@[always_inline]
def path_absolute : Get String := do
  skipChar '/'
  match ← optional segment_nz with
  | none => return "/"
  | some l =>
    let l := s!"/{l}"
    let xs ← many (skipChar '/' *> segment)
    let xs := xs.map fun x => s!"/{x}"
    let xs := l :: xs.toList
    return String.intercalate "" xs

@[always_inline]
def path_noscheme : Get String := do
  let l ← segment_nz_nc
  let xs ← many (skipChar '/' *> segment)
  let xs := xs.map fun x => s!"/{x}"
  let xs := l :: xs.toList
  return String.intercalate "" xs

@[always_inline]
def path_rootless : Get String := do
  let l ← segment_nz
  let xs ← many (skipChar '/' *> segment)
  let xs := xs.map fun x => s!"/{x}"
  let xs := l :: xs.toList
  return String.intercalate "" xs

@[always_inline]
def userinfo : Get String := do
  many_concat <| c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims <|> c2s <$> satisfy fun c => c matches ':'

@[inline]
def h16 : Get UInt16 := do
  let first ← hexDigit
  let rest ← takeUpTo 3 hexDigit
  let xs := first :: rest.toList
  let xs := xs.map decode_hex
  let x :: xs := xs | unreachable!
  let val := xs.foldl (init := x) fun acc x => acc * 16 + x
  assert! val < 2 ^ 16
  return UInt16.ofNat val

@[inline]
def dec_octet : Get UInt8 := do
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

@[always_inline]
def ipv4address : Get Std.Net.IPv4Addr := do
  let a ← dec_octet
  skipChar '.'
  let b ← dec_octet
  skipChar '.'
  let c ← dec_octet
  skipChar '.'
  let d ← dec_octet
  return Std.Net.IPv4Addr.ofParts a b c d

def ls32 : Get (UInt16 × UInt16) :=
  (do
    let a ← h16
    skipChar ':'
    let b ← h16
    return (a, b))
  <|> (ipv4address >>= fun x =>
    return (x.octets[0].toUInt16 * (256 : UInt16) + x.octets[1].toUInt16,
      x.octets[2].toUInt16 * (256 : UInt16) + x.octets[3].toUInt16))

@[always_inline]
private def char : Char → Get Char := fun c => satisfy (· == c)

def ipv6address : Get Std.Net.IPv6Addr := do
  let ret (t : Array UInt16) := do
    if h : t.size = 8 then
      return { segments := ⟨t, h⟩ : Std.Net.IPv6Addr }
    else
      unreachable!
  let t ← sepByUpTo 8 (h16 <* notFollowedBy (char '.')) (skipChar ':')
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
      let (a, b) ← ls32
      ret <| t.push a |>.push b)
  else
    skipString "::"
    let r ← sepByUpTo (7 - t.size) (h16  <* notFollowedBy (char '.')) (skipChar ':')
    if r.size == 7 - t.size then
      ret <| t.push 0 |>.append r
    else if r.size == 6 - t.size then
      ret <| t.append #[0, 0] |>.append r
    else
      (do
        skipChar ':'
        let (a, b) ← ls32 -- ipv4
        let pad := 8 - t.size - r.size - 2
        ret <| t.append (Array.replicate pad 0) |>.append r |>.append #[a, b])
      <|> (do
        let pad := 8 - t.size - r.size
        ret <| t.append (Array.replicate pad 0) |>.append r)

@[inline]
def ipv_future : Get String := do
  skipChar 'v'
  let version ← many1Chars hexDigit
  skipChar '.'
  let addr ← many1Chars <| satisfy fun c =>
    c.isAlphanum || c matches '.' | '-' | '_' | '~' | '!' | '$' | '&' | '\'' | '(' | ')' |
      '*' | '+' | ',' | ';' | '=' | ':'
  return s!"v{version}.{addr}"

@[inline]
def ip_literal : Get Host := do
  skipChar '['
  let host ← (Host.ipv6 <$> ipv6address) <|> (Host.ipvFuture <$> ipv_future)
  skipChar ']'
  return host

@[always_inline]
def reg_name : Get String := many_concat (c2s <$> unreserved <|> pct_encoded <|> c2s <$> sub_delims)

@[always_inline]
def host : Get Host :=
  (ip_literal) <|> (Host.ipv4 <$> ipv4address) <|> (Host.regName <$> reg_name)

@[specialize]
def port : Get UInt16 := do
  let v ← many1Chars (satisfy Char.isDigit)
  let xs := v.toList
  let xs := xs.map fun x => x.toNat - '0'.toNat
  let x :: xs := xs | unreachable!
  let val := xs.foldl (init := x) fun acc t => acc * 10 + t
  if val ≥ 2 ^ 16 then
    fail "port too large"
  return UInt16.ofNat val

@[always_inline]
def port? : Get (Option UInt16) := optional port

@[inline]
def authority : Get Authority := do
  let userInfo? ← optional (userinfo <* skipChar '@')
  let host ← host
  let port? ← optional (skipChar ':' *> port)
  return { userInfo?, host, port? }

@[inline]
def hier_part : Get (Option Authority × String) := do
  (do
    skipString "//"
    let auth ← authority
    let path ← path_abempty
    return (some auth, path))
  <|> (path_absolute >>= fun x => return (none, x))
  <|> (path_rootless >>= fun x => return (none, x))
  <|> (pure (none, ""))

@[always_inline]
def query : Get String := many_concat (pchar' <|> c2s <$> char '/' <|> c2s <$> char '?')

@[always_inline]
def fragment : Get String := many_concat (pchar' <|> c2s <$> char '/' <|> c2s <$> char '?')

def uri : Get Uri := do
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

def absolute_uri : Get Uri := do
  let scheme ← scheme
  skipChar ':'
  let (auth?, path) ← hier_part
  let query? ← optional do
    skipChar '?'
    query
  return { scheme? := some scheme, authority? := auth?, path, query? }

def relative_part : Get (Option Authority × String) := do
  (do
    skipString "//"
    let auth ← authority
    let path ← path_abempty
    return (some auth, path))
  <|> (path_absolute >>= fun x => return (none, x))
  <|> (path_noscheme >>= fun x => return (none, x))
  <|> (pure (none, ""))

def relative_ref : Get Uri := do
  let (auth?, path) ← relative_part
  let query? ← optional do
    skipChar '?'
    query
  let fragment? ← optional do
    skipChar '#'
    fragment
  return { scheme? := none, authority? := auth?, path, query?, fragment? }

@[always_inline]
def uri_reference : Get Uri := uri <|> relative_ref

@[always_inline]
def uri_host : Get Host := host

@[always_inline]
def absolute_path : Get String := do
  let ss ← many1 (skipChar '/' *> segment)
  return String.intercalate "" <| ss.toList.map (fun x => s!"/{x}")

end Uri.Parser

end
