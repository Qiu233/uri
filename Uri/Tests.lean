import Uri

open Uri

private def assert (cond : Bool) (msg : String) : IO Unit :=
  if cond then
    pure ()
  else
    throw <| IO.userError msg

private def assertEq {α} [DecidableEq α] (label : String) (a b : α) : IO Unit :=
  assert (decide (a = b)) s!"{label}: value mismatch"

private def hostEq : Uri.Host → Uri.Host → Bool
  | .ipv4 a, .ipv4 b => decide (a = b)
  | .ipv6 a, .ipv6 b => decide (a = b)
  | .ipvFuture a, .ipvFuture b => a == b
  | .regName a, .regName b => a == b
  | _, _ => false

private def expectHost (label input : String) (expectedHost : Uri.Host) (expectedPath : String := "/") : IO Unit := do
  match Uri.parse input with
  | .ok uri =>
      assertEq (label ++ ": scheme") uri.scheme "http"
      assertEq (label ++ ": path") uri.path expectedPath
      assertEq (label ++ ": query") uri.query ""
      assertEq (label ++ ": fragment") uri.fragment ""
      match uri.authority? with
      | some auth =>
          assertEq (label ++ ": userinfo") auth.userInfo ""
          assertEq (label ++ ": port") auth.port ""
          assert (hostEq auth.host expectedHost) s!"{label}: host mismatch"
      | none => throw <| IO.userError s!"{label}: missing authority"
  | .error err => throw <| IO.userError s!"{label}: parse error: {err}"

private def expectParseError (label input : String) : IO Unit :=
  match Uri.parse input with
  | .ok _ => throw <| IO.userError s!"{label}: expected parse error"
  | .error _ => pure ()

def main : IO Unit := do
  let v4 := Std.Net.IPv4Addr.ofParts 192 0 2 1
  expectHost "ipv4-basic" "http://192.0.2.1/" (.ipv4 v4)

  expectHost "ipv4-out-of-range-regname" "http://256.0.0.1/" (.regName "256.0.0.1")
  expectHost "ipv4-leading-zero-regname" "http://01.2.3.4/" (.regName "01.2.3.4")

  let v6 := Std.Net.IPv6Addr.ofParts 0x2001 0x0db8 0 0 0 0 0 1
  expectHost "ipv6-basic" "http://[2001:db8::1]/" (.ipv6 v6)

  let v6v4 := Std.Net.IPv6Addr.ofParts 0 0 0 0 0 0xffff 0xc000 0x0280
  expectHost "ipv6-embedded-v4" "http://[::ffff:192.0.2.128]/" (.ipv6 v6v4)

  expectHost "ipvfuture" "http://[v1.fe80:abc]/" (.ipvFuture "v1.fe80:abc")

  expectParseError "ipv6-double-elide" "http://[2001::db8::1]/"
  expectParseError "ipv6-too-many-segments" "http://[1:2:3:4:5:6:7:8:9]/"

  expectHost "authority-empty-path" "http://example.com" (.regName "example.com") (expectedPath := "")
  expectHost "authority-root-path" "http://example.com/" (.regName "example.com")

  match Uri.parse "mailto:foo:bar" with
  | .ok uri =>
      assertEq "rootless-colon scheme" uri.scheme "mailto"
      assertEq "rootless-colon path" uri.path "foo:bar"
      match uri.authority? with
      | none => pure ()
      | some _ => throw <| IO.userError "rootless-colon authority should be none"
  | .error err => throw <| IO.userError s!"rootless-colon parse error: {err}"
