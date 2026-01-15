module

public import Std.Net

public inductive Uri.Host where
  | ipv4 : Std.Net.IPv4Addr → Host
  | ipv6 : Std.Net.IPv6Addr → Host
  | ipvFuture : String → Host
  | regName : String → Host
deriving Inhabited

public structure Uri.Authority where
  userInfo? : Option String
  host : Uri.Host
  port? : Option UInt16
deriving Inhabited

public structure Uri where
  /-- The scheme without trailing colon, for example `https` in `https://...`.

      `none` when parsing `relative-ref`.
   -/
  scheme? : Option String
  authority? : Option Uri.Authority
  path : String
  /-- Query part without the leading `?`, for example `a=1` in `https://127.0.0.1?a=1` -/
  query? : Option String := Option.none
  /-- Fragment part without the leading `#`, for example `Title` in `https://127.0.0.1#Title` -/
  fragment? : Option String := Option.none
deriving Inhabited

public def Uri.Host.toString (host : Uri.Host) : String :=
  match host with
  | ipv4 v4 => s!"{v4.toString}"
  | ipv6 v6 => s!"[{v6.toString}]"
  | ipvFuture c => s!"[{c}]"
  | regName n => n

public def Uri.Authority.toString (auth : Uri.Authority) : String :=
  s!"{u}{auth.host.toString}{port}"
  where
    u := match auth.userInfo? with
      | none => ""
      | some x => s!"{x}@"
    port := match auth.port? with
      | none => ""
      | some x => s!":{x}"

public def Uri.toString (uri : Uri) : String :=
  s!"{scheme}:{auth}{uri.path}{q}{f}"
  where
    scheme := match uri.scheme? with
      | none => ""
      | some a => s!"{a}:"
    auth := match uri.authority? with
      | none => ""
      | some a => s!"//{a.toString}"
    q := match uri.query? with
      | none => ""
      | some x => s!"?{x}"
    f := match uri.fragment? with
      | none => ""
      | some x => s!"#{x}"

public instance : ToString Uri.Host := ⟨Uri.Host.toString⟩
public instance : ToString Uri.Authority := ⟨Uri.Authority.toString⟩
public instance : ToString Uri := ⟨Uri.toString⟩
