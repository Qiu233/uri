module

public import Std

public inductive Uri.Host where
  | ipv4 : Std.Net.IPv4Addr → Host
  | ipv6 : Std.Net.IPv6Addr → Host
  | ipvFuture : String → Host
  | regName : String → Host
deriving Inhabited

public structure Uri.Authority where
  userInfo : String
  host : Uri.Host
  port : String
deriving Inhabited

public structure Uri where
  scheme : String
  authority? : Option Uri.Authority
  path : String
  query : String
  fragment : String
deriving Inhabited
