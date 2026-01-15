module

public import Uri.Parser
public import Std.Internal.Parsec.String

open Std.Internal.Parsec Std.Internal.Parsec.String in

section

@[always_inline]
local instance : Uri.Parser.MonadParser Parser where
  satisfy := satisfy
  skipChar := skipChar
  skipString := skipString
  attempt := attempt
  optional := optional
  many := many
  many1 := many1
  fail := fail
  notFollowedBy := notFollowedBy

/-- parses RFC 3986 `URI` -/
public def Uri.parse : String → Except String Uri := fun s => Parser.run (Uri.Parser.uri (m := Parser) <* eof) s

/-- parses RFC 3986 `URI-reference` -/
public def Uri.parse_reference : String → Except String Uri := fun s => Parser.run (Uri.Parser.uri_reference (m := Parser) <* eof) s

end
