module

public import Uri.Parser

section

/-- parses RFC 3986 `URI` -/
public def Uri.parse : String → Except String Uri := fun s =>
  (Uri.Parser.uri <* Binary.shouldBeEOI true) |>.run s.toUTF8 |>.toExceptString

/-- parses RFC 3986 `URI-reference` -/
public def Uri.parse_reference : String → Except String Uri := fun s =>
  (Uri.Parser.uri_reference <* Binary.shouldBeEOI true) |>.run s.toUTF8 |>.toExceptString

end
