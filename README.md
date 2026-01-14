# uri
Lean 4 package for uri parsing, respecting [RFC 3986](https://datatracker.ietf.org/doc/html/rfc3986).

# Usage

```Lean
import Uri

#eval Uri.parse "https://127.0.0.1"
```

To validate uri literal at compile-time:

```Lean
import Uri
import Uri.Meta

#eval uri! "https://127.0.0.1"
```
