import Lake
open Lake DSL

package "uri" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Uri» where
  -- add library configuration options here

lean_exe uriTests where
  root := `Uri.Tests

require binary from git "https://github.com/Lean-zh/binary"
