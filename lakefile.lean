import Lake
open Lake DSL

package «formal-web» where
  -- add package configuration options here

lean_lib ES2023 where
  -- add library configuration options here

@[default_target]
lean_exe es2023 where
  root := `Main
