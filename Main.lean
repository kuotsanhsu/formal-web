import ES2023

def main : IO Unit := do
  IO.println Lean.toolchain
  IO.println ES2023.versionString
