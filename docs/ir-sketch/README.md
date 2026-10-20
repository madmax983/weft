# IR sketch

Reference files for ADR 0012 and `docs/ir.md`. They are not a workspace member and cargo
does not build them. The design work compiled them as a separate crate to check the IR
types, the verifier and the fact templates. `Cargo.toml.sketch` is the manifest of that
crate. Stage B1 of `docs/plan/core-ir.md` starts the real `weft-ir` crate from these
files.
