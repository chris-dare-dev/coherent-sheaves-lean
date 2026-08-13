/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Anchor.TStructure

/-!
# Compatibility with the foundational stability library

Bridges between definitions this repository restates anchor-free and the
foundational library's versions of the same notion. Every module here imports
`BridgelandStability` on purpose; nothing listed in
`scripts/check_anchor_free.py` may depend on this subsystem.
-/
