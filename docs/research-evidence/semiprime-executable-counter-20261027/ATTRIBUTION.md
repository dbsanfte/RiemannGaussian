# Source attribution and status

Independent Python implementation of definitions from OpenAI Math, Apache-2.0:
https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean

Pinned commit: `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. A copy of the license is `LICENSE.OpenAI-Math`. Lean declarations are not copied into Python, and no executable refinement theorem is claimed. The local vendor rewrites import prefixes only; its pin is `/home/dbsanfte/riemann/formal/vendor/openai-semiprime/upstream-pin.json`.

The frozen counter is dynamically imported from `docs/research-evidence/semiprime-shared-counter-20261026/shared_counter.py` without modification. The Python constructor implements the source complete-block construction, rather than the earlier diagnostic partial-copy/eigenbasis constructor.
