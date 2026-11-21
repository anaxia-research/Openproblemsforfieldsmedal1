#!/usr/bin/env bash
# Full verification of the 14-part Lean archive (alpo.ge/lean.tar.gz.part01..14).
# Needs: curl, tar, git, roughly 60 GB of free disk and many cores (about 6 h on 64 cores).
# Output: verify.log. Please send that file back.
set -euo pipefail
exec > >(tee verify.log) 2>&1
mkdir -p rh-verify && cd rh-verify
for i in $(seq -w 1 14); do curl -fsSO "https://alpo.ge/lean.tar.gz.part$i"; done
sha256sum lean.tar.gz.part*
cat lean.tar.gz.part* > lean.tar.gz && tar -xzf lean.tar.gz && cd lean
command -v elan >/dev/null || { curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none; }
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
echo "== scan =="; grep -rnwE 'sorry|admit|native_decide|implemented_by|unsafe|axiom' --include=*.lean src | wc -l
time lake build
cat > /tmp/CheckRH.lean <<'EOF'
import Main
#check (riemannHypothesis : RiemannHypothesis)
#print axioms riemannHypothesis
#print axioms LFunction_eq_zero_re_of_isPrimitive
EOF
echo "== axioms =="; lake env lean /tmp/CheckRH.lean
# Optional independent kernel re-check, if lean4checker is installed:
# lake env lean4checker Main
