#!/bin/bash
# toolchains.sh MODE EXPORTS -- downloads and unpacks the toolchains the measurement script of MODE needs
# (toolchains_dist/MANIFEST.txt: MLton with GMP always; the JDK and CPython when a library column needs them; Isabelle2025-2 when EXPORTS is built) into work/toolchains and work/isabelle, and writes work/env.sh.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
mode=$1 exports=$2
cols=$(for b in $(conf "$mode.benchmarks"); do conf "$mode.columns.$b"; done)
# shellcheck disable=SC2086
want="mlton gmp"
# shellcheck disable=SC2086
any_matches '^jgrapht' $cols && want="$want jdk"
# shellcheck disable=SC2086
any_matches '^(scipy|networkx|ortools|sage)' $cols && want="$want python"
[[ "$exports" == built ]] && want="$want isabelle"

arch="$(uname -m)"
case "$arch" in    # x86_64 is the TACAS VM and the tested target; the aarch64 files are listed but untested
  x86_64)  triplet=x86_64-linux-gnu ;;
  aarch64) triplet=aarch64-linux-gnu ;;
  *) fail "unsupported architecture $arch (x86_64, or aarch64)" ;;
esac
dl="$WORK/downloads"; tc="$WORK/toolchains"
mkdir -p "$tc/bin"
say "== toolchains for $arch: $want (toolchains_dist/MANIFEST.txt)"
declare -A file
while read -r a name f m urls; do
  [[ -z "$a" || "$a" == \#* ]] && continue
  [[ "$a" == "$arch" ]] || continue
  has "$name" $want || continue
  file[$name]=$f
  # shellcheck disable=SC2086
  fetch_file "$dl/$f" "$m" $urls || true
done < "$EVAL/toolchains_dist/MANIFEST.txt"

unpack "MLton 20241230" "$dl/${file[mlton]}" "$tc/mlton" || true
if [[ -f "$dl/${file[gmp]}" && ! -f "$tc/gmp/.installed" ]]; then   # gmp.h and libgmp.a for MLton, linked statically
  deb="$dl/${file[gmp]}"
  rm -rf "$tc/gmp" "$tc/gmp.tmp"; mkdir -p "$tc/gmp/include" "$tc/gmp/lib" "$tc/gmp.tmp"
  if command -v dpkg-deb >/dev/null 2>&1; then dpkg-deb -x "$deb" "$tc/gmp.tmp" >>"$LOG" 2>&1 || fail "dpkg-deb -x failed on $deb"
  else ( cd "$tc/gmp.tmp" && ar x "$deb" && tar --zstd -xf data.tar.zst ) >>"$LOG" 2>&1 || fail "could not extract $deb (needs dpkg-deb, or ar and zstd)"; fi
  cp "$tc/gmp.tmp/usr/include/$triplet/gmp.h" "$tc/gmp/include/" && cp "$tc/gmp.tmp/usr/lib/$triplet/libgmp.a" "$tc/gmp/lib/" || fail "gmp.h or libgmp.a not found in $deb"
  rm -rf "$tc/gmp.tmp"; touch "$tc/gmp/.installed"; say "   GMP 6.3.0 (headers and static library): unpacked"
elif [[ -f "$tc/gmp/.installed" ]]; then say "   GMP 6.3.0: already unpacked"; fi
cat > "$tc/bin/mlton" <<EOS
#!/bin/bash
# MLton 20241230 with the evaluation's GMP headers and static library.
here="\$(cd "\$(dirname "\${BASH_SOURCE[0]}")/.." && pwd)"
exec "\$here/mlton/bin/mlton" -cc-opt "-I\$here/gmp/include" -link-opt "-L\$here/gmp/lib" "\$@"
EOS
chmod +x "$tc/bin/mlton"
has jdk $want && { unpack "Temurin JDK 21.0.12.1+1" "$dl/${file[jdk]}" "$tc/jdk" || true; }
has python $want && { unpack "CPython 3.10.12" "$dl/${file[python]}" "$tc/python" || true; }
has isabelle $want && { unpack "Isabelle2025-2" "$dl/${file[isabelle]}" "$WORK/isabelle/Isabelle2025-2" || true; }

# the package index the Python programs install from: PyPI, or a mirror of it when pypi.org does not answer
pipidx=
if has python $want; then
  for i in https://pypi.org/simple https://pypi.tuna.tsinghua.edu.cn/simple https://mirrors.aliyun.com/pypi/simple; do
    if command -v curl >/dev/null 2>&1; then curl -fsSL --connect-timeout 20 --max-time 60 -o /dev/null "$i/pip/" >>"$LOG" 2>&1 && { pipidx=$i; break; }
    else wget -q --timeout=60 --tries=1 -O /dev/null "$i/pip/" >>"$LOG" 2>&1 && { pipidx=$i; break; }; fi
  done
  [[ -z "$pipidx" ]] && say "   NOTE:  neither PyPI nor a mirror of it answers; the Python programs cannot be installed until one does"
fi
python="$tc/python/bin/python3"; [[ -x "$python" ]] || python="$(command -v python3 || true)"
cat > "$WORK/env.sh" <<EOS
# Environment of every build and run of the evaluation (written by setup/toolchains.sh).  Usage:  source work/env.sh
export EVAL_ROOT="$EVAL"
export PATH="$tc/bin:$tc/jdk/bin:$tc/python/bin:\$PATH"
export JAVA_HOME="$tc/jdk"
export MLTON="$tc/bin/mlton"
export PYTHON="$python"
export ISABELLE="$WORK/isabelle/Isabelle2025-2/bin/isabelle"
export USER_HOME="$WORK/isabelle"   # Isabelle keeps its heaps and settings under \$USER_HOME/.isabelle, inside work/
export PIP_DISABLE_PIP_VERSION_CHECK=1
$( [[ -n "$pipidx" && "$pipidx" != https://pypi.org/simple ]] && echo "export PIP_INDEX_URL=\"$pipidx\"   # pypi.org did not answer when the setup ran; a mirror of it" )
export REPRO_CACHE="$dl"
EOS
# shellcheck disable=SC1091
source "$WORK/env.sh"
say "== versions"
{ [[ -x "$tc/mlton/bin/mlton" ]] && "$MLTON" 2>&1 | head -1; [[ -x "$JAVA_HOME/bin/java" ]] && "$JAVA_HOME/bin/java" -version 2>&1 | head -1
  [[ -x "$PYTHON" ]] && "$PYTHON" --version; [[ -x "$ISABELLE" ]] && "$ISABELLE" version; true; } 2>&1 | sed 's/^/   /' | tee -a "$LOG"
