#!/bin/bash
# toolchains.sh MODE EXPORTS -- downloads and unpacks the toolchains the measurement script of MODE needs
# (toolchains_dist/MANIFEST.txt: MLton with GMP and the paper's compilers, gcc and g++ 11.4.0 of Ubuntu 22.04, always; CMake 3.22.1
# when a LEMON column needs it; the JDK and CPython when a library column needs them; Isabelle2025-2 when EXPORTS is built) into
# work/toolchains and work/isabelle, and writes work/env.sh.  MODE jedit (browse_library_jedit.sh) wants Isabelle alone.
set -uo pipefail
EVAL="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$EVAL/setup/lib.sh"
mode=$1 exports=$2
if [[ "$mode" == jedit ]]; then want=isabelle   # browse_library_jedit.sh: Isabelle alone
else
  cols=$(for b in $(conf "$mode.benchmarks"); do conf "$mode.columns.$b"; done)
  want="mlton gmp gcc"
  # shellcheck disable=SC2086
  any_matches '^lemon' $cols && want="$want cmake"
  # shellcheck disable=SC2086
  any_matches '^jgrapht' $cols && want="$want jdk"
  # shellcheck disable=SC2086
  any_matches '^(scipy|networkx|ortools|sage)' $cols && want="$want python"
  [[ "$exports" == built ]] && want="$want isabelle"
fi

arch="$(uname -m)"
case "$arch" in    # x86_64 is the TACAS VM and the tested target; the aarch64 files are listed but untested
  x86_64)  triplet=x86_64-linux-gnu ;;
  aarch64) triplet=aarch64-linux-gnu ;;
  *) fail "unsupported architecture $arch (x86_64, or aarch64)" ;;
esac
dl="$WORK/downloads"; tc="$WORK/toolchains"
mkdir -p "$tc/bin"
say "== toolchains for $arch: $want (toolchains_dist/MANIFEST.txt)"
declare -A file=([mlton]= [gmp]= [gcc]= [cmake]= [jdk]= [python]= [isabelle]=)   # name -> its files under work/downloads (gcc: several Debian packages)
while read -r a name f m urls; do
  [[ -z "$a" || "$a" == \#* ]] && continue
  [[ "$a" == "$arch" ]] || continue
  has "$name" $want || continue
  file[$name]="${file[$name]:+${file[$name]} }$f"
  # shellcheck disable=SC2086
  fetch_file "$dl/$f" "$m" $urls || true
done < "$EVAL/toolchains_dist/MANIFEST.txt"

# deb_extract DEB DIR   unpacks a Debian package into DIR (dpkg-deb, or ar and tar)
deb_extract() {
  local deb=$1 dir=$2
  if command -v dpkg-deb >/dev/null 2>&1; then dpkg-deb -x "$deb" "$dir" >>"$LOG" 2>&1 || fail "dpkg-deb -x failed on $deb"
  else ( cd "$dir" && ar x "$deb" && tar -xf data.tar.* && rm -f debian-binary control.tar.* data.tar.* ) >>"$LOG" 2>&1 || fail "could not extract $deb (needs dpkg-deb, or ar and tar with zstd)"; fi
}
has mlton $want && { unpack "MLton 20241230" "$dl/${file[mlton]}" "$tc/mlton" || true; }
if has gmp $want && [[ -f "$dl/${file[gmp]}" && ! -f "$tc/gmp/.installed" ]]; then   # gmp.h and libgmp.a for MLton, linked statically
  rm -rf "$tc/gmp" "$tc/gmp.tmp"; mkdir -p "$tc/gmp/include" "$tc/gmp/lib" "$tc/gmp.tmp"
  deb_extract "$dl/${file[gmp]}" "$tc/gmp.tmp"
  cp "$tc/gmp.tmp/usr/include/$triplet/gmp.h" "$tc/gmp/include/" && cp "$tc/gmp.tmp/usr/lib/$triplet/libgmp.a" "$tc/gmp/lib/" || fail "gmp.h or libgmp.a not found in ${file[gmp]}"
  rm -rf "$tc/gmp.tmp"; touch "$tc/gmp/.installed"; say "   GMP 6.3.0 (headers and static library): unpacked"
elif [[ -f "$tc/gmp/.installed" ]]; then say "   GMP 6.3.0: already unpacked"; fi
# gcc and g++ 11.4.0 of Ubuntu 22.04, the compilers the published numbers were made with, relocated into work/toolchains/gcc
# (with their isl, mpc and mpfr); they use the VM's binutils and C library.  Wrappers gcc, g++, cc and c++ in work/toolchains/bin
# put them in front of the VM's compiler for every build, MLton's C compilation included.
if ! has gcc $want; then :
elif [[ -f "$tc/gcc/.installed" ]]; then say "   GCC 11.4.0: already unpacked"
else
  rm -rf "$tc/gcc"; mkdir -p "$tc/gcc"; missing=
  for f in ${file[gcc]}; do [[ -f "$dl/$f" ]] && deb_extract "$dl/$f" "$tc/gcc" || missing="$missing $f"; done
  if [[ -z "$missing" ]]; then
    for t in gcc cc g++ c++; do
      case $t in gcc|cc) real=gcc-11 ;; *) real=g++-11 ;; esac
      cat > "$tc/bin/$t" <<EOS
#!/bin/bash
# $t: GCC 11.4.0 of Ubuntu 22.04 (the paper's compiler), relocated to work/toolchains/gcc by setup/toolchains.sh.
here="\$(cd "\$(dirname "\${BASH_SOURCE[0]}")/.." && pwd)"
export LD_LIBRARY_PATH="\$here/gcc/usr/lib/$triplet\${LD_LIBRARY_PATH:+:\$LD_LIBRARY_PATH}"
exec "\$here/gcc/usr/bin/$real" "\$@"
EOS
      chmod +x "$tc/bin/$t"
    done
    touch "$tc/gcc/.installed"; say "   GCC 11.4.0 (gcc, g++): unpacked"
  else rm -rf "$tc/gcc"; say "   GCC 11.4.0: not available (missing:$missing, see above); the VM's own gcc and g++ are used"; fi
fi
has mlton $want && cat > "$tc/bin/mlton" <<EOS
#!/bin/bash
# MLton 20241230 with the evaluation's GMP headers and static library.
here="\$(cd "\$(dirname "\${BASH_SOURCE[0]}")/.." && pwd)"
exec "\$here/mlton/bin/mlton" -cc-opt "-I\$here/gmp/include" -link-opt "-L\$here/gmp/lib" "\$@"
EOS
[[ -f "$tc/bin/mlton" ]] && chmod +x "$tc/bin/mlton"
has cmake $want && { unpack "CMake 3.22.1" "$dl/${file[cmake]}" "$tc/cmake" || true; }
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
export PATH="$tc/bin:$tc/cmake/bin:$tc/jdk/bin:$tc/python/bin:\$PATH"
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
{ [[ -x "$tc/mlton/bin/mlton" ]] && "$MLTON" 2>&1 | head -1; has gcc $want && gcc --version | head -1; command -v cmake >/dev/null && cmake --version | head -1
  [[ -x "$JAVA_HOME/bin/java" ]] && "$JAVA_HOME/bin/java" -version 2>&1 | head -1
  [[ -x "$PYTHON" ]] && "$PYTHON" --version; [[ -x "$ISABELLE" ]] && "$ISABELLE" version; true; } 2>&1 | sed 's/^/   /' | tee -a "$LOG"
