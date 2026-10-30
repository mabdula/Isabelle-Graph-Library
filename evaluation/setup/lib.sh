# lib.sh -- helpers shared by the setup scripts.  Sourced, never run.
# Expects EVAL (the evaluation directory); sets WORK, LOG (if unset) and NA.
EVAL="${EVAL:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
WORK="${WORK:-$EVAL/work}"
LOG="${LOG:-$WORK/setup.log}"
NA="$EVAL/NOT_AVAILABLE.txt"
mkdir -p "$WORK/downloads"

say()  { echo "$*" | tee -a "$LOG"; }
fail() { say "ERROR: $*"; say "see $LOG"; exit 1; }
need() { command -v "$1" >/dev/null 2>&1 || fail "'$1' is not installed; on the TACAS VM: sudo apt-get install $2"; }
sum()  { md5sum "$1" | cut -c1-32; }

# conf KEY            the values of KEY in modes.conf (empty when the key is absent)
conf() { sed -n -E "s/^[[:space:]]*$1[[:space:]]*=[[:space:]]*//p" "$EVAL/modes.conf" | head -1; }
# has WORD LIST...    is WORD one of the LIST?
has() { local w=$1; shift; local x; for x in "$@"; do [[ "$x" == "$w" ]] && return 0; done; return 1; }
# any_matches REGEX LIST...   does a word of the LIST match REGEX?
any_matches() { local re=$1; shift; local x; for x in "$@"; do [[ "$x" =~ $re ]] && return 0; done; return 1; }

# agent URL   the User-Agent to download URL with: coral.ise.lehigh.edu refuses curl's own, foss.heptapod.net answers a
# browser's with a challenge page
agent() { case $1 in *heptapod.net*) echo "IsaGraphLib-evaluation/1.0" ;; *) echo "Mozilla/5.0 (IsaGraphLib evaluation)" ;; esac; }

# fetch_file DEST MD5 URL...   download from the first source that delivers the md5 (MD5 "-" means
# unchecked), unless DEST already has it.  A total failure prints every source, the md5 and the path to put
# the file at, records it in NOT_AVAILABLE.txt and returns 1; the caller goes on without the file.
fetch_file() {
  local dest=$1 md5=$2 url; shift 2
  if [[ -f "$dest" && ( "$md5" == - || "$(sum "$dest")" == "$md5" ) ]]; then say "   have   $(basename "$dest")"; return 0; fi
  command -v curl >/dev/null 2>&1 || command -v wget >/dev/null 2>&1 || fail "neither curl nor wget is installed"
  mkdir -p "$(dirname "$dest")"
  for url in "$@"; do
    say "   fetch  $(basename "$dest")  <-  $url"
    rm -f "$dest.part"
    if command -v curl >/dev/null 2>&1; then curl -fsSL -A "$(agent "$url")" --connect-timeout 30 --retry 3 --speed-limit 1024 --speed-time 60 --max-time 7200 -o "$dest.part" "$url" >>"$LOG" 2>&1
    else wget -q -U "$(agent "$url")" --timeout=60 --tries=3 -O "$dest.part" "$url" >>"$LOG" 2>&1; fi
    if [[ -s "$dest.part" && ( "$md5" == - || "$(sum "$dest.part")" == "$md5" ) ]]; then mv "$dest.part" "$dest"; return 0; fi
    [[ -s "$dest.part" ]] && say "          (md5 $(sum "$dest.part") instead of $md5, trying the next source)" || say "          (not delivered, trying the next source)"
    rm -f "$dest.part"
  done
  say ""; say "NOTE:  $(basename "$dest") could not be downloaded.  Fetch it by hand from one of"
  for url in "$@"; do say "         $url"; done
  say "       (md5 $md5), put it at"; say "         $dest"; say "       and run the setup again; what is built with it is left out until then."; say ""
  echo "$(basename "$dest") (md5 $md5) not downloaded; put it at $dest and run the setup again; sources: $*" >> "$NA"
  return 1
}

# unpack NAME ARCHIVE DESTDIR [STRIP]   tar xzf into DESTDIR (skipped when DESTDIR/.installed exists)
unpack() {
  local name=$1 ar=$2 dest=$3 strip=${4:-1}
  if [[ -f "$dest/.installed" ]]; then say "   $name: already unpacked"; return 0; fi
  if [[ ! -f "$ar" ]]; then say "   $name: not available (see above); what needs it is left out"; return 1; fi
  rm -rf "$dest"; mkdir -p "$dest"
  tar xzf "$ar" -C "$dest" --strip-components="$strip" >>"$LOG" 2>&1 || fail "could not unpack $ar"
  touch "$dest/.installed"; say "   $name: unpacked"
}

# try_fetch DEST MD5 URL   one quiet attempt (no NOTE, nothing recorded); returns 1 when it did not deliver
try_fetch() {
  local dest=$1 md5=$2 url=$3
  if [[ -f "$dest" && ( "$md5" == - || "$(sum "$dest")" == "$md5" ) ]]; then return 0; fi
  mkdir -p "$(dirname "$dest")"; rm -f "$dest.part"
  if command -v curl >/dev/null 2>&1; then curl -fsSL -A "$(agent "$url")" --connect-timeout 30 --retry 2 --speed-limit 1024 --speed-time 60 --max-time 3600 -o "$dest.part" "$url" >>"$LOG" 2>&1
  else wget -q -U "$(agent "$url")" --timeout=60 --tries=2 -O "$dest.part" "$url" >>"$LOG" 2>&1; fi
  if [[ -s "$dest.part" && ( "$md5" == - || "$(sum "$dest.part")" == "$md5" ) ]]; then mv "$dest.part" "$dest"; return 0; fi
  rm -f "$dest.part"; return 1
}
