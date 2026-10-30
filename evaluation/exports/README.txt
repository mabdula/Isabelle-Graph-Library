The verified code exports the evaluation measures, SML only (the paper's Scala and Go columns are not part of
this evaluation), one directory per benchmark; setup/export_files.txt lists every file.

campaign/      the exports the paper's numbers were measured with (--old-generated-code)
pregenerated/  the exports generated from the current library and shipped (the smoke test's default; the AFP
               push-relabel export is only supplied this way); kruskal has none: the library has no Kruskal
               export theory yet, so its campaign export is used in every mode
built/         not shipped: setup/isabelle.sh generates the exports with Isabelle (the default of the 8h and
               full modes) and setup/exports.sh collects them into work/exports/current

Each directory holds MD5SUM.txt (md5sum -c checks it).  setup/exports.sh copies the selected set to
work/exports/current/<benchmark>/, where every Makefile reads it, and records the origin of each file in
work/exports/current/SOURCE.txt.
