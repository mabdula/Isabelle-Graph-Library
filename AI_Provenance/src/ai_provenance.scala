/*  Title:      AI_Provenance/src/ai_provenance.scala

Count the commands and lines of theories by provenance label, from the theory sources.
*/

package isabelle.ai_provenance

import isabelle._

import scala.collection.mutable


object AI_Provenance {
  /* labels */

  val kinds: List[String] = List("human", "ai_human", "ai")
  val unmarked = "unmarked"
  val labels: List[String] = kinds ::: List(unmarked)

  val command_name = "provenance"

  private def check_kind(where: String, args: List[String]): String =
    args match {
      case List(kind) if kinds.contains(kind) => kind
      case _ =>
        error("Bad provenance label " + quote(args.mkString(" ")) + where +
          "; expected one of " + commas_quote(kinds))
    }


  /* markers: \<^marker>\<open>provenance kind\<close>, possibly among other markers */

  private def marker_items(source: String): List[String] = {
    val items = new mutable.ListBuffer[String]
    val item = new StringBuilder
    var depth = 0
    for (sym <- Symbol.iterator(source)) {
      if (Symbol.is_open(sym)) { if (depth > 0) item ++= sym; depth += 1 }
      else if (Symbol.is_close(sym)) { depth -= 1; if (depth > 0) item ++= sym }
      else if (depth == 1 && sym == ",") { items += item.toString.trim; item.clear() }
      else if (depth > 0) item ++= sym
    }
    items += item.toString.trim
    items.toList
  }

  private def marker_kind(where: String, tok: Token): Option[String] =
    if (!tok.is_marker) None
    else {
      marker_items(tok.source).map(_.split("\\s+").toList.filter(_.nonEmpty)).collect(
        { case `command_name` :: args => check_kind(where, args) }).lastOption
    }


  /* proof structure: nesting depth after a command, from its keyword kind */

  private def depth_after(keyword_kind: Option[String], depth: Int): Int =
    keyword_kind match {
      case Some(kind) if Keyword.theory_goal(kind) || Keyword.proof_goal(kind) => depth + 1
      case Some(Keyword.PRF_BLOCK) | Some(Keyword.PRF_OPEN) => depth + 1
      case Some(Keyword.QED) | Some(Keyword.QED_SCRIPT) | Some(Keyword.PRF_CLOSE) =>
        (depth - 1) max 0
      case Some(Keyword.QED_BLOCK) => (depth - 2) max 0
      case Some(Keyword.QED_GLOBAL) => 0
      case _ => depth
    }


  /* commands of a theory, with their labels */

  sealed case class Command(
    theory: String,
    line: Int,
    name: String,
    label: String,
    lines: Int,
    is_header: Boolean
  )

  def theory_commands(
    syntax: Outer_Syntax,
    theory: String,
    text: String,
    warning: String => Unit = _ => ()
  ): List[Command] = {
    val spans = syntax.parse_spans(text).toVector

    /* a line belongs to the command in which its first visible symbol occurs */

    val start_line = new Array[Int](spans.length)
    val line_count = new Array[Int](spans.length)
    val owned = mutable.Set.empty[Int]
    var line = 1
    for ((span, i) <- spans.iterator.zipWithIndex) {
      val counted = span.kind.isInstanceOf[Command_Span.Command_Span]
      for (tok <- span.content) {
        if (tok.is_command && start_line(i) == 0) start_line(i) = line
        val parts = tok.source.split("\n", -1)
        if (counted && !tok.is_space) {
          for ((part, j) <- parts.iterator.zipWithIndex if part.exists(!_.isWhitespace)) {
            if (!owned(line + j)) { owned += (line + j); line_count(i) += 1 }
          }
        }
        line += parts.length - 1
      }
    }

    /* labels: switch, markers, and scopes of markers in proofs */

    val result = new mutable.ListBuffer[Command]
    var depth = 0
    var switch: Option[String] = None
    var scopes: List[(Int, Option[String])] = Nil
    var header = true

    for ((span, i) <- spans.iterator.zipWithIndex) {
      def where: String = " (line " + start_line(i) + " of theory " + quote(theory) + ")"
      span.kind match {
        case Command_Span.Command_Span(keyword_kind, name, _) =>
          if (name == command_name) {
            val args =
              span.content.dropWhile(tok => !tok.is_command).drop(1)
                .filterNot(tok => tok.is_ignored || tok.is_marker).map(_.content)
            switch = Some(check_kind(where, args))
          }
          if (depth > 0 && keyword_kind.exists(Keyword.theory)) {
            warning("Proof structure not recognised before command " + quote(name) + where)
            depth = 0
          }
          val depth0 = depth
          val depth1 = depth_after(keyword_kind, depth0)
          val scopes0 = scopes.filter({ case (level, _) => level <= depth0 })
          val marker = span.content.flatMap(marker_kind(where, _)).lastOption
          val label =
            marker orElse (scopes0 match { case (_, kind) :: _ => kind case Nil => switch })
          scopes =
            if (depth1 > depth0 || marker.isDefined && name == "apply" && depth1 > 0) {
              (depth1, label) :: scopes0
            }
            else scopes0
          depth = depth1
          result += Command(theory, start_line(i), name, label getOrElse unmarked, line_count(i), header)
          if (name == Thy_Header.THEORY) header = false
        case Command_Span.Malformed_Span =>
          error("Malformed command span" + where)
        case _ =>
      }
    }
    result.toList
  }


  /* statistics */

  sealed case class Count(commands: Int = 0, lines: Int = 0) {
    def + (command: Command): Count = Count(commands + 1, lines + command.lines)
  }

  def count(commands: List[Command]): Map[String, Count] =
    commands.filterNot(_.is_header).foldLeft(Map.empty[String, Count]) {
      case (m, command) => m + (command.label -> (m.getOrElse(command.label, Count()) + command))
    }

  def print_count(title: String, counts: Map[String, Count]): String = {
    val total_lines = counts.valuesIterator.map(_.lines).sum
    def percent(n: Int): String =
      if (total_lines == 0) "" else String.format(java.util.Locale.ROOT, "%5.1f%%", n * 100.0 / total_lines)
    val rows =
      for (label <- labels; c = counts.getOrElse(label, Count()) if c.commands > 0 || label != unmarked)
      yield {
        String.format(java.util.Locale.ROOT, "  %-9s %8d lines %s %8d commands",
          label, c.lines, percent(c.lines), c.commands)
      }
    (title :: rows).mkString("\n")
  }


  /* main */

  def ai_provenance(
    options: Options,
    sessions: List[String],
    dirs: List[Path] = Nil,
    select_dirs: List[Path] = Nil,
    output: Option[Path] = None,
    per_theory: Boolean = false,
    strict: Boolean = false,
    progress: Progress = new Progress
  ): Unit = {
    val structure = Sessions.load_structure(options, dirs = dirs, select_dirs = select_dirs)
    val selection = Sessions.Selection(sessions = sessions)
    val selected = structure.build_selection(selection)
    val deps = Sessions.deps(structure.selection(selection), progress = progress)

    /* the theories of a session include those that only other sessions load */

    val theories: Map[String, List[(Document.Node.Name, Outer_Syntax)]] =
      (for {
        session <- selected
        base = deps(session)
        (name, _) <- base.used_theories
        if selected.contains(deps.sessions_structure.theory_qualifier(name))
      } yield (name, base.theory_syntax(name)))
        .distinctBy({ case (name, _) => name.theory })
        .groupBy({ case (name, _) => deps.sessions_structure.theory_qualifier(name) })

    val all_commands =
      for (session <- selected) yield {
        val commands =
          for ((name, syntax) <- theories.getOrElse(session, Nil).sortBy(_._1.theory)) yield {
            val commands =
              theory_commands(syntax, name.theory, File.read(name.path),
                warning = msg => progress.echo_warning(msg))
            if (per_theory) progress.echo(print_count("Theory " + name.theory + ":", count(commands)))
            commands
          }
        progress.echo(print_count("Session " + session + ":", count(commands.flatten)))
        session -> commands.flatten
      }

    if (selected.length > 1) {
      progress.echo(print_count("Total:", count(all_commands.flatMap(_._2))))
    }

    for (path <- output) {
      val header = List("session", "theory", "line", "command", "label", "lines")
      val rows =
        for ((session, commands) <- all_commands; c <- commands)
          yield List(session, c.theory, c.line.toString, c.name, c.label, c.lines.toString)
      File.write(path, (header :: rows).map(_.mkString("\t")).mkString("", "\n", "\n"))
      progress.echo("Written " + path.expand)
    }

    if (strict) {
      val unmarked_commands =
        all_commands.flatMap(_._2).filter(c => !c.is_header && c.label == unmarked)
      if (unmarked_commands.nonEmpty) {
        error(cat_lines(
          "Unmarked commands:" ::
            unmarked_commands.take(20).map(c =>
              "  " + c.theory + " line " + c.line + ": " + c.name) :::
            (if (unmarked_commands.length > 20) List("  ...") else Nil)))
      }
    }
  }


  /* Isabelle tool wrapper */

  val isabelle_tool =
    Isabelle_Tool("ai_provenance", "count commands and lines by provenance label",
      Scala_Project.here, { args =>
        var select_dirs: List[Path] = Nil
        var dirs: List[Path] = Nil
        var output: Option[Path] = None
        var options = Options.init()
        var strict = false
        var per_theory = false

        val getopts = Getopts("""
Usage: isabelle ai_provenance [OPTIONS] [SESSIONS ...]

  Options are:
    -D DIR       include session directory and select its sessions
    -d DIR       include session directory
    -o FILE      write a table of all commands with their labels (TSV)
    -s           strict: fail if a command other than the theory header
                 is unmarked
    -t           print the counts of every theory

  Count the commands and lines of the theories of the given sessions by
  provenance label (human, ai_human, ai, or unmarked), from the theory
  sources. A line belongs to the command in which its first visible symbol
  occurs; theory headers, and commands before them, are not counted.
""",
          "D:" -> (arg => select_dirs = select_dirs ::: List(Path.explode(arg))),
          "d:" -> (arg => dirs = dirs ::: List(Path.explode(arg))),
          "o:" -> (arg => output = Some(Path.explode(arg))),
          "s" -> (_ => strict = true),
          "t" -> (_ => per_theory = true))

        val sessions = getopts(args)
        if (sessions.isEmpty && select_dirs.isEmpty) getopts.usage()

        val progress = new Console_Progress()

        ai_provenance(options, sessions, dirs = dirs, select_dirs = select_dirs,
          output = output, per_theory = per_theory, strict = strict, progress = progress)
      })
}

class Tools extends Isabelle_Scala_Tools(AI_Provenance.isabelle_tool)
