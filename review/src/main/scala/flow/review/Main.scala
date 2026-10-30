package flow.review

import java.nio.file.{Files, Path}
import java.time.Instant
import java.time.temporal.ChronoUnit
import scala.jdk.CollectionConverters.*

/** The statements of a Stainless Flow project, read from its TASTy, and the developer's signed decisions on them.
  *
  * {{{
  * tree                         the statements from the roots down, with what each rests on
  * status                       every statement and its state; exits 1 while anything waits for a decision
  * show NAME                    one statement: what it says, its proofs, what it rests on, its code
  * review                       the statements waiting for a decision, each with what changed
  * accept NAME... | --all       sign a decision to accept (with --as WHO and optionally --key PATH)
  * reject NAME...               sign a decision to reject
  * }}}
  */
object Main:
  enum State:
    case Accepted(d: Decision)
    case Changed(d: Decision)
    case Rejected(d: Decision)
    case Forged(d: Decision)
    case New

    def settled: Boolean = this.isInstanceOf[Accepted]

  final class Project(val title: String, val model: Model, val root: Path):
    val ledgerFile     = root.resolve(".flow/ledger.json")
    val allowedSigners = root.resolve(".flow/allowed_signers")
    var ledger         = Ledger.load(ledgerFile)
    val verified       = Verification.load(root.resolve("target/streams/compile/compile/_global/streams/out"))

    def state(s: Statement): State = ledger.latest(s.name) match
      case None                                                                         => State.New
      case Some(d) if !Signing.verify(d.payload, d.signature, d.by, allowedSigners)    => State.Forged(d)
      case Some(d) if d.decision != "accepted"                                         => State.Rejected(d)
      case Some(d) if d.hash != s.hash                                                 => State.Changed(d)
      case Some(d)                                                                     => State.Accepted(d)

    private val proofByName = model.proofs.map(p => p.name -> p).toMap

    /** A proof holds when its own verification conditions do, and those of every proof it calls. */
    def proofState(p: Proof, seen: Set[String] = Set.empty): String =
      if p.tested then "tested"
      else
        val own = verified.get((p.file.split('/').last, p.simpleName))
        val failing = p.calls.toList.filterNot(seen).flatMap(proofByName.get)
          .filter(q => !q.tested && proofState(q, seen + p.name) != "proven")
        own match
          case None                         => "not verified yet (run sbt verify)"
          case Some(false)                  => "NOT PROVEN"
          case Some(true) if failing.nonEmpty => s"NOT PROVEN (through ${failing.map(_.simpleName).mkString(", ")})"
          case Some(true)                   => "proven"

    /** How a statement is established, and whether that holds up. */
    def established(s: Statement): (Boolean, String) = s.kind match
      case Kind.Assumption => (true, "assumed")
      case Kind.Design     => (true, "decided")
      case Kind.Claim =>
        val by   = model.provedBy(s.name)
        val at   = model.dischargedBy(s.name)
        val bad  = (by ++ at).filterNot(p => p.tested || proofState(p) == "proven")
        val how  =
          if by.nonEmpty then
            val kinds = by.map(p => if p.tested && !by.forall(_.tested) then s"${p.simpleName} (tested)" else p.simpleName).distinct
            s"${if by.forall(_.tested) then "tested" else "proven"} by ${kinds.mkString(", ")}"
          else if at.nonEmpty then s"proven where used: ${at.map(_.simpleName).distinct.mkString(", ")}"
          else "not proven"
        (bad.isEmpty && (by.nonEmpty || at.nonEmpty), if bad.nonEmpty then s"$how (${bad.map(_.simpleName).mkString(", ")} not proven)" else how)

    def mark(s: Statement): String =
      val (ok, _) = established(s)
      state(s) match
        case _ if !ok                                        => "x"
        case State.Accepted(_) if s.kind == Kind.Claim       => "+"
        case State.Accepted(_)                               => "-"
        case _                                               => "!"

    def describe(st: State): String = st match
      case State.Accepted(d) => s"accepted (${d.by}, ${d.at})"
      case State.Changed(d)  => s"changed since accepted (${d.by}, ${d.at}): review it"
      case State.Rejected(d) => s"rejected (${d.by}, ${d.at})"
      case State.Forged(d)   => s"decision by ${d.by} has no valid signature: review it"
      case State.New         => "new: review it"

  def main(args: Array[String]): Unit =
    val (opts, command) = args.toList.span(_ != "--")
    def opt(name: String) = opts.sliding(2).collectFirst { case List(`name`, v) => v }
      .getOrElse(sys.error(s"missing $name"))

    val root    = Path.of(opt("--root"))
    val tasty   = Files.walk(Path.of(opt("--classes"))).iterator.asScala.filter(_.toString.endsWith(".tasty")).toList
    val classpath = Files.readString(Path.of(opt("--classpath-file"))).trim.split(java.io.File.pathSeparator).toList
    val sources   = opt("--sources").split(java.io.File.pathSeparator).map(Path.of(_).toAbsolutePath.normalize).toList
    def ours(file: String) = sources.exists(root.resolve(file).toAbsolutePath.normalize.startsWith(_))
    val model   = Extract(tasty.map(_.toString), classpath, ours)
    val project = Project(opt("--title"), model, root)

    command.drop(1) match
      case List("tree")                => tree(project)
      case Nil | List("status")        => sys.exit(status(project))
      case List("show", name)          => show(project, name)
      case List("review")              => sys.exit(review(project))
      case "accept" :: rest            => decide(project, "accepted", rest)
      case "reject" :: rest            => decide(project, "rejected", rest)
      case other                       => sys.error(s"unknown command: ${other.mkString(" ")}")

  private def status(p: Project): Int =
    val width = p.model.statements.map(_.name.length).max
    for s <- p.model.statements do
      val (_, how) = p.established(s)
      println(f"${p.mark(s)} ${s.name.padTo(width, ' ')}  ${s.kind.label.padTo(10, ' ')}  $how; ${p.describe(p.state(s))}")
    val settled = p.model.statements.count(s => p.state(s).settled && p.established(s)._1)
    println(s"\n${p.title}: ${p.model.statements.size} statements, $settled accepted and holding")
    if settled == p.model.statements.size then 0 else 1

  private def tree(p: Project): Unit =
    val shown = collection.mutable.Set.empty[String]
    def node(name: String, depth: Int, path: Set[String]): Unit =
      val s      = p.model.byName(name)
      val indent = "    " * depth
      val again  = shown(name)
      println(s"$indent${p.mark(s)} ${s.name}  ${s.kind.label}, ${p.established(s)._2}${if again then "  (above)" else ""}")
      if !again then
        shown += name
        println(s"$indent    ${s.text}")
        for child <- p.model.restsOn(name) if !path(child) do node(child, depth + 1, path + child)
    p.model.roots.foreach(r => node(r, 0, Set(r)))

  private def show(p: Project, name: String): Unit =
    val s = p.model.byName.getOrElse(name, sys.error(s"no statement named $name"))
    println(s"${s.name}  ${s.kind.label}  ${p.describe(p.state(s))}")
    println(s"  ${s.text}\n")
    println(s"  ${p.established(s)._2}")
    for proof <- p.model.provedBy(name) do println(s"    ${proof.simpleName} (${proof.where}): ${p.proofState(proof)}")
    for proof <- p.model.dischargedBy(name) do println(s"    where ${proof.simpleName} (${proof.where}) uses it: ${p.proofState(proof)}")
    val rests = p.model.restsOn(name)
    if rests.nonEmpty then println(s"\n  rests on: ${rests.mkString(", ")}")
    val above = p.model.statements.filter(o => p.model.restsOn(o.name).contains(name)).map(_.name)
    if above.nonEmpty then println(s"  serves: ${above.mkString(", ")}")
    for on <- s.on do println(s"\n  $on\n${indented(s.sources(on), "    ")}")

  private def review(p: Project): Int =
    val waiting = p.model.statements.filterNot(s => p.state(s).settled)
    for s <- waiting do
      println(s"${p.mark(s)} ${s.name}  ${s.kind.label}  ${p.describe(p.state(s))}")
      println(s"  ${s.text}")
      p.state(s) match
        case State.Changed(d) =>
          println(s"\nWhat changed since it was accepted (${d.by}, ${d.at})")
          if d.text != s.text then println(s"  text\n    - ${d.text}\n    + ${s.text}")
          val names     = (d.sources.keySet ++ s.sources.keySet).toList.sorted
          val unchanged = names.count(n => d.sources.get(n) == s.sources.get(n))
          for n <- names if d.sources.get(n) != s.sources.get(n) do
            println(s"  $n")
            Diff.lines(d.sources.getOrElse(n, ""), s.sources.getOrElse(n, "")).filterNot(_.startsWith("  ")) match
              case Nil   => println("    (same source, different meaning: something it refers to changed)")
              case lines => lines.foreach(l => println(s"    $l"))
          if unchanged > 0 then println(s"  ... $unchanged unchanged definition(s)")
        case _ =>
          for on <- s.on do println(s"\n  $on\n${indented(s.sources(on), "    ")}")
      println()
    if waiting.isEmpty then println(s"${p.title}: nothing waits for a decision")
    else println(s"${waiting.size} statement(s) wait for a decision: accept NAME... --as WHO, or reject NAME... --as WHO")
    if waiting.isEmpty then 0 else 1

  private def decide(p: Project, decision: String, args: List[String]): Unit =
    def parse(rest: List[String], flags: Map[String, String], names: List[String]): (Map[String, String], List[String]) =
      rest match
        case "--all" :: tail                        => parse(tail, flags + ("--all" -> ""), names)
        case flag :: value :: tail if flag.startsWith("--") => parse(tail, flags + (flag -> value), names)
        case name :: tail                           => parse(tail, flags, names :+ name)
        case Nil                                    => (flags, names)
    val (flags, names) = parse(args, Map.empty, Nil)
    val by  = flags.getOrElse("--as", sys.error("say who decides: --as NAME (a principal in .flow/allowed_signers)"))
    val key = flags.get("--key").orElse(sys.env.get("FLOW_SIGNING_KEY")).map(Path.of(_))
      .getOrElse(Path.of(sys.props("user.home"), ".ssh", "id_ed25519"))
    val targets =
      if flags.contains("--all") then p.model.statements.filterNot(s => p.state(s).settled)
      else names.map(n => p.model.byName.getOrElse(n, sys.error(s"no statement named $n")))
    for s <- targets do
      val at = Instant.now.truncatedTo(ChronoUnit.SECONDS).toString
      val signature = Signing.sign(Signing.payload(s.name, s.hash, decision, by, at), key)
      val d = Decision(s.name, s.kind.label, s.text, s.hash, decision, by, at, s.sources, signature)
      if !Signing.verify(d.payload, d.signature, by, p.allowedSigners) then
        sys.error(s"$by's signature does not verify against ${p.allowedSigners}: add their key there first")
      p.ledger = p.ledger + d
      println(s"$decision ${s.name} as $by")
    Ledger.save(p.ledgerFile, p.ledger)

  private def indented(text: String, prefix: String): String = text.linesIterator.map(prefix + _).mkString("\n")
