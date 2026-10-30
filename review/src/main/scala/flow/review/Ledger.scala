package flow.review

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import upickle.default.*

/** A developer's decision on a statement, signed with their SSH key. It covers the statement as it was when decided:
  * its hash, and the sources behind it, kept to show what changed since.
  */
final case class Decision(
    statement: String,
    kind: String,
    text: String,
    hash: String,
    decision: String,
    by: String,
    at: String,
    sources: Map[String, String],
    signature: String
) derives ReadWriter:
  def payload: String = Signing.payload(statement, hash, decision, by, at)

final case class Ledger(decisions: List[Decision]) derives ReadWriter:
  def latest(statement: String): Option[Decision] = decisions.findLast(_.statement == statement)
  def +(d: Decision): Ledger = Ledger(decisions.filterNot(_.statement == d.statement) :+ d)

object Ledger:
  def load(file: Path): Ledger =
    if Files.exists(file) then read[Ledger](Files.readString(file)) else Ledger(Nil)

  def save(file: Path, ledger: Ledger): Unit =
    Files.createDirectories(file.getParent)
    Files.writeString(file, write(ledger, indent = 2) + "\n")

/** Decisions are signed and checked with `ssh-keygen -Y`, against the keys in `.flow/allowed_signers`. */
object Signing:
  val namespace = "stainless-flow"

  private def run(builder: ProcessBuilder): Int =
    try builder.start().waitFor()
    catch case e: java.io.IOException => sys.error(s"flow signs and checks decisions with ssh-keygen (OpenSSH), which is not on the PATH: ${e.getMessage}")

  def payload(statement: String, hash: String, decision: String, by: String, at: String): String =
    s"stainless-flow decision\nstatement: $statement\nhash: $hash\ndecision: $decision\nby: $by\nat: $at\n"

  def sign(payload: String, key: Path): String =
    val file = Files.createTempFile("decision", ".txt")
    Files.writeString(file, payload)
    val sig = Path.of(file.toString + ".sig")
    try
      val exit = run(ProcessBuilder("ssh-keygen", "-Y", "sign", "-q", "-f", key.toString, "-n", namespace, file.toString)
        .inheritIO())
      if exit != 0 then sys.error(s"ssh-keygen could not sign with $key")
      Files.readString(sig)
    finally
      Files.deleteIfExists(file)
      Files.deleteIfExists(sig): Unit

  def verify(payload: String, signature: String, by: String, allowedSigners: Path): Boolean =
    Files.exists(allowedSigners) && {
      val data = Files.createTempFile("decision", ".txt")
      val sig  = Files.createTempFile("decision", ".sig")
      Files.writeString(data, payload)
      Files.writeString(sig, signature)
      try
        run(ProcessBuilder("ssh-keygen", "-Y", "verify", "-f", allowedSigners.toString, "-I", by, "-n", namespace,
          "-s", sig.toString)
          .redirectInput(data.toFile)
          .redirectOutput(ProcessBuilder.Redirect.DISCARD)
          .redirectError(ProcessBuilder.Redirect.DISCARD)) == 0
      finally
        Files.deleteIfExists(data)
        Files.deleteIfExists(sig): Unit
    }

/** What the last `sbt verify` (or `compile`) reported, per definition: whether all its verification conditions held. */
object Verification:
  def load(log: Path): Map[(String, String), Boolean] =
    if !Files.exists(log) then Map.empty
    else
      val rows = Files.readAllLines(log).asScala.map(_.replaceAll("\u001b\\[[0-9;]*m", "")).flatMap { line =>
        line.split("║") match
          case Array(_, row, _*) =>
            row.trim.split("\\s{2,}").toList match
              case loc :: fn :: _ :: status :: _ if loc.endsWith(":") && loc.contains(".scala:") =>
                val file = loc.takeWhile(_ != ':').split('/').last
                Some((file, fn) -> (status.startsWith("valid") || status == "trivial"))
              case _ => None
          case _ => None
      }
      rows.groupMapReduce(_._1)(_._2)(_ && _)

/** A line diff, enough to show what changed in a definition. */
object Diff:
  def lines(before: String, after: String): List[String] =
    val a = before.linesIterator.toVector
    val b = after.linesIterator.toVector
    val lcs = Array.ofDim[Int](a.size + 1, b.size + 1)
    for i <- a.indices.reverse; j <- b.indices.reverse do
      lcs(i)(j) = if a(i) == b(j) then lcs(i + 1)(j + 1) + 1 else lcs(i + 1)(j).max(lcs(i)(j + 1))
    val out = List.newBuilder[String]
    var i = 0
    var j = 0
    while i < a.size || j < b.size do
      if i < a.size && j < b.size && a(i) == b(j) then
        out += s"  ${a(i)}"
        i += 1
        j += 1
      else if i < a.size && (j == b.size || lcs(i + 1)(j) >= lcs(i)(j + 1)) then
        out += s"- ${a(i)}"
        i += 1
      else
        out += s"+ ${b(j)}"
        j += 1
    out.result()
