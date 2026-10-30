package flow.review

enum Kind:
  case Claim, Assumption, Design

  def label: String = toString.toLowerCase

/** A statement, as the code states it.
  *
  * @param on      the definitions it is written on: the predicate of a claim, the code an assumption or design is about
  * @param hash    over its kind, text, and every definition it transitively refers to, so that any change to what it
  *                means changes the hash
  * @param sources the source of each of those definitions, to show what changed
  */
final case class Statement(
    name: String,
    kind: Kind,
    text: String,
    on: List[String],
    hash: String,
    sources: Map[String, String]
)

/** A definition with a contract: a lemma, proven code, or `@extern` code whose contract is trusted.
  *
  * @param proves   claims in its postcondition
  * @param requires claims in its precondition
  * @param calls    definitions with contracts it calls: it relies on what they prove, and proves what they require
  * @param assumes  assumptions on code it uses
  */
final case class Proof(
    name: String,
    file: String,
    line: Int,
    tested: Boolean,
    proves: Set[String],
    requires: Set[String],
    calls: Set[String],
    assumes: Set[String]
):
  def simpleName: String = name.split('.').last
  def where: String = s"${file.split('/').last}:$line"

final case class Model(statements: List[Statement], proofs: List[Proof]):
  val byName: Map[String, Statement] = statements.map(s => s.name -> s).toMap
  private val proofByName = proofs.map(p => p.name -> p).toMap

  /** Proofs of a claim; one that only passes on what a definition it calls proves is not one. */
  def provedBy(claim: String): List[Proof] =
    proofs.filter(p => p.proves(claim) && !p.calls.exists(c => proofByName.get(c).exists(_.proves(claim))))

  /** Proofs that call a definition requiring `claim`: Stainless proves it there, as a precondition. */
  def dischargedBy(claim: String): List[Proof] =
    proofs.filter(p => p.calls.exists(c => proofByName.get(c).exists(_.requires(claim))))

  /** Every statement the proofs of a statement start from. */
  private def support(name: String): Set[String] =
    provedBy(name)
      .flatMap(p => p.requires ++ p.calls.flatMap(proofByName.get).flatMap(_.proves) ++ p.assumes)
      .toSet
      .filter(s => s != name && byName.contains(s))

  private def below(name: String): Set[String] =
    val seen = collection.mutable.Set.empty[String]
    def visit(s: String): Unit = support(s).foreach(t => if seen.add(t) then visit(t))
    visit(name)
    seen.toSet

  /** What a statement rests on directly: its support, less what the rest of its support already rests on. */
  def restsOn(name: String): List[String] =
    val all = support(name)
    all.filterNot(s => (all - s).exists(o => below(o)(s))).toList.sortBy(order)

  /** Statements nothing rests on: the purpose. */
  def roots: List[String] =
    val below = statements.flatMap(s => restsOn(s.name)).toSet
    statements.map(_.name).filterNot(below).sortBy(order)

  private def order(name: String): (Int, Int) =
    (byName.get(name).map(_.kind.ordinal).getOrElse(9), statements.indexWhere(_.name == name))
