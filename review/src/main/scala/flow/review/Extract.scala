package flow.review

import java.security.MessageDigest
import scala.collection.mutable
import scala.quoted.*
import scala.tasty.inspector.*

/** Reads the statements and proofs out of the TASTy files of the verified code.
  *
  * Stainless erases contracts and ghost code from the bytecode, but only after the compiler has written TASTy, so the
  * TASTy still holds every `require`, `ensuring`, ghost block and lemma call, and every `@claim`, `@assumption` and
  * `@design` annotation.
  */
object Extract:
  /** @param ours whether a source file is the project's own (the Stainless library is compiled alongside it) */
  def apply(tastyFiles: List[String], classpath: List[String], ours: String => Boolean): Model =
    var model: Option[Model] = None
    val inspector = new Inspector:
      def inspect(using Quotes)(tastys: List[Tasty[quotes.type]]): Unit =
        model = Some(read(tastys.map(_.ast).filter(t => ours(t.pos.sourceFile.path))))
    TastyInspector.inspectAllTastyFiles(tastyFiles, Nil, classpath)(inspector)
    model.getOrElse(sys.error("could not read the TASTy files"))

  private def read(using q: Quotes)(trees: List[q.reflect.Tree]): Model =
    import q.reflect.*
    import flow.review.{Statement as FlowStatement}

    // Every definition in the inspected files, by symbol.
    val defs = mutable.LinkedHashMap.empty[Symbol, Tree]
    object collect extends TreeTraverser:
      override def traverseTree(tree: Tree)(owner: Symbol): Unit =
        tree match
          case d: DefDef                                => defs(d.symbol) = d
          case c: ClassDef                              => defs(c.symbol) = c
          case v: ValDef if v.symbol.exists && v.symbol.owner.isClassDef => defs(v.symbol) = v
          case _                                        =>
        super.traverseTree(tree)(owner)
    trees.foreach(collect.traverseTree(_)(defn.RootClass))

    def flowAnnotations(sym: Symbol): List[(String, List[String])] =
      sym.annotations.collect {
        case Apply(Select(New(tpt), _), args) if tpt.tpe.typeSymbol.fullName.startsWith("flow.") =>
          tpt.tpe.typeSymbol.name -> args.collect { case Literal(StringConstant(s)) => s }
      }

    def isExtern(sym: Symbol): Boolean =
      sym.annotations.exists(_.tpe.typeSymbol.fullName == "stainless.annotation.extern")

    /** The definition a reference leads to: a field or constructor leads to its class. */
    def defining(sym: Symbol): Symbol =
      if sym.isClassConstructor || (sym.isValDef && sym.owner.isClassDef && !sym.owner.flags.is(Flags.Module))
      then sym.owner
      else sym

    def refs(tree: Tree): Set[Symbol] =
      val found = mutable.Set.empty[Symbol]
      object traverser extends TreeTraverser:
        override def traverseTree(t: Tree)(owner: Symbol): Unit =
          t match
            case id: Ident if id.symbol.exists => found += defining(id.symbol)
            case s: Select if s.symbol.exists  => found += defining(s.symbol)
            case n: New                        => found += n.tpe.typeSymbol
            case _                             =>
          super.traverseTree(t)(owner)
      traverser.traverseTree(tree)(defn.RootClass)
      found.toSet.filter(defs.contains)

    /** Every definition `roots` refers to, transitively. */
    def closure(roots: List[Symbol]): List[Symbol] =
      val seen = mutable.LinkedHashSet.empty[Symbol]
      def visit(sym: Symbol): Unit =
        // Synthetic members (case class accessors, lambdas) are covered by the trees that contain them.
        val synthetic = sym.flags.is(Flags.Synthetic) || sym.name.contains("$anonfun")
        if defs.contains(sym) && !synthetic && seen.add(sym) then refs(defs(sym)).foreach(visit)
      roots.foreach(visit)
      seen.toList.sortBy(_.fullName)

    def sha256(s: String): String =
      MessageDigest.getInstance("SHA-256").digest(s.getBytes("UTF-8")).map("%02x".format(_)).mkString

    /** A definition's source, dedented: its first line starts mid-line, at the definition's column. */
    def source(t: Tree): String =
      t.pos.sourceCode match
        case None => t.show
        case Some(code) =>
          val lines  = (" " * t.pos.startColumn + code).linesIterator.toList
          val margin = lines.filter(_.trim.nonEmpty).map(_.takeWhile(_ == ' ').length).minOption.getOrElse(0)
          lines.map(_.drop(margin)).mkString("\n")

    def statement(name: String, kind: Kind, text: String, on: List[Symbol]): FlowStatement =
      val all = closure(on)
      // The tree structure carries no positions, so reformatting leaves the hash alone.
      val structure = all.map(s => s.fullName + "\n" + defs(s).show(using Printer.TreeStructure)).mkString("\n")
      FlowStatement(
        name = name,
        kind = kind,
        text = text,
        on = on.map(_.fullName),
        hash = sha256(s"${kind.label}\n$text\n$structure"),
        sources = all.map(s => s.fullName -> source(defs(s))).toMap
      )

    // ── Statements ────────────────────────────────────────────────────────────────────────────────────────────────
    val annotated = defs.keys.toList.flatMap(sym => flowAnnotations(sym).map(sym -> _))

    val claims = annotated.collect { case (sym, ("claim", List(text))) =>
      statement(sym.name, Kind.Claim, text, List(sym))
    }
    def grouped(kind: Kind) =
      annotated
        .collect { case (sym, (k, List(name, text))) if k == kind.label => (name, text, sym) }
        .groupBy(_._1)
        .toList
        .sortBy((name, _) => annotated.indexWhere { case (_, (_, args)) => args.headOption.contains(name) })
        .map((name, group) => statement(name, kind, group.head._2, group.map(_._3)))

    val statements = claims ++ grouped(Kind.Assumption) ++ grouped(Kind.Design)
    val claimOf = annotated.collect { case (sym, ("claim", _)) => sym -> sym.name }.toMap
    val assumptionsOn = annotated
      .collect { case (sym, ("assumption", name :: _)) => sym -> name }
      .groupMap(_._1)(_._2)

    // ── Proofs ────────────────────────────────────────────────────────────────────────────────────────────────────
    def unwrap(t: Term): Term = t match
      case Inlined(_, Nil, e) => unwrap(e)
      case Block(Nil, e)      => unwrap(e)
      case Typed(e, _)        => unwrap(e)
      case _                  => t

    /** `{ body }.ensuring(post)`, through Stainless's implicit `Ensuring` wrapper. */
    def contract(rhs: Term): Option[(Term, Term)] = unwrap(rhs) match
      case Apply(sel @ Select(wrapped, "ensuring"), List(post)) => Some(unwrapEnsuring(wrapped) -> post)
      case Apply(TypeApply(Select(wrapped, "ensuring"), _), List(post)) => Some(unwrapEnsuring(wrapped) -> post)
      case _ => None

    def unwrapEnsuring(t: Term): Term = unwrap(t) match
      case Apply(_, List(body)) => body
      case other                => other

    def requires(body: Term): List[Term] =
      val found = mutable.ListBuffer.empty[Term]
      object traverser extends TreeTraverser:
        override def traverseTree(t: Tree)(owner: Symbol): Unit =
          t match
            case Apply(fun, List(arg)) if fun.symbol.name == "require" => found += arg
            case _                                                       => super.traverseTree(t)(owner)
      traverser.traverseTree(body)(defn.RootClass)
      found.toList

    def claimsIn(terms: List[Tree]): Set[String] = terms.flatMap(refs).flatMap(claimOf.get).toSet

    def assumptionsUsed(d: DefDef, used: Set[Symbol]): Set[String] =
      val paramTypes = d.termParamss.flatMap(_.params).map(_.tpt.tpe.typeSymbol)
      (used ++ paramTypes + d.symbol).flatMap(s => assumptionsOn.getOrElse(s, Nil))

    val withContracts = defs.toList.collect {
      case (sym, d: DefDef) if d.rhs.exists(rhs => contract(rhs).isDefined) =>
        val (body, post) = contract(d.rhs.get).get
        (sym, d, body, post)
    }
    val contracted = withContracts.map(_._1).toSet

    val proofs = withContracts.map { (sym, d, body, post) =>
      val pre  = requires(body)
      val used = refs(body) ++ refs(post)
      Proof(
        name = sym.fullName,
        file = d.pos.sourceFile.path,
        line = d.pos.startLine + 1,
        tested = isExtern(sym),
        proves = claimsIn(List(post)),
        requires = claimsIn(pre),
        calls = (refs(body) - sym).filter(contracted).map(_.fullName),
        assumes = assumptionsUsed(d, used)
      )
    }

    Model(statements, proofs)
