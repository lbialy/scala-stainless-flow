package flow

import scala.annotation.StaticAnnotation
import stainless.annotation.ignore

/** A claim: a property of the system, in the words of its domain. It goes on the `@ghost` predicate that states it,
  * and the claim takes the predicate's name. Stainless proves it, or ScalaCheck tests it when only tested code
  * promises it.
  */
@ignore
final class claim(text: String) extends StaticAnnotation

/** An assumption: what is trusted, such as an outside system or what comes from outside. It goes on the code it is
  * about (a contract, an invariant, a lock); several places can carry one assumption by sharing its `name`.
  */
@ignore
final class assumption(name: String, text: String) extends StaticAnnotation

/** A design decision with no formal content. Any change to the code it is on brings it back for review. */
@ignore
final class design(name: String, text: String) extends StaticAnnotation
