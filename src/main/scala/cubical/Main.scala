package cubical

import Value.*
import Term.*
import Formula.*

/** A small REPL / runner for cubicaltt-scala.
 *  For now: runs a few built-in demo terms to verify the evaluator works.
 *  Eventually we'll hook up a parser here.
 */
object Main:
  def main(args: Array[String]): Unit =
    println("cubicaltt-scala — Cubical Type Theory in Scala 3 🐎✨")
    println("="*55)
    runDemo()

  def runDemo(): Unit =
    val ctx = TCtx.empty

    // Demo 1: id function
    println("\n[1] Identity function")
    val idTerm = Lam("A", Univ, Lam("x", Var("A"), Var("x")))
    val idTy   = Pi(Univ, Pi(Var("A"), Var("A")))   // simplified (A free)
    val idVal  = Eval.eval(idTerm, Env.empty)
    println(s"  term:  id = λA x. x")
    println(s"  value: $idVal")

    // Demo 2: apply id
    println("\n[2] Apply id to itself (at type U → U)")
    val applyId = App(App(App(idTerm, Pi(Univ, Univ)), idTerm), idTerm)
    val result  = Eval.eval(applyId, Env.empty)
    println(s"  result: $result")

    // Demo 3: formula algebra
    println("\n[3] Interval formula: (i ∧ j) ∨ (¬i ∧ k)")
    val i = Name("i"); val j = Name("j"); val k = Name("k")
    val phi = Formula.Or(
      Formula.And(Atom(i), Atom(j)),
      Formula.And(Neg(Atom(i)), Atom(k))
    )
    println(s"  φ = $phi")
    println(s"  φ[i↦1] = ${phi.subst(i, FOne)}")
    println(s"  φ[i↦0] = ${phi.subst(i, FZero)}")
    println(s"  φ[i↦0][k↦1] = ${phi.subst(i, FZero).subst(k, FOne)}")

    // Demo 4: PathP type (reflexivity path)
    println("\n[4] Reflexivity path: <_> x : Path A x x")
    val a = Name("a")
    val refl = PLam(a, Var("x"))
    val reflInEnv = Env.empty.updated("x", mkVar("x", VUniv))
    val reflVal = Eval.eval(refl, reflInEnv)
    println(s"  term:  <_> x")
    println(s"  value: $reflVal")

    // Demo 5: System / face
    println("\n[5] A partial element (system)")
    val sys: System[Formula] = System(
      Face(i -> Dir.Zero) -> Atom(j),
      Face(i -> Dir.One)  -> Neg(Atom(j))
    )
    println(s"  system: $sys")
    sys.foreach { case (face, v) => println(s"    face $face ↦ $v") }

    // Demo 6: Type checker on simple terms
    println("\n[6] Type check: (λ(x:U). x) : U → U")
    val lam = Lam("x", Univ, Var("x"))
    // Build: VPi(VUniv, body) where body when applied to v gives VUniv
    val piTy = VPi(VUniv, VLam("_", VUniv, Closure(Univ, Env.empty)))
    TypeChecker.check(ctx, lam, piTy) match
      case Right(())  => println("  ✓ Well-typed!")
      case Left(err)  => println(s"  ✗ Type error: $err")

    println("\nAll demos completed. Parser + full type checker coming next! 🐎✨")

  private def mkVar(x: Ident, ty: Value): Value = Neutral(Head.HVar(x, ty), Nil)
