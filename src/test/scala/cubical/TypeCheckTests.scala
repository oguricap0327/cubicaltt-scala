package cubical

import munit.FunSuite
import Term.*
import Value.*
import Eval.*

class TypeCheckTests extends FunSuite:
  
  test("infer type of universe") {
    val ctx = TCtx.empty
    val result = TypeChecker.infer(ctx, Univ)
    assert(result.isRight, s"Universe should infer: ${result.left.getOrElse("")}")
    assertEquals(result.getOrElse(null), VUniv)
  }
  
  test("check universe has type universe") {
    val ctx = TCtx.empty
    val result = TypeChecker.check(ctx, Univ, VUniv)
    assert(result.isRight, s"U : U should check: ${result.left.getOrElse("")}")
  }
  
  test("infer Pi type") {
    val ctx = TCtx.empty
    // (x : U) → U : U
    val piTerm = Pi(Univ, Univ)
    val result = TypeChecker.infer(ctx, piTerm)
    assert(result.isRight, s"Pi type should infer: ${result.left.getOrElse("")}")
    assertEquals(result.getOrElse(null), VUniv)
  }
  
  test("infer Sigma type") {
    val ctx = TCtx.empty
    // (x : U) × U : U
    val sigmaTerm = Sigma(Univ, Univ)
    val result = TypeChecker.infer(ctx, sigmaTerm)
    assert(result.isRight, s"Sigma type should infer: ${result.left.getOrElse("")}")
    assertEquals(result.getOrElse(null), VUniv)
  }

end TypeCheckTests
