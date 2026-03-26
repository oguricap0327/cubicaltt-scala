package cubical

import Value.*
import Term.*
import Formula.*
import Eval.*

/** Type-checking context.
 *
 *  The typechecking monad is modelled as a pure Either-based result
 *  (no IO needed until we add printing/holes).
 *  Context is threaded explicitly.
 */
case class TCtx(
  env:     Env,           // evaluation environment
  types:   Map[Ident, Value],  // typing context Γ
  names:   List[Ident],   // freshness list for name generation
  verbose: Boolean = false
):
  def withVar(x: Ident, ty: Value): TCtx =
    val v = mkVar(x, ty)
    copy(
      env   = env.updated(x, v),
      types = types.updated(x, ty),
      names = x :: names
    )

  def withDim(i: Name): TCtx =
    copy(env = env.subst(i, Atom(i)))

  def withDecls(loc: Loc, ds: List[(Ident, (Term, Term))]): TCtx =
    copy(env = env.withDecls(loc, ds))

  def applyFace(alpha: Face): TCtx =
    copy(env = env.applyFace(alpha))

object TCtx:
  val empty: TCtx = TCtx(Env.empty, Map.empty, Nil)

// ── Type-checker result ────────────────────────────────────

type TCResult[A] = Either[TCError, A]

case class TCError(msg: String, loc: Option[Loc] = None):
  override def toString: String = loc.fold(msg)(l => s"$l: $msg")

object TypeChecker:

  def check(ctx: TCtx, t: Term, ty: Value): TCResult[Unit] =
    ty match
      // ── Univ check: any term that infers a universe ────────
      case VUniv => infer(ctx, t).map(_ => ())

      // ── Pi: check a lambda against Pi type ────────────────
      case VPi(a, b) => t match
        case Lam(x, ann, body) =>
          for
            _ <- checkTy(ctx, ann)
            annV = eval(ann, ctx.env)
            _ <- conv(ctx, annV, a).left.map(e => TCError(s"Lambda annotation mismatch: ${e.msg}"))
            ctx2 = ctx.withVar(x, a)
            bV   = appClosure(b, mkVar(x, a))
            _ <- check(ctx2, body, bV)
          yield ()
        case _ =>
          // eta-expand check
          val x = freshIdent("x", ctx.names)
          val ctx2 = ctx.withVar(x, a)
          val bV = appClosure(b, mkVar(x, a))
          check(ctx2, App(t, Var(x)), bV)

      // ── Sigma: check a pair ────────────────────────────────
      case VSigma(a, b) => t match
        case Pair(u, v) =>
          for
            _ <- check(ctx, u, a)
            uV = eval(u, ctx.env)
            bV = appClosure(b, uV)
            _ <- check(ctx, v, bV)
          yield ()
        case _ =>
          // let inference handle it
          for
            infTy <- infer(ctx, t)
            _ <- conv(ctx, infTy, ty)
          yield ()

      // ── PathP: check a PLam against PathP ─────────────────
      case VPathP(a, u, v) => t match
        case PLam(i, body) =>
          val ctx2 = ctx.withDim(i)
          val ai = appFormula(a, Atom(i))
          for
            _ <- check(ctx2, body, ai)
            // check endpoints
            bodyAtZero = eval(body, ctx.env.subst(i, FZero))
            bodyAtOne  = eval(body, ctx.env.subst(i, FOne))
            _ <- conv(ctx, bodyAtZero, u)
            _ <- conv(ctx, bodyAtOne,  v)
          yield ()
        case _ =>
          for
            infTy <- infer(ctx, t)
            _ <- conv(ctx, infTy, ty)
          yield ()

      // ── Data constructors ──────────────────────────────────
      case VCon(_, _) =>
        for
          infTy <- infer(ctx, t)
          _ <- conv(ctx, infTy, ty)
        yield ()

      // ── Default: infer and compare ─────────────────────────
      case _ =>
        for
          infTy <- infer(ctx, t)
          _ <- conv(ctx, infTy, ty)
        yield ()

  def checkTy(ctx: TCtx, t: Term): TCResult[Unit] =
    check(ctx, t, VUniv)

  def infer(ctx: TCtx, t: Term): TCResult[Value] = t match
    case Var(x) =>
      ctx.types.get(x).toRight(TCError(s"Unbound variable: $x"))

    case Univ => Right(VUniv)

    case Pi(a, b) =>
      for
        _ <- checkTy(ctx, a)
        aV = eval(a, ctx.env)
        x = freshIdent("x", ctx.names)
        ctx2 = ctx.withVar(x, aV)
        _ <- checkTy(ctx2, b)
      yield VUniv

    case Sigma(a, b) =>
      for
        _ <- checkTy(ctx, a)
        aV = eval(a, ctx.env)
        x = freshIdent("x", ctx.names)
        ctx2 = ctx.withVar(x, aV)
        _ <- checkTy(ctx2, b)
      yield VUniv

    case App(f, a) =>
      for
        fTy <- infer(ctx, f)
        res <- fTy match
          case VPi(dom, cod) =>
            check(ctx, a, dom).map { _ =>
              val aV = eval(a, ctx.env)
              appClosure(cod, aV)
            }
          case _ => Left(TCError(s"Expected Pi type, got: $fTy"))
      yield res

    case Fst(p) =>
      for
        pTy <- infer(ctx, p)
        res <- pTy match
          case VSigma(a, _) => Right(a)
          case _            => Left(TCError(s"Expected Sigma type for fst, got: $pTy"))
      yield res

    case Snd(p) =>
      for
        pTy <- infer(ctx, p)
        res <- pTy match
          case VSigma(_, b) =>
            val pV = eval(p, ctx.env)
            Right(appClosure(b, fstVal(pV)))
          case _ => Left(TCError(s"Expected Sigma type for snd, got: $pTy"))
      yield res

    case AppFormula(path, phi) =>
      for
        pathTy <- infer(ctx, path)
        res <- pathTy match
          case VPathP(a, _, _) =>
            val phiV = evalFormula(phi, ctx.env)
            Right(appFormula(a, phiV))
          case _ => Left(TCError(s"Expected PathP type for @, got: $pathTy"))
      yield res

    case PathP(a, u, v) =>
      // Check A : I → U, u : A 0, v : A 1
      val i = freshName(Name("i"), ctx.env.dimSupport)
      val ctx2 = ctx.withDim(i)
      for
        _ <- check(ctx2, a, VUniv)
        aV = eval(a, ctx.env)
        a0 = appFormula(aV, FZero)
        a1 = appFormula(aV, FOne)
        _ <- check(ctx, u, a0)
        _ <- check(ctx, v, a1)
      yield VUniv

    case Id(a, u, v) =>
      for
        _ <- checkTy(ctx, a)
        aV = eval(a, ctx.env)
        _ <- check(ctx, u, aV)
        _ <- check(ctx, v, aV)
      yield VUniv

    case Lam(x, ty, body) =>
      for
        _ <- checkTy(ctx, ty)
        tyV = eval(ty, ctx.env)
        ctx2 = ctx.withVar(x, tyV)
        bodyTy <- infer(ctx2, body)
      yield VPi(tyV, VLam(x, tyV, bodyTy))

    case Where(body, decls) =>
      val ctx2 = decls match
        case Decls.MutualDecls(loc, ds) =>
          // For mutual decls: check each decl then add all
          ctx.withDecls(loc, ds)
        case _ => ctx
      infer(ctx2, body)

    case _ =>
      Left(TCError(s"Cannot infer type of $t"))

  // ── Conversion checking ───────────────────────────────────

  def conv(ctx: TCtx, u: Value, v: Value): TCResult[Unit] =
    if convVal(ctx.names, u, v) then Right(())
    else Left(TCError(s"Type mismatch:\n  got:      $u\n  expected: $v"))

  def convVal(names: List[Ident], u: Value, v: Value): Boolean =
    (u, v) match
      case (VUniv, VUniv) => true
      case (VPi(a1,b1), VPi(a2,b2)) =>
        val x = freshIdent("x", names)
        val xv = mkVar(x, a1)
        convVal(names, a1, a2) && convVal(x :: names, appClosure(b1, xv), appClosure(b2, xv))
      case (VSigma(a1,b1), VSigma(a2,b2)) =>
        val x = freshIdent("x", names)
        val xv = mkVar(x, a1)
        convVal(names, a1, a2) && convVal(x :: names, appClosure(b1, xv), appClosure(b2, xv))
      case (VLam(x,ty,b1), VLam(_,_,b2)) =>
        val xv = mkVar(x, ty)
        convVal(x :: names, appClosure(b1, xv), appClosure(b2, xv))
      case (VLam(x,ty,b), f) =>
        val xv = mkVar(x, ty)
        convVal(x :: names, appClosure(b, xv), app(f, xv))
      case (f, VLam(x,ty,b)) =>
        val xv = mkVar(x, ty)
        convVal(x :: names, app(f, xv), appClosure(b, xv))
      case (VPathP(a1,u1,v1), VPathP(a2,u2,v2)) =>
        val i = freshName(Name("i"), Set.empty)
        convVal(names, appFormula(a1, Atom(i)), appFormula(a2, Atom(i))) &&
        convVal(names, u1, u2) && convVal(names, v1, v2)
      case (VPLam(i,b1), VPLam(j,b2)) =>
        convVal(names, b1, actVal(b2, j, Atom(i)))
      case (VPLam(i,b), p) =>
        convVal(names, b, appFormula(p, Atom(i)))
      case (p, VPLam(i,b)) =>
        convVal(names, appFormula(p, Atom(i)), b)
      case (VPair(u1,v1), VPair(u2,v2)) =>
        convVal(names, u1, u2) && convVal(names, v1, v2)
      case (VPair(u1,v1), p) =>
        convVal(names, u1, fstVal(p)) && convVal(names, v1, sndVal(p))
      case (p, VPair(u2,v2)) =>
        convVal(names, fstVal(p), u2) && convVal(names, sndVal(p), v2)
      case (VCon(c1,args1), VCon(c2,args2)) =>
        c1 == c2 && args1.zip(args2).forall((a,b) => convVal(names, a, b))
      case (Neutral(h1,sp1), Neutral(h2,sp2)) =>
        convHead(names, h1, h2) && convSpine(names, sp1, sp2)
      case (VId(a1,u1,v1), VId(a2,u2,v2)) =>
        convVal(names,a1,a2) && convVal(names,u1,u2) && convVal(names,v1,v2)
      case _ => false

  private def convHead(names: List[Ident], h1: Head, h2: Head): Boolean =
    (h1, h2) match
      case (Head.HVar(x1,_), Head.HVar(x2,_))           => x1 == x2
      case (Head.HOpaque(x1,_), Head.HOpaque(x2,_))     => x1 == x2
      case (Head.HSplit(x1,_,_,_), Head.HSplit(x2,_,_,_)) => x1 == x2
      case _ => false

  private def convSpine(names: List[Ident], sp1: Spine, sp2: Spine): Boolean =
    sp1.zip(sp2).forall {
      case (Elim.EApp(a), Elim.EApp(b))                   => convVal(names, a, b)
      case (Elim.EFst, Elim.EFst)                          => true
      case (Elim.ESnd, Elim.ESnd)                          => true
      case (Elim.EAppFormula(p), Elim.EAppFormula(q))      => p == q
      case _                                               => false
    } && sp1.length == sp2.length

  // ── Helpers ───────────────────────────────────────────────

  private def appClosure(v: Value, arg: Value): Value = v match
    case Closure(body, env)  => eval(body, env.updated("_", arg))  // use positional
    case VLam(x, _, Closure(body, env)) => eval(body, env.updated(x, arg))
    case VLam(x, _, b)                  => app(b, arg)
    case _                   => app(v, arg)

  private def freshIdent(base: Ident, avoid: List[Ident]): Ident =
    val avoidSet = avoid.toSet
    var candidate = base
    var n = 0
    while avoidSet.contains(candidate) do
      n += 1; candidate = s"$base$$$n"
    candidate
