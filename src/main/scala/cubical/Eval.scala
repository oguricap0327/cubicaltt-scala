package cubical

import Value.*
import Term.*
import Formula.*

/** The evaluator: Term × Env → Value */
object Eval:

  def eval(t: Term, rho: Env): Value = t match
    case Var(x) =>
      rho.lookupTerm(x).getOrElse(throw EvalError(s"Unbound variable: $x"))
    case Univ => VUniv
    case Pi(a, b)         => VPi(eval(a, rho), eval(b, rho))
    case Lam(x, ty, body) =>
      val tyV = eval(ty, rho)
      VLam(x, tyV, Closure(body, rho))
    case App(f, a)        => app(eval(f, rho), eval(a, rho))
    case Sigma(a, b)      => VSigma(eval(a, rho), eval(b, rho))
    case Pair(u, v)       => VPair(eval(u, rho), eval(v, rho))
    case Fst(p)           => fstVal(eval(p, rho))
    case Snd(p)           => sndVal(eval(p, rho))
    case Con(c, args)     => VCon(c, args.map(eval(_, rho)))
    case PCon(c, ty, args, phis) =>
      VPCon(c, eval(ty, rho), args.map(eval(_, rho)), phis.map(evalFormula(_, rho)))
    case Split(x, loc, ty, brs) =>
      Neutral(Head.HSplit(x, loc, eval(ty, rho), brs), Nil)
    case Sum(_, n, _)  => rho.lookupTerm(n).getOrElse(throw EvalError(s"Unknown type name: $n"))
    case HSum(_, n, _) => rho.lookupTerm(n).getOrElse(throw EvalError(s"Unknown type name: $n"))
    case PathP(a, u, v) => VPathP(eval(a, rho), eval(u, rho), eval(v, rho))
    case PLam(i, body) =>
      val j = freshName(i, rho.dimSupport)
      VPLam(j, eval(body, rho.subst(i, Atom(j))))
    case AppFormula(p, phi) => appFormula(eval(p, rho), evalFormula(phi, rho))
    case Comp(a, u, sys)  => comp(eval(a, rho), eval(u, rho), evalSystem(sys, rho))
    case Fill(a, u, sys)  => fill(eval(a, rho), eval(u, rho), evalSystem(sys, rho))
    case HComp(a, u, sys) => hcomp(eval(a, rho), eval(u, rho), evalSystem(sys, rho))
    case Glue(a, sys)     => glue(eval(a, rho), evalSystem(sys, rho))
    case GlueElem(a, sys) => glueElem(eval(a, rho), evalSystem(sys, rho))
    case UnGlueElem(a,sys)=> unglueElem(eval(a, rho), evalSystem(sys, rho))
    case Id(a, u, v)      => VId(eval(a,rho), eval(u,rho), eval(v,rho))
    case IdPair(u, sys)   => VIdPair(eval(u,rho), evalSystem(sys,rho))
    case IdJ(a,u,c,d,x,p) => idJ(eval(a,rho),eval(u,rho),eval(c,rho),eval(d,rho),eval(x,rho),eval(p,rho))
    case Where(body, decls) =>
      val rho2 = decls match
        case Decls.MutualDecls(loc, ds) => rho.withDecls(loc, ds)
        case Decls.OpaqueDecl(n)        => OpaqueEnv(Set(n), rho)
        case _                          => rho
      eval(body, rho2)
    case Undef(loc, ty)   => throw EvalError(s"Undefined at $loc")
    case Hole(loc)        => throw EvalError(s"Hole at $loc")

  // ── Formula eval ──────────────────────────────────────────

  def evalFormula(phi: Formula, rho: Env): Formula =
    phi.support.foldLeft(phi) { (p, i) =>
      rho.lookupDim(i).fold(p)(psi => p.subst(i, psi))
    }

  def evalSystem(sys: System[Term], rho: Env): System[Value] =
    sys.map { case (face, t) => face -> eval(t, rho.applyFace(face)) }

  // ── Application ───────────────────────────────────────────

  def app(f: Value, a: Value): Value = f match
    case VLam(x, _, Closure(body, env)) => eval(body, env.updated(x, a))
    case VLam(x, _, body: Value)        => app(body, a)
    case Neutral(h, sp)                 => Neutral(h, sp :+ Elim.EApp(a))
    case _                              => throw EvalError(s"app: not a function: $f")

  def fstVal(v: Value): Value = v match
    case VPair(u, _)    => u
    case Neutral(h, sp) => Neutral(h, sp :+ Elim.EFst)
    case _              => throw EvalError(s"fst: not a pair: $v")

  def sndVal(v: Value): Value = v match
    case VPair(_, w)    => w
    case Neutral(h, sp) => Neutral(h, sp :+ Elim.ESnd)
    case _              => throw EvalError(s"snd: not a pair: $v")

  // ── Path application ──────────────────────────────────────

  def appFormula(v: Value, phi: Formula): Value = v match
    case VPLam(i, body) => actVal(body, i, phi)
    case VPCon(c,a,args,phis) => VPCon(c, a, args, phis :+ phi)
    case Neutral(h, sp) => Neutral(h, sp :+ Elim.EAppFormula(phi))
    case _              => throw EvalError(s"appFormula: not a path: $v")

  // ── Nominal action: substitute dimension i ↦ phi ─────────

  def actVal(v: Value, i: Name, phi: Formula): Value =
    if !v.support.contains(i) then v else actV(v, i, phi)

  private def actV(v: Value, i: Name, phi: Formula): Value = v match
    case VUniv => VUniv
    case Neutral(h, sp) =>
      rebuildNeutral(actHead(h,i,phi), sp.map(actElim(_,i,phi)))
    case VPi(a, b)      => VPi(actVal(a,i,phi), actVal(b,i,phi))
    case VLam(x,ty,b)   => VLam(x, actVal(ty,i,phi), actVal(b,i,phi))
    case VSigma(a,b)    => VSigma(actVal(a,i,phi), actVal(b,i,phi))
    case VPair(u,w)     => VPair(actVal(u,i,phi), actVal(w,i,phi))
    case VCon(c,vs)     => VCon(c, vs.map(actVal(_,i,phi)))
    case VPCon(c,a,vs,phis) =>
      VPCon(c, actVal(a,i,phi), vs.map(actVal(_,i,phi)), phis.map(_.subst(i,phi)))
    case VPathP(a,u,w)  => VPathP(actVal(a,i,phi), actVal(u,i,phi), actVal(w,i,phi))
    case VPLam(j, body) =>
      if j == i then v
      else if phi.support.contains(j) then
        val k = freshName(j, phi.support ++ body.support)
        VPLam(k, actVal(actVal(body, j, Atom(k)), i, phi))
      else VPLam(j, actVal(body, i, phi))
    case VComp(a,u,sys)  => comp(actVal(a,i,phi), actVal(u,i,phi), actSys(sys,i,phi))
    case VHComp(a,u,sys) => hcomp(actVal(a,i,phi), actVal(u,i,phi), actSys(sys,i,phi))
    case VGlue(a,sys)    => glue(actVal(a,i,phi), actSys(sys,i,phi))
    case VGlueElem(a,sys)=> glueElem(actVal(a,i,phi), actSys(sys,i,phi))
    case VUnGlueElem(a,sys) => unglueElem(actVal(a,i,phi), actSys(sys,i,phi))
    case VCompU(a,sys)   => VCompU(actVal(a,i,phi), actSys(sys,i,phi))
    case VUnGlueElemU(a,b,es) =>
      VUnGlueElemU(actVal(a,i,phi), actVal(b,i,phi), actSys(es,i,phi))
    case VId(a,u,w)      => VId(actVal(a,i,phi), actVal(u,i,phi), actVal(w,i,phi))
    case VIdPair(u,sys)  => VIdPair(actVal(u,i,phi), actSys(sys,i,phi))
    case Closure(t,env)  => Closure(t, env.subst(i, phi))

  private def actHead(h: Head, i: Name, phi: Formula): Head = h match
    case Head.HVar(x,ty)          => Head.HVar(x, actVal(ty,i,phi))
    case Head.HOpaque(x,ty)       => Head.HOpaque(x, actVal(ty,i,phi))
    case Head.HSplit(x,loc,ty,brs)=> Head.HSplit(x, loc, actVal(ty,i,phi), brs)

  private def actElim(e: Elim, i: Name, phi: Formula): Elim = e match
    case Elim.EApp(v)          => Elim.EApp(actVal(v,i,phi))
    case Elim.EFst | Elim.ESnd => e
    case Elim.EAppFormula(psi) => Elim.EAppFormula(psi.subst(i, phi))

  private def actSys(sys: System[Value], i: Name, phi: Formula): System[Value] =
    sys.flatMap { case (face, v) =>
      val face2 = face.view.filterKeys(_ != i).toMap
      Some(face2 -> actVal(v, i, phi))
    }

  private def rebuildNeutral(h: Head, sp: Spine): Value =
    sp.foldLeft(Neutral(h, Nil): Value) {
      case (acc, Elim.EApp(a))          => app(acc, a)
      case (acc, Elim.EFst)             => fstVal(acc)
      case (acc, Elim.ESnd)             => sndVal(acc)
      case (acc, Elim.EAppFormula(psi)) => appFormula(acc, psi)
    }

  // ── Kan operations ────────────────────────────────────────

  /** comp (stub — most cases stay as VComp, proper cases reduce) */
  def comp(ty: Value, base: Value, sys: System[Value]): Value =
    if sys.isEmpty then base
    else ty match
      case _ => VComp(ty, base, sys)   // full comp is deferred to phase 2

  /** fill i.A u [sys] — the filler at dimension i */
  def fill(ty: Value, base: Value, sys: System[Value]): Value =
    val i = freshName(Name("i"), ty.support ++ base.support)
    VPLam(i, comp(actVal(ty, i, Atom(i)), base, sys))

  /** hcomp (homogeneous composition — type doesn't vary) */
  def hcomp(ty: Value, base: Value, sys: System[Value]): Value =
    if sys.isEmpty then base
    else VHComp(ty, base, sys)

  /** Glue type introduction */
  def glue(base: Value, sys: System[Value]): Value =
    if sys.isEmpty then base else VGlue(base, sys)

  def glueElem(base: Value, sys: System[Value]): Value =
    if sys.isEmpty then base else VGlueElem(base, sys)

  def unglueElem(base: Value, sys: System[Value]): Value =
    sys.headOption match
      case Some((_, v)) => fstVal(v)  // use first available fiber
      case None         => base

  /** Identity type eliminator */
  def idJ(ty: Value, left: Value, mot: Value, refl: Value, right: Value, path: Value): Value =
    path match
      case VIdPair(w, _) => app(app(mot, w), refl)
      case Neutral(h, sp) => Neutral(h, sp)
      case _ => throw EvalError(s"idJ: not an id pair: $path")

  // ── Helpers ───────────────────────────────────────────────

  def mkVar(x: Ident, ty: Value): Value = Neutral(Head.HVar(x, ty), Nil)
  def mkDimVar(i: Name): Value = Neutral(Head.HVar(i.value, VUniv), Nil)

  private var nameCounter = 0
  def freshName(base: Name, avoid: Set[Name]): Name =
    var candidate = base
    while avoid.contains(candidate) do
      nameCounter += 1
      candidate = Name(s"${base.value}$$${nameCounter}")
    candidate


/** Error type for evaluation failures */
case class EvalError(msg: String) extends Exception(msg)
