package cubical

/** The semantic domain: values after evaluation.
 *
 *  Values are the "meaning" of terms — they represent terms in
 *  weak-head normal form. The key insight from cubical TT is that
 *  values carry a *nominal* structure: they can have free dimension
 *  variables (Names) and need to support substitution along those.
 *
 *  OOP design:
 *  - sealed trait Value with case class variants
 *  - The `Nominal` typeclass is replaced by a method `act` on Value
 *  - Environments are case classes with factory methods
 *  - The "big" eval/comp functions live in Eval.scala
 */
sealed trait Value:
  import Value.*

  /** Free dimension variables in this value */
  def support: Set[Name] = this match
    case VUniv                          => Set.empty
    case Neutral(hd, sp)                => hd.support ++ sp.support
    case VPi(a, b)                      => a.support ++ b.support
    case VLam(_, a, body)               => a.support ++ body.support
    case VSigma(a, b)                   => a.support ++ b.support
    case VPair(u, v)                    => u.support ++ v.support
    case VCon(_, vs)                    => vs.flatMap(_.support).toSet
    case VPCon(_, a, vs, phis)          => a.support ++ vs.flatMap(_.support) ++ phis.flatMap(_.support)
    case VPathP(a, u, v)                => a.support ++ u.support ++ v.support
    case VPLam(i, v)                    => v.support - i
    case VComp(a, u, sys)               => a.support ++ u.support ++ sysSupport(sys)
    case VHComp(a, u, sys)              => a.support ++ u.support ++ sysSupport(sys)
    case VGlue(a, sys)                  => a.support ++ sysSupport(sys)
    case VGlueElem(a, sys)              => a.support ++ sysSupport(sys)
    case VUnGlueElem(a, sys)            => a.support ++ sysSupport(sys)
    case VCompU(a, sys)                 => a.support ++ sysSupport(sys)
    case VUnGlueElemU(a, b, es)         => a.support ++ b.support ++ sysSupport(es)
    case VId(a, u, v)                   => a.support ++ u.support ++ v.support
    case VIdPair(u, sys)                => u.support ++ sysSupport(sys)
    case Closure(t, env)                => env.dimSupport

  private def sysSupport(sys: System[Value]): Set[Name] =
    sys.keys.flatMap(_.keySet).toSet ++ sys.values.flatMap(_.support)

object Value:
  // ── Universe ─────────────────────────────────────────────
  case object VUniv extends Value

  // ── Neutral values (stuck computations) ──────────────────
  /** A neutral is a variable (or split) applied to a spine of eliminations.
   *  We use a separate Head + Spine representation for clarity.
   */
  case class Neutral(head: Head, spine: Spine) extends Value

  // ── Dependent functions ───────────────────────────────────
  case class VPi(domain: Value, codomain: Value) extends Value
  /** A semantic lambda: we store the binder name + domain type for readability,
   *  plus a *closure* (body term + env) as the codomain.
   */
  case class VLam(x: Ident, domainTy: Value, body: Value) extends Value

  // ── Dependent pairs ───────────────────────────────────────
  case class VSigma(fstTy: Value, sndTy: Value) extends Value
  case class VPair(fst: Value, snd: Value) extends Value

  // ── Data constructors ────────────────────────────────────
  case class VCon(ctor: Ident, args: List[Value]) extends Value
  case class VPCon(ctor: Ident, dataType: Value, args: List[Value], phis: List[Formula]) extends Value

  // ── Path types ───────────────────────────────────────────
  case class VPathP(pathTy: Value, left: Value, right: Value) extends Value
  case class VPLam(dim: Name, body: Value) extends Value

  // ── Kan operations (stuck) ───────────────────────────────
  case class VComp(ty: Value, base: Value, sys: System[Value]) extends Value
  case class VHComp(ty: Value, base: Value, sys: System[Value]) extends Value

  // ── Glue types ───────────────────────────────────────────
  case class VGlue(base: Value, sys: System[Value]) extends Value
  case class VGlueElem(base: Value, sys: System[Value]) extends Value
  case class VUnGlueElem(base: Value, sys: System[Value]) extends Value
  case class VCompU(base: Value, sys: System[Value]) extends Value
  case class VUnGlueElemU(equiv: Value, base: Value, es: System[Value]) extends Value

  // ── Identity types ───────────────────────────────────────
  case class VId(ty: Value, left: Value, right: Value) extends Value
  case class VIdPair(witness: Value, sys: System[Value]) extends Value

  // ── Closures ─────────────────────────────────────────────
  /** A term-level closure (unevaluated body with its environment).
   *  Used to represent the codomain of Pi/Sigma as a function.
   */
  case class Closure(body: Term, env: Env) extends Value

/** The "head" of a neutral term */
enum Head:
  case HVar(name: Ident, ty: Value)
  case HOpaque(name: Ident, ty: Value)
  case HSplit(name: Ident, loc: Loc, ty: Value, branches: List[Branch])

  def support: Set[Name] = this match
    case HVar(_, ty)          => ty.support
    case HOpaque(_, ty)       => ty.support
    case HSplit(_, _, ty, _)  => ty.support

/** The "spine" of a neutral: a list of pending eliminations */
type Spine = List[Elim]
extension (sp: Spine)
  def support: Set[Name] = sp.flatMap(_.support).toSet

/** Eliminations */
enum Elim:
  case EApp(arg: Value)
  case EFst
  case ESnd
  case EAppFormula(phi: Formula)

  def support: Set[Name] = this match
    case EApp(v)          => v.support
    case EFst | ESnd      => Set.empty
    case EAppFormula(phi) => phi.support

// ============================================================
// Environments
// ============================================================

/** The evaluation environment.
 *
 *  In the Haskell original this is a recursive union type (Upd/Def/Sub/Empty).
 *  We represent it as an OOP class hierarchy for clarity.
 *
 *  An Env contains:
 *    - term variable bindings  (Ident → Value)
 *    - dimension substitutions (Name  → Formula)
 *    - opaque set               (Set[Ident])
 */
sealed abstract class Env:
  def lookupTerm(x: Ident): Option[Value]
  def lookupDim(i: Name): Option[Formula]
  def isOpaque(x: Ident): Boolean
  def dimSupport: Set[Name]

  /** Extend with a term binding */
  def updated(x: Ident, v: Value): Env = TermEnv(x, v, this)

  /** Extend with a dimension substitution */
  def subst(i: Name, phi: Formula): Env = DimEnv(i, phi, this)

  /** Add a definition group */
  def withDecls(loc: Loc, decls: List[(Ident, (Term, Term))]): Env =
    DeclEnv(loc, decls, this)

  /** Apply a face substitution to all dimension names in scope */
  def applyFace(alpha: Face): Env =
    alpha.foldLeft(this) { case (env, (i, d)) =>
      val phi = d match
        case Dir.Zero => Formula.FZero
        case Dir.One  => Formula.FOne
      env.subst(i, phi)
    }

object Env:
  val empty: Env = EmptyEnv

case object EmptyEnv extends Env:
  def lookupTerm(x: Ident): Option[Value]   = None
  def lookupDim(i: Name): Option[Formula]   = None
  def isOpaque(x: Ident): Boolean           = false
  def dimSupport: Set[Name]                 = Set.empty

case class TermEnv(x: Ident, v: Value, parent: Env) extends Env:
  def lookupTerm(y: Ident): Option[Value]   = if y == x then Some(v) else parent.lookupTerm(y)
  def lookupDim(i: Name): Option[Formula]   = parent.lookupDim(i)
  def isOpaque(y: Ident): Boolean           = parent.isOpaque(y)
  def dimSupport: Set[Name]                 = v.support ++ parent.dimSupport

case class DimEnv(i: Name, phi: Formula, parent: Env) extends Env:
  def lookupTerm(x: Ident): Option[Value]   = parent.lookupTerm(x)
  def lookupDim(j: Name): Option[Formula]   = if j == i then Some(phi) else parent.lookupDim(j)
  def isOpaque(x: Ident): Boolean           = parent.isOpaque(x)
  def dimSupport: Set[Name]                 = phi.support ++ parent.dimSupport

case class DeclEnv(loc: Loc, decls: List[(Ident, (Term, Term))], parent: Env) extends Env:
  // Lazy: definitions are evaluated on demand
  def lookupTerm(x: Ident): Option[Value] =
    decls.collectFirst { case (`x`, (_, body)) =>
      Eval.eval(body, this)
    }.orElse(parent.lookupTerm(x))
  def lookupDim(i: Name): Option[Formula]   = parent.lookupDim(i)
  def isOpaque(x: Ident): Boolean           = parent.isOpaque(x)
  def dimSupport: Set[Name]                 = parent.dimSupport

case class OpaqueEnv(names: Set[Ident], parent: Env) extends Env:
  def lookupTerm(x: Ident): Option[Value] =
    if names.contains(x) then None else parent.lookupTerm(x)
  def lookupDim(i: Name): Option[Formula]   = parent.lookupDim(i)
  def isOpaque(x: Ident): Boolean           = names.contains(x) || parent.isOpaque(x)
  def dimSupport: Set[Name]                 = parent.dimSupport
