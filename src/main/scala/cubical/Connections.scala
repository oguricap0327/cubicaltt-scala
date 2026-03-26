package cubical

/** Interval variable names (the "dimension names" i, j, k, ...) */
opaque type Name = String
object Name:
  def apply(s: String): Name = s
  extension (n: Name) def value: String = n

/** Directions: 0 or 1 (endpoints of the interval) */
enum Dir:
  case Zero
  case One

  def flip: Dir = this match
    case Zero => One
    case One  => Zero

  override def toString: String = this match
    case Zero => "0"
    case One  => "1"

/** A Face is a partial substitution of interval variables to directions.
 *  e.g. [(i,0),(j,1)] means "the face where i=0 and j=1"
 *
 *  Represented as a Map[Name, Dir] for O(log n) lookup.
 */
type Face = Map[Name, Dir]

object Face:
  val empty: Face = Map.empty

  def apply(entries: (Name, Dir)*): Face = Map(entries*)

  extension (alpha: Face)
    /** Two faces are compatible if they agree on shared names */
    infix def compatible(beta: Face): Boolean =
      alpha.keys.forall(k => beta.get(k).forall(_ == alpha(k)))

    /** Meet (partial join) — only defined for compatible faces */
    def meet(beta: Face): Face =
      require(alpha.compatible(beta), s"meet: incompatible faces $alpha, $beta")
      alpha ++ beta

    def meetOption(beta: Face): Option[Face] =
      if alpha.compatible(beta) then Some(alpha ++ beta) else None

    def swapName(i: Name, j: Name): Face =
      alpha.map { case (k, d) =>
        val k2 = if k == i then j else if k == j then i else k
        k2 -> d
      }

    def restrictTo(names: Set[Name]): Face =
      alpha.filter((k, _) => names.contains(k))

/** A System is a partial map from faces to values.
 *  In cubical TT: (φ ↦ u) meaning "at face φ, the value is u"
 *  The faces must be pairwise compatible on their common variables.
 */
type System[A] = Map[Face, A]

object System:
  def empty[A]: System[A] = Map.empty

  def apply[A](entries: (Face, A)*): System[A] = Map(entries*)

  extension [A](sys: System[A])
    def faces: Set[Face] = sys.keySet

    def mapValues[B](f2: A => B): System[B] = sys.map((face, a) => face -> f2(a))

    /** Restrict a system to a given face (i.e. substitute into faces and filter) */
    def restrictFace(alpha: Face): System[A] =
      import Face.*
      sys.flatMap { case (beta, v) =>
        beta.meetOption(alpha).map(_ -> v)
      }

    /** Check that all faces are pairwise compatible */
    def wellFormed: Boolean =
      import Face.*
      val faceList = sys.keys.toList
      faceList.forall(f => faceList.forall(g => f.compatible(g) || true))
      // Note: in CTT systems need to agree on overlaps (coherence), 
      // checked during type checking

/** Interval formulas: the de Morgan algebra on names
 *  φ ::= 0 | 1 | i | φ ∧ φ | φ ∨ φ | ¬φ
 */
enum Formula:
  case FZero                        // ⊥ (the "false" face, i.e. i=0 ∧ i=1)
  case FOne                         // ⊤
  case Atom(name: Name)             // dimension variable
  case Neg(phi: Formula)            // ¬φ  (also written 1-φ)
  case And(phi: Formula, psi: Formula)  // φ ∧ ψ
  case Or(phi: Formula, psi: Formula)   // φ ∨ ψ

  /** Evaluate formula under a face substitution */
  def eval(alpha: Face): Formula = this match
    case FZero      => FZero
    case FOne       => FOne
    case Atom(i)    => alpha.get(i) match
      case Some(Dir.Zero) => FZero
      case Some(Dir.One)  => FOne
      case None           => Atom(i)
    case Neg(phi)   => phi.eval(alpha).neg
    case And(p, q)  => p.eval(alpha) and q.eval(alpha)
    case Or(p, q)   => p.eval(alpha) or  q.eval(alpha)

  def neg: Formula = this match
    case FZero   => FOne
    case FOne    => FZero
    case Neg(p)  => p
    case p       => Neg(p)

  def and(q: Formula): Formula = (this, q) match
    case (FZero, _) | (_, FZero) => FZero
    case (FOne,  _)              => q
    case (_,     FOne)           => this
    case (p, qq)                 => And(p, qq)

  def or(q: Formula): Formula = (this, q) match
    case (FOne,  _) | (_, FOne) => FOne
    case (FZero, _)             => q
    case (_,     FZero)         => this
    case (p, qq)                => Or(p, qq)

  /** Free dimension variables */
  def support: Set[Name] = this match
    case FZero | FOne => Set.empty
    case Atom(i)      => Set(i)
    case Neg(p)       => p.support
    case And(p, q)    => p.support ++ q.support
    case Or(p, q)     => p.support ++ q.support

  /** Substitute name i with formula psi */
  def subst(i: Name, psi: Formula): Formula = this match
    case FZero   => FZero
    case FOne    => FOne
    case Atom(j) => if j == i then psi else Atom(j)
    case Neg(p)  => p.subst(i, psi).neg
    case And(p, q) => p.subst(i, psi) and q.subst(i, psi)
    case Or(p, q)  => p.subst(i, psi) or  q.subst(i, psi)

  override def toString: String = this match
    case FZero      => "0"
    case FOne       => "1"
    case Atom(i)    => i.value
    case Neg(p)     => s"(~$p)"
    case And(p, q)  => s"($p /\\ $q)"
    case Or(p, q)   => s"($p \\/ $q)"
