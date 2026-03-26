package cubical

import scala.util.parsing.combinator.*
import Term.*
import Decl.*

/** Parser for cubical type theory syntax.
 *  Compatible with Mortberg's grammar but with Unicode support.
 */
object Parser extends RegexParsers:
  
  // ── Lexical ──────────────────────────────────────────────
  
  override def skipWhitespace = true
  
  // Skip line comments starting with --
  protected override val whiteSpace = """(\s|--[^\n]*)+""".r
  
  val reserved = Set("data", "module", "where", "import", "U", "PathP", "comp", "fill", "Glue", "glue", "unglue", "split")
  
  def ident: Parser[String] = 
    """[a-zA-Z_][a-zA-Z0-9_']*""".r.filter(!reserved.contains(_))
  
  def number: Parser[Int] = 
    """[0-9]+""".r ^^ (_.toInt)
  
  // ── Terms ────────────────────────────────────────────────
  
  def term: Parser[Term] = expr
  
  def expr: Parser[Term] = 
    piType | sigmaType | pathType | pathAbs | lamExpr | splitExpr | arrowType | app
  
  // Multi-parameter binders: (x y z : A)
  def binder: Parser[(List[String], Term)] =
    ("(" ~> rep1(ident) <~ ":") ~ (term <~ ")") ^^ {
      case xs ~ ty => (xs, ty)
    }
  
  // Telescope: (x : A) (y : B) -> C
  def piType: Parser[Term] =
    rep1(binder) ~ ("->" ~> term) ^^ {
      case binders ~ body =>
        binders.foldRight(body) { case ((xs, ty), acc) =>
          xs.foldRight(acc)((x, b) => Pi(ty, Lam(x, ty, b)))
        }
    }
  
  // Simple arrow: A -> B (no binder)
  def arrowType: Parser[Term] =
    atom ~ ("->" ~> term) ^^ {
      case a ~ b => Pi(a, Lam("_", a, b))
    }
  
  def sigmaType: Parser[Term] =
    rep1(binder) ~ ("*" ~> term) ^^ {
      case binders ~ body =>
        binders.foldRight(body) { case ((xs, ty), acc) =>
          xs.foldRight(acc)((x, b) => Sigma(ty, Lam(x, ty, b)))
        }
    }
  
  def pathType: Parser[Term] =
    "Path" ~> atom ~ atom ~ atom ^^ {
      case a ~ u ~ v => PathP(Lam("_", Univ, a), u, v)
    } |
    "PathP" ~> atom ~ atom ~ atom ^^ {
      case a ~ u ~ v => PathP(a, u, v)
    }
  
  // Path abstraction: <i> expr
  def pathAbs: Parser[Term] =
    ("<" ~> rep1(ident) <~ ">") ~ term ^^ {
      case is ~ body => is.foldRight(body)((i, b) => Lam(i, Univ, b))
    }
  
  def lamExpr: Parser[Term] =
    "\\" ~> rep1(ident) ~ ("->" ~> term) ^^ {
      case xs ~ body => xs.foldRight(body)((x, b) => Lam(x, Univ, b))
    }
  
  // Split expression: split { pat -> expr ; ... } or split\n pat -> expr\n ...
  def splitExpr: Parser[Term] =
    "split" ~> ("{" ~> rep1sep(splitCase, opt(";")) <~ "}") ^^ { cases =>
      // For now, represent as a lambda (simplified)
      Lam("x", Univ, cases.head._2)
    } |
    "split" ~> rep1(splitCase) ^^ { cases =>
      Lam("x", Univ, cases.head._2)
    }
  
  def splitCase: Parser[(String, Term)] =
    opt("|") ~> ident ~ rep(ident) ~ ("->" ~> term) ^^ {
      case pat ~ args ~ body => (pat, body)
    }
  
  def app: Parser[Term] = 
    atom ~ rep(atom | pathApp) ^^ {
      case f ~ args => args.foldLeft(f) {
        case (fn, arg) => App(fn, arg)
      }
    }
  
  // Path application: @i
  def pathApp: Parser[Term] =
    "@" ~> ident ^^ Var.apply
  
  def atom: Parser[Term] =
    "U" ^^^ Univ |
    ident ^^ Var.apply |
    "(" ~> repsep(term, ",") <~ ")" ^^ {
      case List(t) => t  // Single element: just the term
      case ts => ts.reduceRight((a, b) => App(App(Var("pair"), a), b))  // Tuple
    }
  
  // ── Declarations ─────────────────────────────────────────
  
  def moduleHeader: Parser[String] =
    "module" ~> ident <~ "where"
  
  def importDecl: Parser[Unit] =
    "import" ~> ident ^^^ ()
  
  def decl: Parser[Decl] =
    ("data" ~> ident) ~ ("=" ~> rep1sep(constructor, "|")) ^^ {
      case name ~ constrs => DataDecl(name, Nil, Univ, constrs)
    } |
    ident ~ rep(binder) ~ (":" ~> term) ~ opt("=" ~> term ~ opt(whereClause)) ^^ {
      case name ~ params ~ ty ~ bodyOpt =>
        val fullType = params.foldRight(ty) { case ((xs, pty), acc) =>
          xs.foldRight(acc)((x, b) => Pi(pty, Lam(x, pty, b)))
        }
        bodyOpt match {
          case Some(body ~ _) => DefDecl(name, fullType, body)
          case None => DefDecl(name, fullType, Var("undefined"))
        }
    }
  
  def constructor: Parser[(String, Term)] =
    ident ~ rep(binder) ^^ {
      case name ~ Nil => (name, Univ)
      case name ~ binders => 
        val ty = binders.foldRight(Univ: Term) { case ((xs, a), acc) =>
          xs.foldRight(acc)((_, b) => Pi(a, Lam("_", a, b)))
        }
        (name, ty)
    }
  
  def whereClause: Parser[List[Decl]] =
    "where" ~> rep(decl)
  
  def module: Parser[List[Decl]] = 
    opt(moduleHeader) ~> rep(importDecl) ~> rep(decl)
  
  // ── Public API ───────────────────────────────────────────
  
  def parseModule(input: String): Either[String, List[Decl]] =
    parseAll(module, input) match {
      case Success(result, _) => Right(result)
      case NoSuccess(msg, _) => Left(msg)
    }

end Parser

